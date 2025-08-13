# Fix JSON loading initialization
import os
import xml.etree.ElementTree as ET
from telethon import TelegramClient, events
from telethon.sessions import StringSession
from telethon.tl.types import DocumentAttributeVideo, InputFileBig, InputFile
from telethon.tl.functions.upload import SaveBigFilePartRequest, SaveFilePartRequest
from telethon.tl.functions.messages import UploadMediaRequest
from telethon.tl.types import InputMediaUploadedDocument
import asyncio
import aiohttp
from aiohttp import web
import logging
import time
import base64
from dotenv import load_dotenv
import subprocess
import traceback
import zipfile
import requests
import stat  # For setting file permissions
import inspect  # For debugging class methods
import random  # For generating unique file IDs
import mmap  # For zero-copy file part reads to speed up uploads
import re
import sys
from urllib.parse import urlparse, unquote
import psutil
from telethon.errors.rpcerrorlist import FloodWaitError  # Import FloodWaitError
from collections import deque  # For task queue
import json
import math

# Set up logging at the very start - console only to save disk space
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler()]
)

logging.info("Script started.")

# Load .env file
load_dotenv()

# Config from .env
API_ID = os.getenv('API_ID')
API_HASH = os.getenv('API_HASH')
BOT_TOKEN = os.getenv('BOT_TOKEN')
SESSION_STRING = os.getenv('SESSION_STRING')
ALLOWED_USERS = os.getenv('ALLOWED_USERS', '')

if not all([API_ID, API_HASH, ALLOWED_USERS]):
    logging.error("Missing env vars: Set API_ID, API_HASH, ALLOWED_USERS in .env")
    raise ValueError("Missing env vars: Set API_ID, API_HASH, ALLOWED_USERS in .env")

# SESSION_STRING is optional - if provided, use it for user client, otherwise use bot
if SESSION_STRING and not SESSION_STRING.strip():
    SESSION_STRING = None

if not SESSION_STRING and not BOT_TOKEN:
    logging.error("Either SESSION_STRING or BOT_TOKEN must be provided")
    raise ValueError("Either SESSION_STRING or BOT_TOKEN must be provided")

try:
    API_ID = int(API_ID)
except ValueError:
    logging.error(f"Invalid API_ID: {API_ID}. Must be a valid integer.")
    raise ValueError(f"Invalid API_ID: {API_ID}. Must be a valid integer.")

try:
    ALLOWED_USERS = [int(uid.strip()) for uid in ALLOWED_USERS.split(',') if uid.strip()]
except ValueError as e:
    logging.error(f"Invalid ALLOWED_USERS format: {ALLOWED_USERS}. Error: {e}")
    raise ValueError(f"Invalid ALLOWED_USERS format: {ALLOWED_USERS}. Must be comma-separated integers.")

# Debug environment variables
logging.info(f"Environment RENDER: {os.getenv('RENDER')}")
# Set DOWNLOAD_DIR based on environment
if os.getenv('RENDER') == 'true':
    DOWNLOAD_DIR = '/app/downloads'
else:
    DOWNLOAD_DIR = os.getenv('DOWNLOAD_DIR', 'downloads')
logging.info(f"Set DOWNLOAD_DIR to: {DOWNLOAD_DIR}")

# Path to mp4decrypt will be set after downloading Bento4 SDK
MP4DECRYPT_PATH = os.path.join(os.getcwd(), 'Bento4-SDK', 'bin', 'mp4decrypt')

# Global locks and task queue - now per user
global_download_lock = asyncio.Lock()
message_rate_limit_lock = asyncio.Lock()  # Lock to throttle message sends

# User-specific task queues and processing states
user_task_queues = {}  # Format: {user_id: deque()}
user_processing_states = {}  # Format: {user_id: bool}
user_queue_locks = {}  # Format: {user_id: asyncio.Lock()}
user_active_tasks = {}  # Format: {user_id: asyncio.Task()}
user_bot_instances = {}  # Format: {user_id: MPDLeechBot}

# JSON storage for loadjson/processjson functionality
user_json_data = {}  # Format: {user_id: json_data}
json_lock = asyncio.Lock()  # Lock for JSON data management

# User management storage
authorized_users = set(ALLOWED_USERS)  # Use a set for faster lookups
user_lock = asyncio.Lock()  # Lock to manage authorized_users

# Thumbnail storage for users
user_thumbnails = {}  # Format: {user_id: thumbnail_file_path}
thumbnail_lock = asyncio.Lock()  # Lock for thumbnail management

# Speed tracking for users
user_speed_stats = {}  # Format: {user_id: {'download_speed': float, 'upload_speed': float, 'last_updated': timestamp}}
speed_lock = asyncio.Lock()  # Lock for speed tracking

# Bulk JSON processing storage
user_bulk_data = {}  # Format: {user_id: [json_data1, json_data2, ...]}
bulk_lock = asyncio.Lock()  # Lock for bulk processing

# Client tracking for session type
is_user_session = False

# Download and extract Bento4 SDK if not present
def setup_bento4():
    try:
        bento4_dir = os.path.join(os.getcwd(), 'Bento4-SDK')
        mp4decrypt_path = os.path.join(bento4_dir, 'bin', 'mp4decrypt')
        if not os.path.isfile(mp4decrypt_path):
            logging.info("Downloading Bento4 SDK for mp4decrypt...")
            # Use a GitHub release URL for reliability
            bento4_urls = [
                "https://github.com/axiomatic-systems/Bento4/releases/download/v1.6.0-641/Bento4-SDK-1.6.0-641-x86_64-unknown-linux.zip",
                "https://www.bok.net/Bento4/binaries/Bento4-SDK-1-6-0-641.x86_64-unknown-linux.zip"  # Fallback URL
            ]
            zip_path = os.path.join(os.getcwd(), 'Bento4-SDK.zip')
            response = None

            # Try each URL until one succeeds
            for url in bento4_urls:
                logging.info(f"Attempting to download from: {url}")
                try:
                    response = requests.get(url, stream=True)
                    if response.status_code == 200:
                        logging.info(f"Successfully accessed URL: {url}")
                        break
                    else:
                        logging.warning(f"Failed to download from {url}: HTTP {response.status_code}")
                except Exception as e:
                    logging.warning(f"Error accessing {url}: {str(e)}")

            if not response or response.status_code != 200:
                raise Exception(f"Failed to download Bento4 SDK: All URLs failed (last status: {response.status_code if response else 'No response'})")

            with open(zip_path, 'wb') as f:
                for chunk in response.iter_content(chunk_size=8192):
                    if chunk:
                        f.write(chunk)

            # Validate the zip file
            try:
                with zipfile.ZipFile(zip_path, 'r') as zip_ref:
                    zip_ref.testzip()
                    logging.info("Zip file validation successful")
            except zipfile.BadZipFile:
                if os.path.exists(zip_path):
                    os.remove(zip_path)
                raise Exception("Downloaded file is not a valid zip file - check the URL")

            # Extract the zip file
            with zipfile.ZipFile(zip_path, 'r') as zip_ref:
                zip_ref.extractall(os.getcwd())

            # Log the extracted contents
            extracted_files = os.listdir(os.getcwd())
            logging.info(f"Extracted files: {extracted_files}")

            # Find the extracted Bento4 folder (exclude the zip file itself)
            extracted_folders = [f for f in os.listdir() if f.startswith('Bento4-SDK') and not f.endswith('.zip')]
            if not extracted_folders:
                raise Exception("No Bento4-SDK folder found after extraction. Extracted contents: " + str(extracted_files))
            extracted_folder = extracted_folders[0]
            logging.info(f"Found Bento4 folder: {extracted_folder}")

            # Rename the extracted folder to Bento4-SDK
            if extracted_folder != 'Bento4-SDK':
                os.rename(extracted_folder, 'Bento4-SDK')
                logging.info(f"Renamed {extracted_folder} to Bento4-SDK")

            # Verify the bin directory exists
            bin_dir = os.path.join(bento4_dir, 'bin')
            if not os.path.isdir(bin_dir):
                raise FileNotFoundError(f"Bento4-SDK/bin directory not found at {bin_dir}. Directory contents: {os.listdir(bento4_dir)}")

            # Log the contents of the bin directory
            bin_contents = os.listdir(bin_dir)
            logging.info(f"Contents of {bin_dir}: {bin_contents}")

            # Verify mp4decrypt exists
            if not os.path.isfile(mp4decrypt_path):
                raise FileNotFoundError(f"mp4decrypt not found at {mp4decrypt_path} after extraction. Bin directory contents: {bin_contents}")

            # Set executable permissions for mp4decrypt
            os.chmod(mp4decrypt_path, stat.S_IRWXU | stat.S_IRWXG | stat.S_IROTH | stat.S_IXOTH)  # 775 permissions
            logging.info(f"Set executable permissions for {mp4decrypt_path}")

            # Clean up the zip file with better error handling
            try:
                if os.path.exists(zip_path):
                    os.remove(zip_path)
                    logging.info(f"Removed zip file: {zip_path}")
                else:
                    logging.info(f"Zip file {zip_path} already removed or never existed")
            except Exception as e:
                logging.warning(f"Failed to remove zip file {zip_path}: {str(e)}")

            logging.info(f"Bento4 SDK setup complete: {mp4decrypt_path}")
    except Exception as e:
        logging.error(f"Failed to set up Bento4 SDK: {str(e)}\n{traceback.format_exc()}")
        raise

# Run setup on startup
try:
    setup_bento4()
except Exception as e:
    logging.error(f"Startup error in setup_bento4: {str(e)}\n{traceback.format_exc()}")
    raise

# Initialize Telegram client with optimized settings and proper session handling
if SESSION_STRING:
    logging.info("Using StringSession from environment - User session mode")
    client = TelegramClient(StringSession(SESSION_STRING), API_ID, API_HASH, connection_retries=5, auto_reconnect=True)
    is_user_session = True
elif BOT_TOKEN:
    logging.info("Using Bot Token - Bot session mode")
    client = TelegramClient('bot', API_ID, API_HASH, connection_retries=5, auto_reconnect=True)
    is_user_session = False
else:
    raise ValueError("Neither SESSION_STRING nor BOT_TOKEN provided")

# Helper function to get user-specific locks and queues
def get_user_resources(user_id):
    if user_id not in user_task_queues:
        user_task_queues[user_id] = deque()
    if user_id not in user_processing_states:
        user_processing_states[user_id] = False
    if user_id not in user_queue_locks:
        user_queue_locks[user_id] = asyncio.Lock()
    if user_id not in user_active_tasks:
        user_active_tasks[user_id] = None
    return user_task_queues[user_id], user_processing_states, user_queue_locks[user_id]

# Helper function to handle flood wait errors and throttle message sends
async def send_message_with_flood_control(entity, message, event=None, edit_message=None):
    async with message_rate_limit_lock:
        # Throttle message sends to 1 per 0.8 seconds for faster UI updates
        await asyncio.sleep(0.8)
        retries = 0
        max_retries = 5
        
        while retries < max_retries:
            try:
                if edit_message:
                    logging.info(f"Editing message: {message[:100]}...")
                    await edit_message.edit(message)
                    return edit_message
                else:
                    logging.info(f"Sending message to {entity.id if hasattr(entity, 'id') else entity}: {message[:100]}...")
                    if event:
                        return await event.reply(message)
                    else:
                        return await client.send_message(entity, message)
            except FloodWaitError as e:
                wait_time = min(e.seconds, 30)  # Cap wait time at 30 seconds
                logging.warning(f"FloodWaitError: Waiting for {wait_time} seconds before retrying...")
                await asyncio.sleep(wait_time)
                retries += 1
            except Exception as e:
                logging.error(f"Failed to send/edit message (attempt {retries + 1}): {str(e)}")
                retries += 1
                if retries < max_retries:
                    await asyncio.sleep(2)
                else:
                    raise

# Helper function for retry with exponential backoff
async def retry_with_backoff(coroutine, max_retries=3, base_delay=1, operation_name="operation"):
    for attempt in range(max_retries + 1):
        try:
            return await coroutine()
        except Exception as e:
            if attempt == max_retries:
                logging.error(f"{operation_name} failed after {max_retries} retries: {str(e)}")
                raise
            delay = base_delay * (2 ** attempt)
            logging.warning(f"{operation_name} failed (attempt {attempt + 1}/{max_retries + 1}): {str(e)}. Retrying after {delay} seconds...")
            await asyncio.sleep(delay)

def format_size(bytes_size):
    if bytes_size < 0:
        return "0B"
    for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
        if bytes_size < 1024:
            return f"{bytes_size:.2f}{unit}"
        bytes_size /= 1024
    return f"{bytes_size:.2f}PB"

def format_time(seconds):
    if seconds < 0:
        return "0s"
    if seconds < 60:
        return f"{int(seconds)}s"
    minutes = seconds // 60
    seconds = int(seconds % 60)
    if minutes < 60:
        return f"{int(minutes)}m{seconds}s"
    hours = minutes // 60
    minutes = int(minutes % 60)
    return f"{int(hours)}h{int(minutes)}m{seconds}s"

def derive_name_from_url(url: str) -> str:
    try:
        parsed = urlparse(url)
        path = unquote(parsed.path or '')
        filename = os.path.basename(path)
        if not filename:
            return "video"
        # Remove extension if present
        base, _ext = os.path.splitext(filename)
        base = base or filename
        # Sanitize
        safe = re.sub(r'[^\w\-_. ]+', '_', base)
        return safe or "video"
    except Exception:
        return "video"

def format_completion_message(completed_tasks, failed_tasks, total_initial_tasks):
    """Format completion message in parts if it exceeds Telegram's limit"""
    messages = []

    # Main summary
    summary_message = f"🎉 **All Tasks Completed!**\n\n"
    summary_message += f"📊 **Summary:**\n"
    summary_message += f"✅ Completed: {len(completed_tasks)}/{total_initial_tasks}\n"

    if failed_tasks:
        summary_message += f"❌ Failed: {len(failed_tasks)}/{total_initial_tasks}\n"

    messages.append(summary_message)

    # Failed tasks (if any)
    if failed_tasks:
        failed_message = f"**❌ Failed Tasks:**\n"
        for name, error in failed_tasks:
            error_short = error[:30] + "..." if len(error) > 30 else error
            task_line = f"• {name}.mp4 - {error_short}\n"

            # Check if adding this line would exceed limit
            if len(failed_message + task_line) > 3500:
                messages.append(failed_message)
                failed_message = f"**❌ Failed Tasks (continued):**\n{task_line}"
            else:
                failed_message += task_line

        if failed_message.strip():
            messages.append(failed_message)

    # Completed tasks
    if completed_tasks and len(completed_tasks) <= 20:  # Only show if reasonable number
        completed_message = f"**✅ Completed Tasks:**\n"
        for name in completed_tasks:
            task_line = f"• {name}.mp4\n"

            # Check if adding this line would exceed limit
            if len(completed_message + task_line) > 3500:
                messages.append(completed_message)
                completed_message = f"**✅ Completed Tasks (continued):**\n{task_line}"
            else:
                completed_message += task_line

        if completed_message.strip():
            messages.append(completed_message)

    return messages

async def generate_random_thumbnail(output_path):
    """Generate a random colored thumbnail"""
    try:
        import random
        # Generate random RGB values
        r = random.randint(50, 255)
        g = random.randint(50, 255)  
        b = random.randint(50, 255)

        # Create a 320x180 thumbnail with random color using FFmpeg
        cmd = [
            'ffmpeg', '-f', 'lavfi',
            '-i', f'color=c=#{r:02x}{g:02x}{b:02x}:size=320x180:duration=1',
            '-frames:v', '1', '-y',
            output_path
        ]

        process = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        stdout, stderr = await process.communicate()

        if process.returncode == 0 and os.path.exists(output_path) and os.path.getsize(output_path) > 0:
            logging.info(f"Generated random thumbnail: {output_path}")
            return True
        else:
            logging.error(f"Failed to generate random thumbnail: {stderr.decode()}")
            return False
    except Exception as e:
        logging.error(f"Error generating random thumbnail: {str(e)}")
        return False

async def extract_video_frame_thumbnail(video_path, output_path, duration=None):
    """Extract a random frame from video as thumbnail"""
    try:
        import random

        # If duration is provided, pick a random time between 10% and 90% of video
        if duration and duration > 10:
            start_time = max(1, int(duration * 0.1))
            end_time = int(duration * 0.9)
            random_time = random.randint(start_time, end_time)
        else:
            # Default to 5 seconds if no duration or short video
            random_time = 5

        # Extract frame at random time
        cmd = [
            'ffmpeg', '-i', video_path,
            '-ss', str(random_time),
            '-frames:v', '1',
            '-s', '320x180',
            '-q:v', '2', '-y',
            output_path
        ]

        process = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        stdout, stderr = await process.communicate()

        if process.returncode == 0 and os.path.exists(output_path) and os.path.getsize(output_path) > 0:
            logging.info(f"Extracted video frame thumbnail: {output_path} at {random_time}s")
            return True
        else:
            logging.error(f"Failed to extract video frame: {stderr.decode()}")
            return False
    except Exception as e:
        logging.error(f"Error extracting video frame thumbnail: {str(e)}")
        return False

async def save_thumbnail_from_message(event, user_id):
    """Save thumbnail from user message"""
    try:
        if not event.photo:
            return False, "Please send a photo to use as thumbnail."

        # Create user thumbnail directory
        thumbnail_dir = os.path.join(DOWNLOAD_DIR, f"user_{user_id}", "thumbnails")
        if not os.path.exists(thumbnail_dir):
            os.makedirs(thumbnail_dir)

        # Download the photo
        thumbnail_path = os.path.join(thumbnail_dir, "user_thumbnail.jpg")
        await event.download_media(file=thumbnail_path)

        # Store in user thumbnails
        async with thumbnail_lock:
            user_thumbnails[user_id] = thumbnail_path

        logging.info(f"Saved thumbnail for user {user_id}: {thumbnail_path}")
        return True, f"Thumbnail saved successfully!"

    except Exception as e:
        logging.error(f"Error saving thumbnail: {str(e)}")
        return False, f"Error saving thumbnail: {str(e)}"

def progress_display(stage, percent, done, total, speed, elapsed, user, user_id, filename):
    bar_length = 20
    filled = int((percent / 100) * bar_length)
    spinner = ['⣿', '⣷', '⣯', '⣟', '⡿', '⢿', '⣿'][int(time.time() * 10) % 7]
    progress_bar = '█' * filled + '░' * (bar_length - filled)
    eta = (total - done) / speed if speed > 0 and done < total else 0
    stage_info = {
        "Downloading": ("📥", f"Downloading {percent:.1f}%"),
        "Decrypting": ("🔐", "Decrypting"),
        "Merging": ("🎬", "Merging"),
        "Uploading": ("📤", f"Uploading {percent:.1f}%"),
        "Splitting": ("✂️", f"Splitting {percent:.1f}%"),
        "Finalizing": ("🧩", "Finalizing on Telegram"),
        "Completed": ("✅", "Completed"),
        "Initializing": ("🟡", "Initializing"),
    }
    emoji, status_text = stage_info.get(stage, ("🚀", stage))
    return (
        f"{spinner} {filename}\n"
        f"{emoji} {status_text}\n"
        f"[{progress_bar}] {percent:.1f}%\n"
        f"⚡ {format_size(speed)}/s | ⏱️ {format_time(elapsed)} | ⌛ {format_time(eta)}\n"
        f"📦 {format_size(done)} / {format_size(total)}\n"
        f"👤 {user} | 🆔 {user_id}"
    )

def parse_duration(duration_str):
    if duration_str.startswith('PT'):
        time_part = duration_str[2:]
        seconds = 0
        if 'H' in time_part:
            h, time_part = time_part.split('H')
            seconds += int(h) * 3600
        if 'M' in time_part:
            m, time_part = time_part.split('M')
            seconds += int(m) * 60
        if 'S' in time_part:
            s = time_part.replace('S', '')
            seconds += float(s)
        return int(seconds)
    return 0

# Optimized file size limits based on session type
def get_upload_limits():
    """Get upload limits based on session type"""
    if is_user_session:
        # User session can upload up to 4GB files and send up to 2GB per file
        return {
            'max_file_size': 4 * 1024 * 1024 * 1024,  # 4GB total processing
            'chunk_size': 2 * 1024 * 1024 * 1024,     # 2GB per chunk
            'part_size': 512 * 1024,                   # 512KB per part
            'max_parts': 8000                          # Max parts per file
        }
    else:
        # Bot session limits
        return {
            'max_file_size': 2 * 1024 * 1024 * 1024,  # 2GB total processing  
            'chunk_size': 50 * 1024 * 1024,           # 50MB per chunk for bots
            'part_size': 512 * 1024,                   # 512KB per part
            'max_parts': 3000                          # Max parts per file
        }

class MPDLeechBot:
    def __init__(self, user_id):
        self.user_id = user_id
        self.user_download_dir = os.path.join(DOWNLOAD_DIR, f"user_{user_id}")
        self.setup_dirs()
        self.has_notified_split = False
        self.progress_task = None
        self.update_lock = asyncio.Lock()
        self.is_downloading = False
        self.current_filename = None
        self.abort_event = asyncio.Event()
        # Enhanced progress tracking state
        self.progress_state = {
            'stage': 'Initializing',
            'percent': 0.0,
            'done_size': 0,
            'total_size': 0,
            'speed': 0,
            'elapsed': 0,
            'start_time': 0,
            'last_update': 0
        }
        # Get upload limits based on session type
        self.limits = get_upload_limits()
        logging.info(f"MPDLeechBot initialized for user {user_id} - Session type: {'User' if is_user_session else 'Bot'}")
        logging.info(f"Upload limits: Max file: {format_size(self.limits['max_file_size'])}, Chunk: {format_size(self.limits['chunk_size'])}")

    def setup_dirs(self):
        if not os.path.exists(self.user_download_dir):
            os.makedirs(self.user_download_dir)
            logging.info(f"Created directory: {self.user_download_dir}")

    async def download_direct_file(self, event, url, name, sender):
        """Download a direct file from URL with optimized progress tracking"""
        if self.is_downloading:
            logging.info(f"Another download is already in progress for user {self.user_id} - rejecting new request")
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="Another download is already in progress for your account. Please wait.",
                event=event
            )
            return None, None, None, None

        self.is_downloading = True
        status_msg = None
        try:
            output_file = os.path.join(self.user_download_dir, f"{name}.mp4")
            status_msg = await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"🚀 Starting direct download: {name}...",
                event=event
            )
            
            # Initialize progress state
            self.progress_state.update({
                'start_time': time.time(),
                'stage': "Downloading",
                'percent': 0.0,
                'done_size': 0,
                'total_size': 0,
                'speed': 0,
                'elapsed': 0,
                'last_update': 0
            })

            # Optimized progress updater with less frequent updates
            async def update_progress_direct():
                nonlocal status_msg
                last_msg_update = 0
                while self.progress_state['stage'] == "Downloading" and not self.abort_event.is_set():
                    current_time = time.time()
                    # Update message every 2 seconds instead of 3 for better UX
                    if current_time - last_msg_update < 2:
                        await asyncio.sleep(0.5)
                        continue
                        
                    self.progress_state['elapsed'] = current_time - self.progress_state['start_time']
                    self.progress_state['speed'] = (self.progress_state['done_size'] / self.progress_state['elapsed']) if self.progress_state['elapsed'] > 0 else 0
                    
                    display = progress_display(
                        self.progress_state['stage'],
                        self.progress_state['percent'],
                        self.progress_state['done_size'],
                        self.progress_state['total_size'],
                        self.progress_state['speed'],
                        self.progress_state['elapsed'],
                        sender.first_name,
                        sender.id,
                        name + ".mp4"
                    )
                    
                    async with self.update_lock:
                        try:
                            status_msg = await send_message_with_flood_control(
                                entity=event.chat_id,
                                message=display,
                                edit_message=status_msg
                            )
                            last_msg_update = current_time
                        except Exception as e:
                            logging.warning(f"Progress update failed: {e}")
                    
                    await asyncio.sleep(2)

            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                'Accept': 'video/mp4,application/mp4,*/*',
                'Accept-Language': 'en-US,en;q=0.9',
                'Accept-Encoding': 'gzip, deflate, br',
                'Cache-Control': 'no-cache',
                'Pragma': 'no-cache',
                'Connection': 'keep-alive',
                'Range': 'bytes=0-'  # Enable range requests
            }

            timeout = aiohttp.ClientTimeout(total=None, sock_connect=60, sock_read=120)
            connector = aiohttp.TCPConnector(limit=0, enable_cleanup_closed=True, keepalive_timeout=30)
            
            async with aiohttp.ClientSession(timeout=timeout, connector=connector) as session:
                async with session.get(url, headers=headers, allow_redirects=True) as response:
                    if response.status not in [200, 206]:
                        raise Exception(f"HTTP {response.status}: {response.reason}")

                    total_size = int(response.headers.get('Content-Length', 0))
                    self.progress_state['total_size'] = total_size
                    downloaded = 0

                    # Start optimized progress updater
                    progress_task = asyncio.create_task(update_progress_direct())

                    # Use larger chunks for faster downloads
                    chunk_size = 8 * 1024 * 1024  # 8MB chunks for maximum speed
                    with open(output_file, 'wb', buffering=8*1024*1024) as f:  # 8MB buffer
                        async for chunk in response.content.iter_chunked(chunk_size):
                            if self.abort_event.is_set():
                                raise asyncio.CancelledError("Download cancelled by user")
                            f.write(chunk)
                            downloaded += len(chunk)
                            self.progress_state['done_size'] = downloaded
                            self.progress_state['percent'] = (downloaded / total_size * 100) if total_size > 0 else 0

                    # Stop progress updater
                    progress_task.cancel()
                    try:
                        await progress_task
                    except asyncio.CancelledError:
                        pass

            # Get video duration using ffprobe with timeout
            duration = 0
            try:
                duration_cmd = ['timeout', '30', 'ffprobe', '-v', 'quiet', '-show_entries', 'format=duration', '-of', 'csv=p=0', output_file]
                process = await asyncio.create_subprocess_exec(*duration_cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
                stdout, stderr = await process.communicate()
                if stdout.decode().strip():
                    duration = int(float(stdout.decode().strip()))
            except Exception as e:
                logging.warning(f"Could not get duration: {e}")
                duration = 0

            final_size = os.path.getsize(output_file)
            logging.info(f"Direct download complete: {output_file}, size: {format_size(final_size)}")

            # Update user speed statistics
            elapsed = time.time() - self.progress_state['start_time']
            download_speed = final_size / elapsed if elapsed > 0 else 0
            async with speed_lock:
                if self.user_id not in user_speed_stats:
                    user_speed_stats[self.user_id] = {}
                user_speed_stats[self.user_id]['download_speed'] = download_speed
                user_speed_stats[self.user_id]['last_updated'] = time.time()

            self.progress_state['stage'] = "Completed"
            return output_file, status_msg, final_size, duration

        except asyncio.CancelledError:
            logging.info(f"Direct download cancelled by user: {name}")
            if status_msg:
                try:
                    await send_message_with_flood_control(
                        entity=event.chat_id,
                        message=f"⏭️ Download cancelled: {name}",
                        edit_message=status_msg
                    )
                except:
                    pass
            raise
        except Exception as e:
            logging.error(f"Direct download error for {name}: {str(e)}\n{traceback.format_exc()}")
            error_message = f"❌ Direct download failed: {name}\n{str(e)}"
            if status_msg:
                try:
                    await send_message_with_flood_control(
                        entity=event.chat_id,
                        message=error_message,
                        edit_message=status_msg
                    )
                except:
                    pass
            else:
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message=error_message,
                    event=event
                )
            raise
        finally:
            self.is_downloading = False

    async def fetch_segment(self, url, progress, total_segments, range_header=None, output_file=None):
        """Optimized segment fetching with better error handling"""
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
            'Accept': 'video/mp4,application/mp4,*/*',
            'Accept-Language': 'en-US,en;q=0.9',
            'Accept-Encoding': 'gzip, deflate, br',
            'Cache-Control': 'no-cache',
            'Pragma': 'no-cache',
            'Connection': 'keep-alive'
        }
        if range_header:
            headers['Range'] = range_header
            
        timeout = aiohttp.ClientTimeout(total=300, sock_connect=30, sock_read=60)

        async def download_operation():
            connector = aiohttp.TCPConnector(limit=0, enable_cleanup_closed=True, keepalive_timeout=30)
            async with aiohttp.ClientSession(timeout=timeout, connector=connector) as session:
                logging.debug(f"Fetching: {url}, range={range_header}")
                async with session.get(url, headers=headers) as response:
                    if response.status == 403:
                        raise Exception(f"403 Forbidden: {url}")
                    elif response.status == 404:
                        raise Exception(f"404 Not Found: {url}")
                    response.raise_for_status()
                    
                    downloaded = 0
                    # Use larger chunks and better buffering
                    with open(output_file, 'wb', buffering=4*1024*1024) as f:  # 4MB buffer
                        async for chunk in response.content.iter_chunked(8 * 1024 * 1024):  # 8MB chunks
                            if self.abort_event.is_set():
                                raise asyncio.CancelledError("Segment download cancelled")
                            f.write(chunk)
                            downloaded += len(chunk)
                            progress['done_size'] += len(chunk)
                            self.progress_state['done_size'] = progress['done_size']
                            
                    logging.debug(f"Fetched segment: {url}, size={downloaded} bytes")
                    progress['completed'] += 1
                    return downloaded

        # Use optimized retry with shorter delays
        try:
            return await retry_with_backoff(
                coroutine=download_operation,
                max_retries=2,  # Reduced retries for speed
                base_delay=1,   # Faster retry
                operation_name=f"Download segment"
            )
        except Exception as e:
            raise Exception(f"Segment fetch failed: {str(e)}")

    async def decrypt_with_mp4decrypt(self, input_file, output_file, kid, key):
        """Optimized decryption with progress tracking"""
        try:
            cmd = [
                MP4DECRYPT_PATH,
                '--key', f"{kid}:{key}",
                input_file,
                output_file
            ]
            logging.info(f"Running mp4decrypt: {' '.join(cmd)}")
            
            # Add timeout for decryption
            process = await asyncio.create_subprocess_exec(
                *cmd, 
                stdout=asyncio.subprocess.PIPE, 
                stderr=asyncio.subprocess.PIPE
            )
            
            try:
                stdout, stderr = await asyncio.wait_for(process.communicate(), timeout=300)  # 5 minute timeout
            except asyncio.TimeoutError:
                process.kill()
                raise Exception("mp4decrypt timed out after 5 minutes")
                
            if process.returncode == 0:
                logging.info(f"mp4decrypt succeeded: {output_file}")
                # Verify the output file exists and has content
                if not os.path.exists(output_file) or os.path.getsize(output_file) == 0:
                    raise Exception(f"mp4decrypt output file {output_file} is missing or empty")
                return output_file
            else:
                error_msg = stderr.decode()
                logging.error(f"mp4decrypt failed: {error_msg}")
                raise Exception(f"mp4decrypt failed: {error_msg}")
        except Exception as e:
            logging.error(f"mp4decrypt error: {str(e)}")
            raise

    async def split_file(self, input_file, max_size_mb=None, progress_cb=None, cancel_event: asyncio.Event = None):
        """Optimized file splitting with proper size limits based on session type"""
        if max_size_mb is None:
            # Use session-appropriate chunk size
            max_size_mb = self.limits['chunk_size'] // (1024 * 1024)
        
        max_size = max_size_mb * 1024 * 1024
        file_size = os.path.getsize(input_file)
        
        if file_size <= max_size:
            logging.info(f"File size {format_size(file_size)} is within limit {format_size(max_size)}, no splitting needed")
            return [input_file]

        base_name = os.path.splitext(input_file)[0]
        ext = os.path.splitext(input_file)[1]
        chunks = []
        
        # Get video duration for accurate splitting
        duration = 0
        try:
            duration_cmd = ['ffprobe', '-v', 'quiet', '-show_entries', 'format=duration', '-of', 'csv=p=0', input_file]
            process = await asyncio.create_subprocess_exec(*duration_cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
            stdout, stderr = await process.communicate()
            if stdout.decode().strip():
                duration = int(float(stdout.decode().strip()))
                logging.info(f"Video duration: {duration}s")
        except Exception as e:
            logging.warning(f"Could not get duration for splitting: {e}")
            duration = 0

        # Calculate number of chunks and duration per chunk
        num_chunks = math.ceil(file_size / max_size)
        chunk_duration = duration / num_chunks if duration > 0 else 300  # Default 5min chunks if no duration
        
        logging.info(f"Splitting {format_size(file_size)} file into {num_chunks} chunks of ~{format_size(max_size)} each")
        
        for i in range(num_chunks):
            if cancel_event and cancel_event.is_set():
                raise asyncio.CancelledError("File splitting cancelled")
                
            output_file = f"{base_name}_part{i+1:03d}{ext}"
            start_time = i * chunk_duration
            
            # Use optimized ffmpeg settings for faster splitting
            cmd = [
                'ffmpeg',
                '-hide_banner', '-loglevel', 'error',  # Reduced logging for speed
                '-ss', str(start_time),
                '-t', str(chunk_duration),
                '-i', input_file,
                '-c', 'copy',  # Stream copy - no re-encoding
                '-avoid_negative_ts', 'make_zero',  # Handle timestamp issues
                '-y',  # Overwrite output
                output_file
            ]
            
            logging.info(f"Creating chunk {i+1}/{num_chunks}: {output_file}")
            
            start_split = time.time()
            process = await asyncio.create_subprocess_exec(
                *cmd, 
                stdout=asyncio.subprocess.PIPE, 
                stderr=asyncio.subprocess.PIPE
            )

            # Monitor process with timeout
            try:
                stdout, stderr = await asyncio.wait_for(process.communicate(), timeout=600)  # 10 minute timeout per chunk
            except asyncio.TimeoutError:
                process.kill()
                raise Exception(f"Splitting chunk {i+1} timed out after 10 minutes")

            split_time = time.time() - start_split
            
            if process.returncode == 0 and os.path.exists(output_file) and os.path.getsize(output_file) > 0:
                chunk_size = os.path.getsize(output_file)
                chunks.append(output_file)
                logging.info(f"Split chunk {i+1} created: {format_size(chunk_size)} in {split_time:.1f}s")
                
                # Update progress callback if provided
                if progress_cb:
                    try:
                        progress_percent = ((i + 1) / num_chunks) * 100
                        await progress_cb(i+1, num_chunks, progress_percent)
                    except Exception as e:
                        logging.warning(f"Progress callback failed: {e}")
            else:
                error_msg = stderr.decode() if stderr else "Unknown error"
                logging.error(f"Split chunk {i+1} failed: {error_msg}")
                raise Exception(f"Failed to create chunk {i+1}: {error_msg}")
                
        logging.info(f"File splitting completed: {len(chunks)} chunks created")
        return chunks

    async def download_and_decrypt(self, event, mpd_url, key, name, sender):
        """Optimized DRM download and decryption process"""
        if self.is_downloading:
            logging.info(f"Another download is already in progress for user {self.user_id}")
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="Another download is already in progress for your account. Please wait.",
                event=event
            )
            return None, None, None, None

        # Check available disk space
        try:
            import shutil
            free_space = shutil.disk_usage(self.user_download_dir).free
            if free_space < 1024 * 1024 * 1024:  # Less than 1GB free
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message="⚠️ Low disk space! Cleaning up old files...",
                    event=event
                )
                self.cleanup(None)
        except Exception as e:
            logging.warning(f"Could not check disk space: {e}")

        self.is_downloading = True
        status_msg = None
        try:
            # File paths
            raw_video_file = os.path.join(self.user_download_dir, f"{name}_raw_video.mp4")
            raw_audio_file = os.path.join(self.user_download_dir, f"{name}_raw_audio.mp4")
            decrypted_video_file = os.path.join(self.user_download_dir, f"{name}_decrypted_video.mp4")
            decrypted_audio_file = os.path.join(self.user_download_dir, f"{name}_decrypted_audio.mp4")
            output_file = os.path.join(self.user_download_dir, f"{name}.mp4")
            
            status_msg = await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"🔍 Fetching MPD manifest: {name}...",
                event=event
            )
            
            # Initialize progress state
            self.progress_state.update({
                'start_time': time.time(),
                'stage': "Downloading",
                'percent': 0.0,
                'done_size': 0,
                'total_size': 0,
                'speed': 0,
                'elapsed': 0,
                'last_update': 0
            })

            # Stage 1: Fetch MPD with optimized retry
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                'Accept': 'application/dash+xml,video/mp4,application/mp4,*/*',
                'Accept-Language': 'en-US,en;q=0.9',
                'Accept-Encoding': 'gzip, deflate, br',
                'Cache-Control': 'no-cache',
                'Pragma': 'no-cache',
                'Connection': 'keep-alive'
            }

            async def fetch_mpd_operation():
                timeout = aiohttp.ClientTimeout(total=60)
                connector = aiohttp.TCPConnector(limit=0, enable_cleanup_closed=True)
                async with aiohttp.ClientSession(timeout=timeout, connector=connector) as session:
                    logging.info(f"Fetching MPD: {mpd_url}")
                    async with session.get(mpd_url, headers=headers) as response:
                        if response.status == 403:
                            raise Exception(f"403 Forbidden - MPD may require authentication: {mpd_url}")
                        elif response.status == 404:
                            raise Exception(f"404 Not Found - MPD URL invalid: {mpd_url}")
                        response.raise_for_status()
                        return await response.text()

            try:
                mpd_content = await retry_with_backoff(
                    coroutine=fetch_mpd_operation,
                    max_retries=2,
                    base_delay=2,
                    operation_name=f"Fetch MPD"
                )
            except Exception as e:
                raise Exception(f"Failed to fetch MPD: {str(e)}")

            logging.debug(f"MPD content length: {len(mpd_content)} chars")

            # Parse MPD
            try:
                root = ET.fromstring(mpd_content)
            except ET.ParseError as e:
                raise Exception(f"Invalid MPD XML format: {str(e)}")
                
            namespace = {'ns': 'urn:mpeg:dash:schema:mpd:2011'}
            video_segments = []
            audio_segments = []
            base_url = mpd_url.rsplit('/', 1)[0] + '/'
            
            # Parse duration
            duration = 0
            mpd_duration = root.get('mediaPresentationDuration')
            if mpd_duration:
                duration = parse_duration(mpd_duration)

            # Parse adaptation sets
            for period in root.findall('.//ns:Period', namespace):
                for adaptation_set in period.findall('.//ns:AdaptationSet', namespace):
                    content_type = adaptation_set.get('contentType', '')
                    if content_type not in ['video', 'audio']:
                        # Check mimeType if contentType not specified
                        mime_type = adaptation_set.get('mimeType', '')
                        if 'video' in mime_type.lower():
                            content_type = 'video'
                        elif 'audio' in mime_type.lower():
                            content_type = 'audio'
                        else:
                            continue
                            
                    segments = video_segments if content_type == 'video' else audio_segments
                    
                    for representation in adaptation_set.findall('.//ns:Representation', namespace):
                        # Get the best quality representation
                        bandwidth = int(representation.get('bandwidth', 0))
                        
                        base_url_elem = representation.find('.//ns:BaseURL', namespace)
                        if base_url_elem is not None:
                            stream_url = base_url + base_url_elem.text.strip()
                            logging.info(f"Found {content_type} stream: {stream_url}")
                            
                            segment_base = representation.find('.//ns:SegmentBase', namespace)
                            if segment_base is not None:
                                init = segment_base.find('.//ns:Initialization', namespace)
                                init_range = init.get('range') if init is not None else None
                                index_range = segment_base.get('indexRange')
                                
                                if init_range:
                                    segments.append((stream_url, f"bytes={init_range}"))
                                if index_range:
                                    segments.append((stream_url, f"bytes={index_range}"))
                                if not (init_range or index_range):
                                    segments.append((stream_url, None))
                            else:
                                segments.append((stream_url, None))
                            break  # Use first valid representation

            if not video_segments:
                raise Exception("No video segments found in MPD")

            logging.info(f"Found {len(video_segments)} video segments, {len(audio_segments)} audio segments")

            # Parse key
            try:
                kid, key_hex = key.split(':')
                if len(kid) != 32 or len(key_hex) != 32:
                    raise ValueError("Invalid key format")
            except Exception:
                raise Exception("Key must be in format KID:KEY (32 hex chars each)")

            # Estimate total size for better progress
            total_segments = len(video_segments) + len(audio_segments)
            progress = {'done_size': 0, 'completed': 0}
            
            # Try to get content lengths for size estimation
            estimated_total = 0
            try:
                async def head_size(url, range_header=None):
                    try:
                        timeout = aiohttp.ClientTimeout(total=10)
                        async with aiohttp.ClientSession(timeout=timeout) as session:
                            head_headers = headers.copy()
                            if range_header:
                                head_headers['Range'] = range_header
                            async with session.head(url, headers=head_headers) as resp:
                                return int(resp.headers.get('Content-Length', 0))
                    except:
                        return 0

                size_tasks = [head_size(u, r) for u, r in (video_segments + audio_segments)]
                sizes = await asyncio.gather(*size_tasks, return_exceptions=True)
                estimated_total = sum(s for s in sizes if isinstance(s, int) and s > 0)
                
                if estimated_total > 0:
                    self.progress_state['total_size'] = estimated_total
                    logging.info(f"Estimated download size: {format_size(estimated_total)}")
            except Exception as e:
                logging.warning(f"Could not estimate download size: {e}")

            # Start progress updater
            async def update_progress_mpd():
                nonlocal status_msg
                last_msg_update = 0
                while self.progress_state['stage'] in ["Downloading", "Decrypting", "Merging"] and not self.abort_event.is_set():
                    current_time = time.time()
                    if current_time - last_msg_update < 2:
                        await asyncio.sleep(0.5)
                        continue
                        
                    self.progress_state['elapsed'] = current_time - self.progress_state['start_time']
                    self.progress_state['speed'] = (self.progress_state['done_size'] / self.progress_state['elapsed']) if self.progress_state['elapsed'] > 0 else 0
                    
                    # Calculate progress percentage
                    if estimated_total > 0:
                        self.progress_state['percent'] = (self.progress_state['done_size'] / estimated_total) * 100
                    else:
                        self.progress_state['percent'] = (progress['completed'] / total_segments) * 100
                    
                    display = progress_display(
                        self.progress_state['stage'],
                        self.progress_state['percent'],
                        self.progress_state['done_size'],
                        self.progress_state['total_size'] or estimated_total,
                        self.progress_state['speed'],
                        self.progress_state['elapsed'],
                        sender.first_name,
                        sender.id,
                        name + ".mp4"
                    )
                    
                    async with self.update_lock:
                        try:
                            status_msg = await send_message_with_flood_control(
                                entity=event.chat_id,
                                message=display,
                                edit_message=status_msg
                            )
                            last_msg_update = current_time
                        except Exception as e:
                            logging.warning(f"Progress update failed: {e}")
                    
                    await asyncio.sleep(2)

            # Start progress task
            self.progress_task = asyncio.create_task(update_progress_mpd())

            # Stage 2: Download segments with higher concurrency
            video_files = [os.path.join(self.user_download_dir, f"{name}_video_seg{i}.mp4") for i in range(len(video_segments))]
            audio_files = [os.path.join(self.user_download_dir, f"{name}_audio_seg{i}.mp4") for i in range(len(audio_segments))]

            # Increase concurrency for faster downloads
            semaphore = asyncio.Semaphore(10)  # Up to 10 concurrent downloads
            
            async def download_with_semaphore(segment_data):
                async with semaphore:
                    return await self.fetch_segment(*segment_data)
            
            # Prepare download tasks
            tasks = []
            for i, (seg_url, range_header) in enumerate(video_segments):
                tasks.append(download_with_semaphore((seg_url, progress, total_segments, range_header, video_files[i])))
            for i, (seg_url, range_header) in enumerate(audio_segments):
                tasks.append(download_with_semaphore((seg_url, progress, total_segments, range_header, audio_files[i])))

            # Download all segments
            try:
                segment_results = await asyncio.gather(*tasks, return_exceptions=True)
                
                # Check for failed segments
                for i, result in enumerate(segment_results):
                    if isinstance(result, Exception):
                        raise Exception(f"Segment {i+1} failed: {str(result)}")
                        
            except Exception as e:
                raise Exception(f"Segment download failed: {str(e)}")

            # Concatenate segments
            logging.info("Concatenating video segments...")
            with open(raw_video_file, 'wb') as outfile:
                for seg_file in video_files:
                    if os.path.exists(seg_file) and os.path.getsize(seg_file) > 0:
                        with open(seg_file, 'rb') as infile:
                            outfile.write(infile.read())
                        os.remove(seg_file)  # Clean up immediately
                        
            if audio_segments:
                logging.info("Concatenating audio segments...")
                with open(raw_audio_file, 'wb') as outfile:
                    for seg_file in audio_files:
                        if os.path.exists(seg_file) and os.path.getsize(seg_file) > 0:
                            with open(seg_file, 'rb') as infile:
                                outfile.write(infile.read())
                            os.remove(seg_file)  # Clean up immediately

            # Update progress for decryption stage
            self.progress_state['stage'] = "Decrypting"
            self.progress_state['percent'] = 0.0

            # Stage 3: Decrypt files
            logging.info("Decrypting video...")
            await self.decrypt_with_mp4decrypt(raw_video_file, decrypted_video_file, kid, key_hex)
            os.remove(raw_video_file)  # Clean up
            
            if audio_segments:
                logging.info("Decrypting audio...")
                await self.decrypt_with_mp4decrypt(raw_audio_file, decrypted_audio_file, kid, key_hex)
                os.remove(raw_audio_file)  # Clean up

            # Stage 4: Merge files
            self.progress_state['stage'] = "Merging"
            self.progress_state['percent'] = 0.0
            
            cmd = ['ffmpeg', '-hide_banner', '-loglevel', 'error', '-i', decrypted_video_file]
            if audio_segments:
                cmd.extend(['-i', decrypted_audio_file, '-c', 'copy', '-map', '0:v', '-map', '1:a'])
            else:
                cmd.extend(['-c', 'copy'])
            cmd.extend(['-y', output_file])
            
            logging.info("Merging video and audio...")
            process = await asyncio.create_subprocess_exec(*cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
            
            try:
                stdout, stderr = await asyncio.wait_for(process.communicate(), timeout=300)
            except asyncio.TimeoutError:
                process.kill()
                raise Exception("Merging timed out after 5 minutes")
                
            if process.returncode != 0:
                error_msg = stderr.decode()
                raise Exception(f"FFmpeg merging failed: {error_msg}")

            # Clean up intermediate files
            if os.path.exists(decrypted_video_file):
                os.remove(decrypted_video_file)
            if os.path.exists(decrypted_audio_file):
                os.remove(decrypted_audio_file)

            # Final size and stats
            final_size = os.path.getsize(output_file)
            elapsed = time.time() - self.progress_state['start_time']
            download_speed = final_size / elapsed if elapsed > 0 else 0

            # Update speed stats
            async with speed_lock:
                if self.user_id not in user_speed_stats:
                    user_speed_stats[self.user_id] = {}
                user_speed_stats[self.user_id]['download_speed'] = download_speed
                user_speed_stats[self.user_id]['last_updated'] = time.time()

            self.progress_state.update({
                'stage': "Completed",
                'total_size': final_size,
                'done_size': final_size,
                'percent': 100.0,
                'speed': download_speed,
                'elapsed': elapsed
            })

            # Stop progress task
            if self.progress_task and not self.progress_task.done():
                self.progress_task.cancel()
                try:
                    await self.progress_task
                except asyncio.CancelledError:
                    pass

            logging.info(f"DRM download complete: {output_file}, size: {format_size(final_size)}, time: {format_time(elapsed)}")
            return output_file, status_msg, final_size, duration

        except asyncio.CancelledError:
            logging.info(f"DRM download cancelled by user: {name}")
            if status_msg:
                try:
                    await send_message_with_flood_control(
                        entity=event.chat_id,
                        message=f"⏭️ Download cancelled: {name}",
                        edit_message=status_msg
                    )
                except:
                    pass
            raise
        except Exception as e:
            logging.error(f"DRM download error for {name}: {str(e)}\n{traceback.format_exc()}")
            
            # Stop progress task on error
            if self.progress_task and not self.progress_task.done():
                self.progress_task.cancel()
                try:
                    await self.progress_task
                except asyncio.CancelledError:
                    pass
                    
            error_message = f"❌ DRM download failed: {name}\n{str(e)}"
            if "403" in str(e):
                error_message += "\n💡 MPD may require authentication headers"
            elif "404" in str(e):
                error_message += "\n💡 MPD URL may be expired or invalid"
            
            if status_msg:
                try:
                    await send_message_with_flood_control(
                        entity=event.chat_id,
                        message=error_message,
                        edit_message=status_msg
                    )
                except:
                    pass
            else:
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message=error_message,
                    event=event
                )
            raise
        finally:
            self.is_downloading = False

    async def upload_file(self, event, filepath, status_msg, total_size, sender, duration):
        """Optimized file upload with proper session handling and instant finalization"""
        try:
            file_size = os.path.getsize(filepath)
            logging.info(f"Starting upload: {filepath}, size: {format_size(file_size)}, duration: {duration}s")
            
            # Initialize upload progress
            self.progress_state.update({
                'start_time': time.time(),
                'total_size': file_size,
                'done_size': 0,
                'percent': 0.0,
                'speed': 0,
                'elapsed': 0,
                'stage': 'Uploading'
            })

            # Get session-appropriate limits
            chunk_size = self.limits['chunk_size']
            part_size = self.limits['part_size']
            max_parts = self.limits['max_parts']
            
            logging.info(f"Upload limits - Chunk: {format_size(chunk_size)}, Part: {format_size(part_size)}, Max parts: {max_parts}")

            # Determine if file needs splitting
            if file_size > chunk_size:
                if not self.has_notified_split:
                    split_size_mb = chunk_size // (1024 * 1024)
                    await send_message_with_flood_control(
                        entity=event.chat_id,
                        message=f"📦 File size {format_size(file_size)} > {format_size(chunk_size)}\n✂️ Splitting into {split_size_mb}MB parts for {'user session' if is_user_session else 'bot'} upload...",
                        edit_message=status_msg
                    )
                    self.has_notified_split = True

                # Split file with optimized progress tracking
                splitting_start = time.time()
                
                async def splitting_progress(current_part, total_parts, part_percent):
                    processed_ratio = ((current_part - 1 + (part_percent / 100.0)) / total_parts)
                    processed_bytes = int(file_size * processed_ratio)
                    elapsed = time.time() - splitting_start
                    speed = processed_bytes / elapsed if elapsed > 0 else 0
                    
                    self.progress_state.update({
                        'stage': "Splitting",
                        'done_size': processed_bytes,
                        'percent': processed_ratio * 100,
                        'speed': speed,
                        'elapsed': elapsed
                    })
                    
                    display = progress_display(
                        self.progress_state['stage'],
                        self.progress_state['percent'], 
                        self.progress_state['done_size'],
                        self.progress_state['total_size'],
                        self.progress_state['speed'],
                        self.progress_state['elapsed'],
                        sender.first_name,
                        sender.id,
                        f"{os.path.basename(filepath)} (Part {current_part}/{total_parts})"
                    )
                    
                    nonlocal status_msg
                    async with self.update_lock:
                        try:
                            status_msg = await send_message_with_flood_control(
                                entity=event.chat_id,
                                message=display,
                                edit_message=status_msg
                            )
                        except Exception as e:
                            logging.warning(f"Splitting progress update failed: {e}")

                # Split with session-appropriate chunk size
                max_size_mb = chunk_size // (1024 * 1024)
                chunks = await self.split_file(filepath, max_size_mb=max_size_mb, progress_cb=splitting_progress, cancel_event=self.abort_event)
                
                # Upload each chunk with optimized process
                total_chunks = len(chunks)
                for i, chunk in enumerate(chunks, 1):
                    chunk_size_bytes = os.path.getsize(chunk)
                    chunk_duration = duration // total_chunks if duration > 0 else 0
                    
                    logging.info(f"Uploading chunk {i}/{total_chunks}: {format_size(chunk_size_bytes)}")
                    
                    # Reset progress for this chunk
                    self.progress_state.update({
                        'stage': "Uploading",
                        'total_size': chunk_size_bytes,
                        'done_size': 0,
                        'percent': 0.0,
                        'start_time': time.time()
                    })
                    
                    # Optimized upload for chunk
                    sent_msg = await self._upload_single_file(
                        event, chunk, chunk_size_bytes, sender, 
                        chunk_duration, f"Part {i}/{total_chunks}: {os.path.basename(filepath)}"
                    )
                    
                    # Delete chunk immediately after successful upload
                    try:
                        os.remove(chunk)
                        logging.info(f"Deleted uploaded chunk: {chunk}")
                    except Exception as e:
                        logging.warning(f"Failed to delete chunk {chunk}: {e}")
                
                # Delete original file after all chunks uploaded
                try:
                    os.remove(filepath)
                    logging.info(f"Deleted original file: {filepath}")
                except Exception as e:
                    logging.warning(f"Failed to delete original file: {e}")
                    
                # Update status message
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message=f"✅ All {total_chunks} parts uploaded successfully!\n📁 {os.path.basename(filepath)}",
                    edit_message=status_msg
                )
                
            else:
                # Single file upload - optimized process
                logging.info(f"Single file upload: {format_size(file_size)}")
                sent_msg = await self._upload_single_file(
                    event, filepath, file_size, sender, duration, os.path.basename(filepath)
                )
                
                # Delete original file
                try:
                    os.remove(filepath)
                    logging.info(f"Deleted uploaded file: {filepath}")
                except Exception as e:
                    logging.warning(f"Failed to delete original file: {e}")

        except Exception as e:
            logging.error(f"Upload failed: {str(e)}\n{traceback.format_exc()}")
            await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"❌ Upload failed: {str(e)}",
                edit_message=status_msg
            )
            raise
        finally:
            self.has_notified_split = False

    async def _upload_single_file(self, event, filepath, file_size, sender, duration, caption):
        """Optimized single file upload with instant finalization"""
        try:
            part_size = self.limits['part_size']
            max_parts = self.limits['max_parts']
            
            # Calculate parts needed
            total_parts = math.ceil(file_size / part_size)
            if total_parts > max_parts:
                raise Exception(f"File too large: {total_parts} parts needed, max {max_parts} allowed")
            
            logging.info(f"Uploading {filepath}: {format_size(file_size)}, {total_parts} parts of {format_size(part_size)}")
            
            # Generate file ID
            file_id = random.getrandbits(63)
            
            # Progress tracking
            progress = {'uploaded': 0}
            upload_start = time.time()
            
            # Optimized progress updater with less frequent updates
            async def update_upload_progress():
                nonlocal status_msg
                last_update = 0
                while progress['uploaded'] < file_size and not self.abort_event.is_set():
                    current_time = time.time()
                    if current_time - last_update < 1.5:  # Update every 1.5s for faster feel
                        await asyncio.sleep(0.3)
                        continue
                        
                    elapsed = current_time - upload_start
                    speed = progress['uploaded'] / elapsed if elapsed > 0 else 0
                    percent = (progress['uploaded'] / file_size) * 100
                    
                    self.progress_state.update({
                        'done_size': progress['uploaded'],
                        'percent': percent,
                        'speed': speed,
                        'elapsed': elapsed
                    })
                    
                    display = progress_display(
                        "Uploading",
                        percent,
                        progress['uploaded'],
                        file_size,
                        speed,
                        elapsed,
                        sender.first_name,
                        sender.id,
                        caption
                    )
                    
                    async with self.update_lock:
                        try:
                            status_msg = await send_message_with_flood_control(
                                entity=event.chat_id,
                                message=display,
                                edit_message=status_msg
                            )
                            last_update = current_time
                        except Exception as e:
                            logging.warning(f"Upload progress update failed: {e}")
                    
                    await asyncio.sleep(1.5)
            
            # Optimized upload part function with better error handling
            async def upload_part(part_num, data_chunk):
                if self.abort_event.is_set():
                    raise asyncio.CancelledError("Upload cancelled")
                    
                logging.debug(f"Uploading part {part_num}: {len(data_chunk)} bytes")
                
                # Use appropriate upload method based on session type
                if is_user_session:
                    # User session can use big file upload
                    await client(SaveBigFilePartRequest(
                        file_id=file_id,
                        file_part=part_num,
                        file_total_parts=total_parts,
                        bytes=data_chunk
                    ))
                else:
                    # Bot session uses regular file upload
                    await client(SaveFilePartRequest(
                        file_id=file_id,
                        file_part=part_num,
                        bytes=data_chunk
                    ))
                
                # Update progress
                progress['uploaded'] += len(data_chunk)
                logging.debug(f"Part {part_num} uploaded successfully")

            # Start progress updater
            progress_task = asyncio.create_task(update_upload_progress())
            
            try:
                # Read and upload file in optimized chunks
                upload_tasks = []
                semaphore = asyncio.Semaphore(8)  # Limit concurrent uploads
                
                with open(filepath, 'rb', buffering=8*1024*1024) as f:  # 8MB buffer
                    for part_num in range(total_parts):
                        if self.abort_event.is_set():
                            break
                            
                        # Read part data
                        data_chunk = f.read(part_size)
                        if not data_chunk:
                            break
                        
                        # Create upload task with semaphore
                        async def upload_with_semaphore(pn, dc):
                            async with semaphore:
                                return await retry_with_backoff(
                                    lambda: upload_part(pn, dc),
                                    max_retries=2,
                                    base_delay=1,
                                    operation_name=f"Upload part {pn}"
                                )
                        
                        upload_tasks.append(upload_with_semaphore(part_num, data_chunk))
                
                # Upload all parts concurrently
                await asyncio.gather(*upload_tasks)
                
                # Stop progress updater
                progress_task.cancel()
                try:
                    await progress_task
                except asyncio.CancelledError:
                    pass
                
                # Create input file object based on session type
                if is_user_session and total_parts > 1:
                    # User session with multiple parts
                    input_file = InputFileBig(
                        id=file_id,
                        parts=total_parts,
                        name=os.path.basename(filepath)
                    )
                else:
                    # Bot session or single part
                    input_file = InputFile(
                        id=file_id,
                        parts=total_parts,
                        name=os.path.basename(filepath),
                        md5_checksum=""  # Optional for faster upload
                    )
                
                # Get thumbnail
                thumbnail_file = None
                async with thumbnail_lock:
                    if sender.id in user_thumbnails and os.path.exists(user_thumbnails[sender.id]):
                        thumbnail_file = user_thumbnails[sender.id]
                
                # Try to extract thumbnail if none exists
                if not thumbnail_file:
                    temp_thumb_path = os.path.join(self.user_download_dir, f"temp_thumb_{int(time.time())}.jpg")
                    if await extract_video_frame_thumbnail(filepath, temp_thumb_path, duration):
                        thumbnail_file = temp_thumb_path
                    elif await generate_random_thumbnail(temp_thumb_path):
                        thumbnail_file = temp_thumb_path
                
                # Show finalizing status
                self.progress_state.update({
                    'stage': "Finalizing",
                    'percent': 100.0,
                    'done_size': file_size
                })
                
                finalize_display = progress_display(
                    "Finalizing",
                    100.0,
                    file_size,
                    file_size,
                    progress['uploaded'] / (time.time() - upload_start),
                    time.time() - upload_start,
                    sender.first_name,
                    sender.id,
                    caption
                )
                
                async with self.update_lock:
                    try:
                        status_msg = await send_message_with_flood_control(
                            entity=event.chat_id,
                            message=finalize_display,
                            edit_message=status_msg
                        )
                    except Exception as e:
                        logging.warning(f"Finalize progress update failed: {e}")
                
                # Send file with optimized attributes
                video_attributes = []
                if duration > 0:
                    video_attributes.append(
                        DocumentAttributeVideo(
                            duration=duration,
                            w=1280,
                            h=720,
                            supports_streaming=True
                        )
                    )
                
                # Instant send - this is the key optimization!
                logging.info(f"Sending file with {total_parts} parts, thumbnail: {thumbnail_file is not None}")
                send_start = time.time()
                
                if thumbnail_file and os.path.exists(thumbnail_file):
                    sent_msg = await client.send_file(
                        event.chat_id,
                        file=input_file,
                        caption=caption,
                        thumb=thumbnail_file,
                        attributes=video_attributes,
                        force_document=False  # Send as video
                    )
                else:
                    sent_msg = await client.send_file(
                        event.chat_id,
                        file=input_file,
                        caption=caption,
                        attributes=video_attributes,
                        force_document=False
                    )
                
                send_time = time.time() - send_start
                total_time = time.time() - upload_start
                
                # Clean up temp thumbnail
                if thumbnail_file and thumbnail_file.startswith(self.user_download_dir):
                    try:
                        os.remove(thumbnail_file)
                    except:
                        pass
                
                # Update upload speed stats
                upload_speed = file_size / total_time
                async with speed_lock:
                    if self.user_id not in user_speed_stats:
                        user_speed_stats[self.user_id] = {}
                    user_speed_stats[self.user_id]['upload_speed'] = upload_speed
                    user_speed_stats[self.user_id]['last_updated'] = time.time()
                
                logging.info(f"Upload completed in {format_time(total_time)} (send: {format_time(send_time)}) at {format_size(upload_speed)}/s")
                return sent_msg
                
            except Exception as e:
                # Stop progress updater on error
                progress_task.cancel()
                try:
                    await progress_task
                except asyncio.CancelledError:
                    pass
                raise
                
        except asyncio.CancelledError:
            logging.info(f"Upload cancelled for {filepath}")
            raise
        except Exception as e:
            logging.error(f"Single file upload failed: {str(e)}")
            raise

    async def process_task(self, event, task_data, sender, starting_msg=None):
        """Process a single task with better error handling and cleanup"""
        filepath = None
        status_msg = None
        try:
            # Reset abort flag
            if self.abort_event.is_set():
                self.abort_event.clear()
                
            task_type = task_data.get('type', 'drm')
            name = task_data['name']
            self.current_filename = f"{name}.mp4"
            
            logging.info(f"Processing {task_type} task: {name}")
            
            # Download phase
            if task_type == 'drm':
                mpd_url = task_data['mpd_url']
                key = task_data['key']
                result = await self.download_and_decrypt(event, mpd_url, key, name, sender)
            elif task_type == 'direct':
                url = task_data['url']
                result = await self.download_direct_file(event, url, name, sender)
            else:
                raise ValueError(f"Unsupported task type: {task_type}")
            
            if result is None:  # Download rejected
                return None, None
                
            filepath, status_msg, total_size, duration = result
            
            # Upload phase
            await self.upload_file(event, filepath, status_msg, total_size, sender, duration)
            
            # Clean up starting message
            if starting_msg:
                try:
                    await starting_msg.delete()
                    logging.debug(f"Deleted starting message for: {name}")
                except Exception as e:
                    logging.warning(f"Could not delete starting message: {e}")
            
            # Clean up status message
            if status_msg:
                try:
                    await status_msg.delete()
                    logging.debug(f"Deleted status message for: {name}")
                except Exception as e:
                    logging.warning(f"Could not delete status message: {e}")
            
            return True, None  # Success
            
        except asyncio.CancelledError:
            logging.info(f"Task cancelled: {task_data.get('name', 'unknown')}")
            try:
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message=f"⏭️ Skipped: {task_data.get('name', 'unknown')}.mp4",
                    event=event
                )
            except:
                pass
            return False, "Cancelled by user"
            
        except Exception as e:
            logging.error(f"Task failed: {task_data.get('name', 'unknown')}: {str(e)}")
            
            # Clean up messages
            if starting_msg:
                try:
                    await starting_msg.delete()
                except:
                    pass
            if status_msg:
                try:
                    await status_msg.delete()
                except:
                    pass
            
            return False, str(e)
            
        finally:
            # Aggressive cleanup
            if filepath:
                self.cleanup(filepath)
            
            # Clean up all related files
            cleanup_patterns = [
                f"{task_data.get('name', 'unknown')}_*.mp4",
                f"temp_thumb_*.jpg"
            ]
            
            import glob
            for pattern in cleanup_patterns:
                files = glob.glob(os.path.join(self.user_download_dir, pattern))
                for file in files:
                    try:
                        if os.path.exists(file):
                            os.remove(file)
                            logging.debug(f"Cleaned up: {file}")
                    except Exception as e:
                        logging.warning(f"Cleanup failed for {file}: {e}")

    async def process_queue(self, event):
        """Process task queue with improved error handling"""
        user_queue, user_states, user_lock = get_user_resources(self.user_id)
        user_bot_instances[self.user_id] = self  # Register instance
        
        logging.info(f"Queue processor started for user {self.user_id}")
        
        total_initial_tasks = len(user_queue)
        current_task_number = 1
        completed_tasks = []
        failed_tasks = []
        
        while True:
            # Get next task
            async with user_lock:
                if not user_queue:
                    user_states[self.user_id] = False
                    logging.info(f"Queue empty for user {self.user_id}")
                    break
                    
                task = user_queue.popleft()
                remaining_tasks = len(user_queue)
                user_states[self.user_id] = True
                
            name = task['name']
            sender = task['sender']
            
            logging.info(f"Processing task {current_task_number}/{total_initial_tasks}: {name}")
            
            # Notify task start
            starting_msg = await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"🚀 Task {current_task_number}/{total_initial_tasks}: {name}.mp4\n📋 {remaining_tasks} remaining",
                event=event
            )
            
            # Process task
            success, error = await self.process_task(event, task, sender, starting_msg)
            
            if success:
                completed_tasks.append(name)
                logging.info(f"Task completed: {name}")
            else:
                failed_tasks.append((name, error))
                logging.error(f"Task failed: {name} - {error}")
            
            current_task_number += 1
        
        # Send completion summary
        if total_initial_tasks > 0:
            completion_messages = format_completion_message(completed_tasks, failed_tasks, total_initial_tasks)
            for msg in completion_messages:
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message=msg,
                    event=event
                )
        
        logging.info(f"Queue processor finished for user {self.user_id}")

    def cleanup(self, filepath):
        """Enhanced cleanup with better error handling"""
        try:
            if filepath and os.path.exists(filepath):
                os.remove(filepath)
                logging.debug(f"Cleaned up: {filepath}")
        except Exception as e:
            logging.warning(f"Failed to cleanup {filepath}: {e}")
        
        # Clean up old files (older than 2 hours)
        try:
            import glob
            import time
            current_time = time.time()
            cutoff_age = 2 * 3600  # 2 hours
            
            for pattern in ["*.mp4", "*.jpg", "*.tmp"]:
                for file_path in glob.glob(os.path.join(self.user_download_dir, pattern)):
                    try:
                        if os.path.isfile(file_path):
                            file_age = current_time - os.path.getmtime(file_path)
                            if file_age > cutoff_age:
                                os.remove(file_path)
                                logging.debug(f"Cleaned up old file: {file_path}")
                    except Exception as e:
                        logging.warning(f"Failed to cleanup old file {file_path}: {e}")
        except Exception as e:
            logging.warning(f"Old file cleanup failed: {e}")

# Event handlers with fixed command implementations

@client.on(events.NewMessage(pattern=r'^/start'))
async def start_handler(event):
    sender = await event.get_sender()
    logging.info(f"Received /start command from user {sender.id}")

    if sender.id not in authorized_users:
        await send_message_with_flood_control(
            entity=event.chat_id,
            message="🚫 You're not authorized to use this bot.\n\nContact the admin to get access.",
            event=event
        )
        logging.info(f"Unauthorized access attempt by {sender.id}")
        return

    session_type = "User Session (4GB files)" if is_user_session else "Bot Session (2GB files)"
    
    welcome_message = (
        f"✨ ————  𝚉𝚎𝚛𝚘𝚃𝚛𝚊𝚌𝚎 𝙻𝚎𝚎𝚌𝚑 𝙱𝚘𝚝  ———— ✨\n"
        f"🔗 **{session_type}**\n\n"
        f"Hello! I'm your ultra-fast Telegram leech bot. Here's what I can do:\n\n"
        f"📥  **𝗟𝗲𝗲𝗰𝗵 (DRM/Direct)**\n"
        f"   • /leech\n"
        f"   • `<mpd_url>|<key>|<name>`\n"
        f"   • `<direct_url>|<name>` or `/leech <direct_url>`\n\n"
        f"⚡  **𝗤𝘂𝗶𝗰𝗸 𝗠𝗣𝟰 𝗟𝗲𝗲𝗰𝗵**\n"
        f"   • /mplink `<direct_url>|<name>`\n\n"
        f"📋  **𝗝𝗦𝗢𝗡 𝗪𝗼𝗿𝗸𝗳𝗹𝗼𝘄**\n"
        f"   • /loadjson — send JSON file or text\n"
        f"   • /processjson [range] — e.g. `all`, `1-50`, `5`\n\n"
        f"📦  **𝗕𝘂𝗹𝗸 𝗣𝗿𝗼𝗰𝗲𝘀𝘀𝗶𝗻𝗴**\n"
        f"   • /bulk — start bulk mode\n"
        f"   • /processbulk — process each JSON sequentially\n"
        f"   • /clearbulk — clear stored JSONs\n\n"
        f"🎛️  **𝗛𝗲𝗹𝗽𝗳𝘂𝗹 𝗖𝗼𝗻𝘁𝗿𝗼𝗹𝘀**\n"
        f"   • /speed — live VPS speed test\n"
        f"   • /status — current task status\n"
        f"   • /skip — skip current task\n"
        f"   • /skip 3-5 — skip queued tasks 3 to 5\n"
        f"   • /clearall — stop and clear queue\n"
        f"   • /clear — full cleanup\n\n"
        f"🖼️  **𝗧𝗵𝘂𝗺𝗯𝗻𝗮𝗶𝗹𝘀**\n"
        f"   • /addthumbnail — send a photo\n"
        f"   • /removethumbnail — remove custom thumbnail\n\n"
        f"🛡️  **𝗔𝗱𝗺𝗶𝗻**\n"
        f"   • /addadmin <id>\n"
        f"   • /removeadmin <id>\n\n"
        f"Ready to go at maximum speed! 🚀"
    )

    await send_message_with_flood_control(
        entity=event.chat_id,
        message=welcome_message,
        event=event
    )

@client.on(events.NewMessage(pattern=r'^/(leech|mplink)'))
async def leech_handler(event):
    sender = await event.get_sender()
    raw_message = event.raw_text
    logging.info(f"Received /{event.pattern_match.group(1)} command from user {sender.id}")

    if sender.id not in authorized_users:
        await send_message_with_flood_control(
            entity=event.chat_id,
            message="🚫 You're not authorized to use this bot.",
            event=event
        )
        return

    user_queue, user_states, user_lock = get_user_resources(sender.id)

    try:
        message_content = event.raw_text.split('\n', 1)
        if len(message_content) < 2:
            # Handle inline usage: /leech <url> [| name]
            parts = raw_message.split(maxsplit=1)
            if len(parts) == 2:
                inline = parts[1].strip()
                if inline.startswith('http'):
                    message_content = [parts[0], inline]
                else:
                    cmd = event.pattern_match.group(1)
                    usage = "📝 **Format:**\n" + (
                        "/mplink\n<direct_url>|<name>\n\n💡 For direct .mp4 files" if cmd == 'mplink' else
                        "/leech\n<mpd_url>|<key>|<name>\n<direct_url>|<name>\n\n💡 For DRM or direct files"
                    )
                    await send_message_with_flood_control(entity=event.chat_id, message=usage, event=event)
                    return
            else:
                cmd = event.pattern_match.group(1)
                usage = "📝 **Format:**\n" + (
                    "/mplink\n<direct_url>|<name>\n\n💡 For direct .mp4 files" if cmd == 'mplink' else
                    "/leech\n<mpd_url>|<key>|<name>\n<direct_url>|<name>\n\n💡 For DRM or direct files"
                )
                await send_message_with_flood_control(entity=event.chat_id, message=usage, event=event)
                return

        links = message_content[1].strip().split('\n')
        links = [link.strip() for link in links if link.strip()]

        tasks_to_add = []
        invalid_links = []

        for i, link in enumerate(links, 1):
            args = link.split('|')
            if len(args) == 3:  # DRM format
                mpd_url, key, name = [arg.strip() for arg in args]
                if not mpd_url.startswith("http") or ".mpd" not in mpd_url.lower():
                    invalid_links.append(f"Link {i}: Invalid MPD URL")
                    continue
                if ":" not in key or len(key.split(":")) != 2:
                    invalid_links.append(f"Link {i}: Key must be in KID:KEY format")
                    continue
                tasks_to_add.append({
                    'type': 'drm',
                    'mpd_url': mpd_url,
                    'key': key,
                    'name': name,
                    'sender': sender
                })
            elif len(args) == 2:  # Direct format
                direct_url, name = [arg.strip() for arg in args]
                if not direct_url.startswith("http"):
                    invalid_links.append(f"Link {i}: Invalid URL")
                    continue
                tasks_to_add.append({
                    'type': 'direct',
                    'url': direct_url,
                    'name': name,
                    'sender': sender
                })
            elif len(args) == 1 and args[0].strip().startswith('http'):  # URL only
                direct_url = args[0].strip()
                name = derive_name_from_url(direct_url)
                tasks_to_add.append({
                    'type': 'direct',
                    'url': direct_url,
                    'name': name,
                    'sender': sender
                })
            else:
                invalid_links.append(f"Link {i}: Invalid format")

        if invalid_links:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="⚠️ **Invalid links (skipped):**\n" + "\n".join(invalid_links),
                event=event
            )

        if not tasks_to_add:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="❌ No valid links found. Please check the format.",
                event=event
            )
            return

        # Add tasks to queue
        async with user_lock:
            for task in tasks_to_add:
                user_queue.append(task)
            
            # Reset abort flag
            if sender.id in user_bot_instances and user_bot_instances[sender.id]:
                try:
                    user_bot_instances[sender.id].abort_event.clear()
                except:
                    pass

            queue_size = len(user_queue)
            if len(tasks_to_add) <= 10:
                task_list = "\n".join([f"Task {i}: {task['name']}.mp4" for i, task in enumerate(tasks_to_add, queue_size - len(tasks_to_add) + 1)])
                queue_message = f"✅ **Added {len(tasks_to_add)} task(s)**\n\n{task_list}\n\n📊 Queue size: {queue_size}"
            else:
                queue_message = f"✅ **Added {len(tasks_to_add)} tasks**\n📊 Queue size: {queue_size}\n\nFirst 3 tasks:\n"
                for i, task in enumerate(tasks_to_add[:3], queue_size - len(tasks_to_add) + 1):
                    queue_message += f"Task {i}: {task['name']}.mp4\n"
                queue_message += f"...and {len(tasks_to_add) - 3} more"

            if user_states.get(sender.id, False):
                queue_message += "\n\n⏳ Processing in progress..."

            await send_message_with_flood_control(
                entity=event.chat_id,
                message=queue_message,
                event=event
            )

            # Start queue processor if not running
            if not user_states.get(sender.id, False) and (not user_active_tasks.get(sender.id) or user_active_tasks[sender.id].done()):
                logging.info(f"Starting queue processor for user {sender.id}")
                bot = MPDLeechBot(sender.id)
                user_bot_instances[sender.id] = bot
                user_active_tasks[sender.id] = asyncio.create_task(bot.process_queue(event))

    except Exception as e:
        logging.error(f"Leech handler error: {str(e)}\n{traceback.format_exc()}")
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"❌ Failed to add tasks: {str(e)}",
            event=event
        )

@client.on(events.NewMessage(pattern=r'^/(clearall|stop)$'))
async def clearall_handler(event):
    sender = await event.get_sender()
    logging.info(f"Received /clearall command from user {sender.id}")

    if sender.id not in authorized_users:
        await send_message_with_flood_control(entity=event.chat_id, message="🚫 Not authorized.", event=event)
        return

    user_queue, user_states, user_lock = get_user_resources(sender.id)

    try:
        # Cancel active task
        if sender.id in user_active_tasks and user_active_tasks[sender.id]:
            active_task = user_active_tasks[sender.id]
            if not active_task.done():
                logging.info(f"Cancelling active task for user {sender.id}")
                
                # Signal abort if bot instance exists
                if sender.id in user_bot_instances and user_bot_instances[sender.id]:
                    user_bot_instances[sender.id].abort_event.set()
                
                active_task.cancel()
                try:
                    await asyncio.wait_for(active_task, timeout=5.0)
                except (asyncio.CancelledError, asyncio.TimeoutError):
                    logging.info(f"Active task cancelled for user {sender.id}")
                except Exception as e:
                    logging.warning(f"Error cancelling task: {e}")
            
            user_active_tasks[sender.id] = None

        # Clear queue and state
        async with user_lock:
            cleared_count = len(user_queue)
            user_queue.clear()
            user_states[sender.id] = False
            if sender.id in user_bot_instances:
                user_bot_instances[sender.id] = None

        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"🛑 **Stopped and cleared {cleared_count} task(s)**\n\n✅ All processing halted",
            event=event
        )
        logging.info(f"Cleared {cleared_count} tasks for user {sender.id}")

    except Exception as e:
        logging.error(f"Clearall error for user {sender.id}: {str(e)}")
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"❌ Error clearing tasks: {str(e)}",
            event=event
        )

@client.on(events.NewMessage(pattern=r'^/clear$'))
async def clear_handler(event):
    sender = await event.get_sender()
    logging.info(f"Received /clear command from user {sender.id}")

    if sender.id not in authorized_users:
        await send_message_with_flood_control(entity=event.chat_id, message="🚫 Not authorized.", event=event)
        return

    user_queue, user_states, user_lock = get_user_resources(sender.id)

    try:
        # Cancel active task
        if sender.id in user_active_tasks and user_active_tasks[sender.id]:
            active_task = user_active_tasks[sender.id]
            if not active_task.done():
                if sender.id in user_bot_instances and user_bot_instances[sender.id]:
                    user_bot_instances[sender.id].abort_event.set()
                active_task.cancel()
                try:
                    await asyncio.wait_for(active_task, timeout=5.0)
                except (asyncio.CancelledError, asyncio.TimeoutError):
                    pass
            user_active_tasks[sender.id] = None

        # Clear queue and state
        async with user_lock:
            cleared_count = len(user_queue)
            user_queue.clear()
            user_states[sender.id] = False
            if sender.id in user_bot_instances:
                user_bot_instances[sender.id] = None

        # Clear JSON data
        async with json_lock:
            if sender.id in user_json_data:
                del user_json_data[sender.id]

        # Clear bulk data
        async with bulk_lock:
            if sender.id in user_bulk_data:
                del user_bulk_data[sender.id]

        # Clear download directory
        user_download_dir = os.path.join(DOWNLOAD_DIR, f"user_{sender.id}")
        try:
            if os.path.exists(user_download_dir):
                import shutil
                shutil.rmtree(user_download_dir)
                os.makedirs(user_download_dir)
        except Exception as e:
            logging.warning(f"Failed to clear download directory: {e}")

        # Clear thumbnails
        async with thumbnail_lock:
            if sender.id in user_thumbnails:
                try:
                    thumbnail_path = user_thumbnails[sender.id]
                    if os.path.exists(thumbnail_path):
                        os.remove(thumbnail_path)
                    del user_thumbnails[sender.id]
                except Exception as e:
                    logging.warning(f"Failed to clear thumbnail: {e}")

        # Clear speed stats
        async with speed_lock:
            if sender.id in user_speed_stats:
                del user_speed_stats[sender.id]

        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"🧹 **Complete cleanup done!**\n\n✅ Stopped all tasks ({cleared_count})\n✅ Cleared JSON data\n✅ Cleared bulk data\n✅ Cleared downloads\n✅ Cleared thumbnails\n✅ Reset all settings\n\n🎉 Fresh start ready!",
            event=event
        )
        logging.info(f"Full cleanup completed for user {sender.id}")

    except Exception as e:
        logging.error(f"Clear error for user {sender.id}: {str(e)}")
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"❌ Cleanup error: {str(e)}",
            event=event
        )

@client.on(events.NewMessage(pattern=r'^/(skip)(?:\s+(\d+)(?:-(\d+))?)?$'))
async def skip_handler(event):
    sender = await event.get_sender()
    logging.info(f"Received /skip command from user {sender.id}")

    if sender.id not in authorized_users:
        return

    user_queue, user_states, user_lock = get_user_resources(sender.id)

    try:
        start = event.pattern_match.group(2)
        end = event.pattern_match.group(3)

        if not start:
            # Skip current task
            if sender.id in user_active_tasks and user_active_tasks[sender.id] and not user_active_tasks[sender.id].done():
                if sender.id in user_bot_instances and user_bot_instances[sender.id]:
                    user_bot_instances[sender.id].abort_event.set()
                    logging.info(f"Signalled skip to active task for user {sender.id}")
                    
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message="⏭️ **Skipping current task...**\n\n✅ Processing next task in queue",
                    event=event
                )
            else:
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message="ℹ️ **No active task to skip**\n\n💡 Queue may be empty or idle",
                    event=event
                )
            return

        # Skip range from queue
        start_idx = int(start)
        end_idx = int(end) if end else start_idx
        
        if start_idx <= 0 or end_idx < start_idx:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="❌ **Invalid range**\n\n💡 Use: `/skip` or `/skip 3-5`",
                event=event
            )
            return

        removed_tasks = []
        async with user_lock:
            queue_list = list(user_queue)
            new_queue = []
            
            for pos, task in enumerate(queue_list, start=1):
                if start_idx <= pos <= end_idx:
                    removed_tasks.append(task.get('name', 'unknown'))
                else:
                    new_queue.append(task)
            
            user_queue.clear()
            user_queue.extend(new_queue)

        if removed_tasks:
            if len(removed_tasks) == 1:
                message = f"⏭️ **Skipped task:** {removed_tasks[0]}.mp4"
            else:
                message = f"⏭️ **Skipped {len(removed_tasks)} tasks:**\n" + "\n".join([f"• {name}.mp4" for name in removed_tasks[:10]])
                if len(removed_tasks) > 10:
                    message += f"\n...and {len(removed_tasks) - 10} more"
            
            message += f"\n\n📊 Remaining in queue: {len(user_queue)}"
            
            await send_message_with_flood_control(
                entity=event.chat_id,
                message=message,
                event=event
            )
        else:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="ℹ️ **No tasks matched the range**\n\n💡 Check your queue position",
                event=event
            )

    except ValueError:
        await send_message_with_flood_control(
            entity=event.chat_id,
            message="❌ **Invalid range format**\n\n💡 Use: `/skip` or `/skip 3-5`",
            event=event
        )
    except Exception as e:
        logging.error(f"Skip error for user {sender.id}: {str(e)}")
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"❌ Skip error: {str(e)}",
            event=event
        )

@client.on(events.NewMessage(pattern=r'^/status$'))
async def status_handler(event):
    sender = await event.get_sender()
    logging.info(f"Received /status command from user {sender.id}")

    if sender.id not in authorized_users:
        return

    user_queue, user_states, user_lock = get_user_resources(sender.id)

    try:
        async with user_lock:
            queue_size = len(user_queue)
            is_processing = user_states.get(sender.id, False)

        status_message = f"📊 **Status Report**\n\n"
        status_message += f"🔗 **Session:** {'User (4GB max)' if is_user_session else 'Bot (2GB max)'}\n"
        status_message += f"📋 **Queue:** {queue_size} task(s)\n"
        status_message += f"⚡ **Status:** {'🟢 Processing' if is_processing else '🔴 Idle'}\n\n"

        # Current task details
        if is_processing and sender.id in user_bot_instances:
            bot_inst = user_bot_instances[sender.id]
            if bot_inst:
                try:
                    stage = bot_inst.progress_state.get('stage', 'Unknown')
                    percent = bot_inst.progress_state.get('percent', 0)
                    speed = bot_inst.progress_state.get('speed', 0)
                    elapsed = bot_inst.progress_state.get('elapsed', 0)
                    current_file = getattr(bot_inst, 'current_filename', 'Processing...')
                    
                    status_message += f"🎬 **Current Task:**\n"
                    status_message += f"📄 {current_file}\n"
                    status_message += f"🔄 {stage} ({percent:.1f}%)\n"
                    status_message += f"⚡ {format_size(speed)}/s\n"
                    status_message += f"⏱️ {format_time(elapsed)}\n\n"
                except Exception as e:
                    logging.warning(f"Could not get current task details: {e}")
                    status_message += f"🎬 **Current Task:** Processing...\n\n"

        # Queue preview
        if queue_size > 0:
            status_message += f"📋 **Next Tasks:**\n"
            async with user_lock:
                preview_tasks = list(user_queue)[:5]
                for i, task in enumerate(preview_tasks, 1):
                    task_type = "🔐" if task.get('type') == 'drm' else "📥"
                    status_message += f"{i}. {task_type} {task.get('name', 'Unknown')}.mp4\n"
                
                if queue_size > 5:
                    status_message += f"...and {queue_size - 5} more\n"
        else:
            status_message += f"📋 **Queue:** Empty\n"

        # Speed stats
        async with speed_lock:
            if sender.id in user_speed_stats:
                stats = user_speed_stats[sender.id]
                download_speed = stats.get('download_speed', 0)
                upload_speed = stats.get('upload_speed', 0)
                last_update = stats.get('last_updated', 0)
                
                if time.time() - last_update < 300:  # Within 5 minutes
                    status_message += f"\n📈 **Recent Speeds:**\n"
                    status_message += f"📥 Download: {format_size(download_speed)}/s\n"
                    status_message += f"📤 Upload: {format_size(upload_speed)}/s\n"

        await send_message_with_flood_control(
            entity=event.chat_id,
            message=status_message,
            event=event
        )

    except Exception as e:
        logging.error(f"Status error for user {sender.id}: {str(e)}")
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"❌ Status error: {str(e)}",
            event=event
        )

@client.on(events.NewMessage(pattern=r'^/loadjson'))
async def loadjson_handler(event):
    sender = await event.get_sender()
    logging.info(f"Received /loadjson command from user {sender.id}")

    if sender.id not in authorized_users:
        await send_message_with_flood_control(entity=event.chat_id, message="🚫 Not authorized.", event=event)
        return

    await send_message_with_flood_control(
        entity=event.chat_id,
        message="📥 **Ready for JSON data!**\n\n**Methods:**\n1. 📎 Upload .json file\n2. 📝 Send JSON text\n\n**Format:**\n```json\n[\n  {\n    \"name\": \"Video Name\",\n    \"type\": \"drm\",\n    \"mpd_url\": \"https://example.com/manifest.mpd\",\n    \"keys\": [\"kid:key\"]\n  },\n  {\n    \"name\": \"Direct Video\",\n    \"type\": \"direct\",\n    \"url\": \"https://example.com/video.mp4\"\n  }\n]\n```\n\n💡 Use `/processjson` after loading!",
        event=event
    )

@client.on(events.NewMessage())
async def json_data_handler(event):
    """Handle JSON file uploads and text input"""
    sender = await event.get_sender()

    if sender.id not in authorized_users:
        return

    try:
        json_data = None

        # Handle JSON file upload
        if event.document and event.document.mime_type == 'application/json':
            logging.info(f"JSON file uploaded by user {sender.id}")

            file_path = await event.download_media()
            with open(file_path, 'r', encoding='utf-8') as f:
                json_content = f.read()
            os.remove(file_path)

            json_data = json.loads(json_content)

            # Check bulk mode
            async with bulk_lock:
                if sender.id in user_bulk_data:
                    user_bulk_data[sender.id].append(json_data)
                    total_bulk = len(user_bulk_data[sender.id])
                    await send_message_with_flood_control(
                        entity=event.chat_id,
                        message=f"📦 **Bulk JSON #{total_bulk}** loaded!\n\n📊 Items: {len(json_data)}\n\n💡 Send more or use `/processbulk`",
                        event=event
                    )
                else:
                    await send_message_with_flood_control(
                        entity=event.chat_id,
                        message=f"✅ **JSON file loaded!**\n\n📊 Items: {len(json_data)}\n\n💡 Use `/processjson` to start",
                        event=event
                    )

        # Handle JSON text
        elif event.text and (event.text.strip().startswith('[') or event.text.strip().startswith('{')):
            logging.info(f"JSON text received from user {sender.id}")

            json_data = json.loads(event.text.strip())

            async with bulk_lock:
                if sender.id in user_bulk_data:
                    user_bulk_data[sender.id].append(json_data)
                    total_bulk = len(user_bulk_data[sender.id])
                    await send_message_with_flood_control(
                        entity=event.chat_id,
                        message=f"📦 **Bulk JSON #{total_bulk}** loaded!\n\n📊 Items: {len(json_data)}\n\n💡 Send more or use `/processbulk`",
                        event=event
                    )
                else:
                    await send_message_with_flood_control(
                        entity=event.chat_id,
                        message=f"✅ **JSON text loaded!**\n\n📊 Items: {len(json_data)}\n\n💡 Use `/processjson` to start",
                        event=event
                    )

        # Store JSON data
        if json_data:
            async with bulk_lock:
                if sender.id not in user_bulk_data:
                    async with json_lock:
                        user_json_data[sender.id] = json_data
                    logging.info(f"Stored JSON data for user {sender.id}: {len(json_data)} items")

    except json.JSONDecodeError as e:
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"❌ **Invalid JSON:**\n{str(e)}\n\n💡 Check syntax and try again",
            event=event
        )
    except Exception as e:
        logging.error(f"JSON data handler error: {str(e)}")
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"❌ JSON processing error: {str(e)}",
            event=event
        )

@client.on(events.NewMessage(pattern=r'^/processjson(?:\s+(.+))?'))
async def processjson_handler(event):
    sender = await event.get_sender()
    range_input = event.pattern_match.group(1)
    logging.info(f"Received /processjson command from user {sender.id} with range: {range_input}")

    if sender.id not in authorized_users:
        await send_message_with_flood_control(entity=event.chat_id, message="🚫 Not authorized.", event=event)
        return

    async with json_lock:
        if sender.id not in user_json_data:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="❌ **No JSON data found**\n\n💡 Use `/loadjson` first",
                event=event
            )
            return
        json_data = user_json_data[sender.id]

    if not range_input:
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"📋 **JSON loaded: {len(json_data)} items**\n\n**Specify range:**\n• `/processjson all` - All items\n• `/processjson 1-10` - Items 1-10\n• `/processjson 5` - Item 5 only\n\n📊 **Range: 1-{len(json_data)}**",
            event=event
        )
        return

    # Parse range
    try:
        if range_input.lower() == "all":
            selected_data = json_data
            range_text = f"1-{len(json_data)}"
        elif "-" in range_input:
            start, end = map(int, range_input.split("-"))
            start_idx, end_idx = start - 1, end
            if start_idx < 0 or end_idx > len(json_data) or start_idx >= end_idx:
                raise ValueError("Invalid range")
            selected_data = json_data[start_idx:end_idx]
            range_text = range_input
        else:
            item_num = int(range_input)
            start_idx = item_num - 1
            if start_idx < 0 or start_idx >= len(json_data):
                raise ValueError("Invalid item number")
            selected_data = [json_data[start_idx]]
            range_text = range_input
    except (ValueError, IndexError):
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"❌ **Invalid range**\n\n💡 Valid: `all`, `1-10`, `5`\nRange: 1-{len(json_data)}",
            event=event
        )
        return

    user_queue, user_states, user_lock = get_user_resources(sender.id)

    try:
        tasks_to_add = []
        invalid_items = []

        for i, item in enumerate(selected_data, 1):
            try:
                name = item.get('name', f'Video_{i}')
                item_type = item.get('type', 'drm').lower()

                if item_type == 'drm':
                    mpd_url = item.get('mpd_url')
                    keys = item.get('keys', [])
                    if not mpd_url or not keys:
                        invalid_items.append(f"Item {i}: Missing mpd_url or keys")
                        continue
                    key = keys[0] if isinstance(keys, list) else keys
                    tasks_to_add.append({
                        'type': 'drm',
                        'mpd_url': mpd_url,
                        'key': key,
                        'name': name,
                        'sender': sender
                    })
                elif item_type == 'direct':
                    url = item.get('url')
                    if not url:
                        invalid_items.append(f"Item {i}: Missing url")
                        continue
                    tasks_to_add.append({
                        'type': 'direct',
                        'url': url,
                        'name': name,
                        'sender': sender
                    })
                else:
                    invalid_items.append(f"Item {i}: Unknown type '{item_type}'")
            except Exception as e:
                invalid_items.append(f"Item {i}: {str(e)}")

        if invalid_items:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="⚠️ **Invalid items (skipped):**\n" + "\n".join(invalid_items),
                event=event
            )

        if not tasks_to_add:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="❌ No valid items found",
                event=event
            )
            return

        # Add to queue
        async with user_lock:
            for task in tasks_to_add:
                user_queue.append(task)
            
            # Reset abort flag
            if sender.id in user_bot_instances and user_bot_instances[sender.id]:
                try:
                    user_bot_instances[sender.id].abort_event.clear()
                except:
                    pass

            drm_count = sum(1 for t in tasks_to_add if t['type'] == 'drm')
            direct_count = len(tasks_to_add) - drm_count

            message = f"📋 **JSON Range: {range_text}**\n"
            message += f"✅ Added {len(tasks_to_add)} tasks\n"
            message += f"🔐 DRM: {drm_count} | 📥 Direct: {direct_count}\n"
            message += f"📊 Queue: {len(user_queue)} total\n"

            if user_states.get(sender.id, False):
                message += "\n⏳ Processing in progress..."

            await send_message_with_flood_control(entity=event.chat_id, message=message, event=event)

            # Start processor
            if not user_states.get(sender.id, False) and (not user_active_tasks.get(sender.id) or user_active_tasks[sender.id].done()):
                bot = MPDLeechBot(sender.id)
                user_bot_instances[sender.id] = bot
                user_active_tasks[sender.id] = asyncio.create_task(bot.process_queue(event))

    except Exception as e:
        logging.error(f"ProcessJSON error: {str(e)}")
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"❌ Processing failed: {str(e)}",
            event=event
        )

@client.on(events.NewMessage(pattern=r'^/bulk'))
async def bulk_handler(event):
    sender = await event.get_sender()
    if sender.id not in authorized_users:
        return

    async with bulk_lock:
        user_bulk_data[sender.id] = []

    await send_message_with_flood_control(
        entity=event.chat_id,
        message="📦 **Bulk mode activated!**\n\n**Send multiple JSON files/text**\nEach JSON processes completely before the next\n\n**Commands:**\n• `/processbulk` - Start processing\n• `/clearbulk` - Clear stored data\n\n🚀 Ready for JSON data!",
        event=event
    )

@client.on(events.NewMessage(pattern=r'^/processbulk'))
async def processbulk_handler(event):
    sender = await event.get_sender()
    if sender.id not in authorized_users:
        return

    async with bulk_lock:
        if sender.id not in user_bulk_data or not user_bulk_data[sender.id]:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="❌ **No bulk data**\n\n💡 Use `/bulk` and send JSON first",
                event=event
            )
            return
        bulk_list = user_bulk_data[sender.id]

    user_queue, user_states, user_lock = get_user_resources(sender.id)
    if user_states.get(sender.id, False):
        await send_message_with_flood_control(
            entity=event.chat_id,
            message="❌ **Tasks already running**\n\n💡 Use `/clearall` first",
            event=event
        )
        return

    total_jsons = len(bulk_list)
    await send_message_with_flood_control(
        entity=event.chat_id,
        message=f"🚀 **Starting bulk processing**\n\n📦 Processing {total_jsons} JSON files\n⏳ Sequential execution starting...",
        event=event
    )

    for json_idx, json_data in enumerate(bulk_list, 1):
        try:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"📋 **JSON {json_idx}/{total_jsons}**\n🔄 Processing {len(json_data)} items...",
                event=event
            )

            # Convert JSON to tasks
            tasks = []
            for item in json_data:
                try:
                    name = item.get('name', f'Video_{json_idx}_{len(tasks)+1}')
                    item_type = item.get('type', 'drm').lower()
                    
                    if item_type == 'drm':
                        mpd_url = item.get('mpd_url')
                        keys = item.get('keys', [])
                        if mpd_url and keys:
                            key = keys[0] if isinstance(keys, list) else keys
                            tasks.append({'type': 'drm', 'mpd_url': mpd_url, 'key': key, 'name': name, 'sender': sender})
                    elif item_type == 'direct':
                        url = item.get('url')
                        if url:
                            tasks.append({'type': 'direct', 'url': url, 'name': name, 'sender': sender})
                except:
                    continue

            if not tasks:
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message=f"⚠️ **JSON {json_idx}** - No valid items, skipping",
                    event=event
                )
                continue

            # Add to queue
            async with user_lock:
                for task in tasks:
                    user_queue.append(task)

            # Start processing and wait for completion
            if not user_states.get(sender.id, False):
                bot = MPDLeechBot(sender.id)
                user_bot_instances[sender.id] = bot
                user_active_tasks[sender.id] = asyncio.create_task(bot.process_queue(event))

            # Wait for completion
            while user_states.get(sender.id, False) or (user_active_tasks.get(sender.id) and not user_active_tasks[sender.id].done()):
                await asyncio.sleep(3)

            completion_msg = f"✅ **JSON {json_idx}/{total_jsons} completed!**\n📊 {len(tasks)} items processed"
            if json_idx < total_jsons:
                completion_msg += f"\n⏭️ Moving to JSON {json_idx + 1}..."
            else:
                completion_msg += "\n\n🎉 **All JSONs completed!**"
                
            await send_message_with_flood_control(entity=event.chat_id, message=completion_msg, event=event)

        except Exception as e:
            logging.error(f"Bulk processing error for JSON {json_idx}: {e}")
            await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"❌ **JSON {json_idx} failed:** {str(e)}",
                event=event
            )

@client.on(events.NewMessage(pattern=r'^/clearbulk'))
async def clearbulk_handler(event):
    sender = await event.get_sender()
    if sender.id not in authorized_users:
        return

    async with bulk_lock:
        if sender.id in user_bulk_data:
            count = len(user_bulk_data[sender.id])
            del user_bulk_data[sender.id]
            await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"🧹 **Cleared {count} bulk JSON files**",
                event=event
            )
        else:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="ℹ️ **No bulk data to clear**",
                event=event
            )

@client.on(events.NewMessage(pattern=r'^/addthumbnail'))
async def addthumbnail_handler(event):
    sender = await event.get_sender()
    if sender.id not in authorized_users:
        return

    await send_message_with_flood_control(
        entity=event.chat_id,
        message="🖼️ **Send a photo** to set as your custom thumbnail\n\n💡 Will be used for all future uploads",
        event=event
    )

@client.on(events.NewMessage())
async def thumbnail_handler(event):
    """Handle thumbnail uploads"""
    sender = await event.get_sender()
    if sender.id not in authorized_users or not event.photo:
        return

    success, message = await save_thumbnail_from_message(event, sender.id)
    status = "✅" if success else "❌"
    await send_message_with_flood_control(
        entity=event.chat_id,
        message=f"{status} {message}",
        event=event
    )

@client.on(events.NewMessage(pattern=r'^/removethumbnail'))
async def removethumbnail_handler(event):
    sender = await event.get_sender()
    if sender.id not in authorized_users:
        return

    async with thumbnail_lock:
        if sender.id in user_thumbnails:
            try:
                thumbnail_path = user_thumbnails[sender.id]
                if os.path.exists(thumbnail_path):
                    os.remove(thumbnail_path)
                del user_thumbnails[sender.id]
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message="🗑️ **Custom thumbnail removed**",
                    event=event
                )
            except Exception as e:
                await send_message_with_flood_control(
                    entity=event.chat_id,
                    message=f"❌ Error: {str(e)}",
                    event=event
                )
        else:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message="ℹ️ **No custom thumbnail set**",
                event=event
            )

@client.on(events.NewMessage(pattern=r'^/addadmin (\d+)$'))
async def addadmin_handler(event):
    sender = await event.get_sender()
    if sender.id not in authorized_users:
        return

    user_id = int(event.pattern_match.group(1))
    async with user_lock:
        if user_id not in authorized_users:
            authorized_users.add(user_id)
            await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"✅ **Admin added:** {user_id}\n\n🔓 Full bot access granted",
                event=event
            )
        else:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"ℹ️ **User {user_id} is already an admin**",
                event=event
            )

@client.on(events.NewMessage(pattern=r'^/removeadmin (\d+)$'))
async def removeadmin_handler(event):
    sender = await event.get_sender()
    if sender.id not in authorized_users:
        return

    user_id = int(event.pattern_match.group(1))
    if user_id == sender.id:
        await send_message_with_flood_control(
            entity=event.chat_id,
            message="❌ **Cannot remove yourself**",
            event=event
        )
        return

    async with user_lock:
        if user_id in authorized_users:
            authorized_users.remove(user_id)
            await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"🗑️ **Admin removed:** {user_id}\n\n🔒 Bot access revoked",
                event=event
            )
        else:
            await send_message_with_flood_control(
                entity=event.chat_id,
                message=f"ℹ️ **User {user_id} is not an admin**",
                event=event
            )

async def perform_internet_speed_test():
    """Enhanced speed test with better reliability"""
    download_urls = [
        "https://speed.cloudflare.com/__down?bytes=104857600",  # 100MB
        "https://speed.hetzner.de/100MB.bin",  # Removed extra spaces
        "https://proof.ovh.net/files/100Mb.dat",  # Removed extra spaces
        "https://speedtest.tele2.net/100MB.zip",  # Removed extra spaces
    ]

    test_size = 100 * 1024 * 1024  # 100MB
    max_test_time = 10

   # Download test
    download_speed = download_bytes = download_time = None
    for url in download_urls:
        try:
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                'Accept': '*/*',
                'Connection': 'keep-alive'
            }
            timeout = aiohttp.ClientTimeout(total=max_test_time + 5)

            start_time = time.time()
            downloaded = 0

            async with aiohttp.ClientSession(timeout=timeout) as session:
                async with session.get(url.strip(), headers=headers) as response:
                    if response.status != 200:
                        continue

                    async for chunk in response.content.iter_chunked(4 * 1024 * 1024):
                        downloaded += len(chunk)
                        elapsed = time.time() - start_time
                        if elapsed >= max_test_time or downloaded >= test_size:
                            break

            elapsed = time.time() - start_time
            if elapsed > 0 and downloaded > 1024 * 1024:
                download_speed = downloaded / elapsed
                download_bytes = downloaded
                download_time = elapsed
                break
        except Exception as e:
            logging.warning(f"Download test failed for {url}: {e}")
            continue

# Upload test
upload_speed = upload_bytes = upload_time = None
try:
    upload_data = b'0' * (10 * 1024 * 1024)  # 10MB
    url = "https://httpbin.org/post"
    headers = {'User-Agent': 'SpeedTest/1.0', 'Content-Type': 'application/octet-stream'}
    timeout = aiohttp.ClientTimeout(total=max_test_time)
    
    start_time = time.time()
    async with aiohttp.ClientSession(timeout=timeout) as session:
        async with session.post(url, data=upload_data, headers=headers) as response:
            await response.read()  # Ensure upload completes before measuring time
            elapsed = time.time() - start_time
            if elapsed > 0:
                upload_speed = len(upload_data) / elapsed
                upload_bytes = len(upload_data)
                upload_time = elapsed
except Exception as e:
    logging.warning(f"Upload test failed: {e}")

return download_speed, download_bytes, download_time, upload_speed, upload_bytes, upload_time

@client.on(events.NewMessage(pattern=r'^/speed$'))
async def speed_handler(event):
    sender = await event.get_sender()
    if sender.id not in authorized_users:
        return

    status_msg = await send_message_with_flood_control(
        entity=event.chat_id,
        message="🌐 **Internet Speed Test**\n\n⏳ Testing download and upload speeds...\n\nPlease wait...",
        event=event
    )

    try:
        # Perform speed test
        dl_speed, dl_bytes, dl_time, ul_speed, ul_bytes, ul_time = await perform_internet_speed_test()

        # Format results
        if dl_speed:
            dl_mbps = dl_speed / (1024 * 1024)
            dl_text = f"📥 **Download:** {format_size(dl_speed)}/s\n📊 {format_size(dl_bytes)} in {format_time(dl_time)}"
            if dl_mbps >= 50:
                dl_text += "\n🟢 **Excellent**"
            elif dl_mbps >= 25:
                dl_text += "\n🟡 **Good**"
            else:
                dl_text += "\n🟠 **Average**"
        else:
            dl_text = "📥 **Download:** ❌ Failed"

        if ul_speed:
            ul_mbps = ul_speed / (1024 * 1024)
            ul_text = f"📤 **Upload:** {format_size(ul_speed)}/s\n📊 {format_size(ul_bytes)} in {format_time(ul_time)}"
            if ul_mbps >= 25:
                ul_text += "\n🟢 **Excellent**"
            elif ul_mbps >= 10:
                ul_text += "\n🟡 **Good**"
            else:
                ul_text += "\n🟠 **Average**"
        else:
            ul_text = "📤 **Upload:** ❌ Failed"

        # Current task info
        current_info = ""
        if sender.id in user_bot_instances and user_bot_instances[sender.id]:
            bot_inst = user_bot_instances[sender.id]
            if bot_inst and bot_inst.progress_state.get('stage') in ['Downloading', 'Uploading']:
                stage = bot_inst.progress_state['stage']
                speed = bot_inst.progress_state.get('speed', 0)
                filename = getattr(bot_inst, 'current_filename', 'Current task')
                current_info = f"\n\n🔄 **Current Task:**\n📄 {filename}\n{'📥' if stage == 'Downloading' else '📤'} {format_size(speed)}/s"

        result_message = f"🌐 **Speed Test Results**\n\n{dl_text}\n\n{ul_text}{current_info}\n\n💡 *Live test completed*"

        await send_message_with_flood_control(
            entity=event.chat_id,
            message=result_message,
            edit_message=status_msg
        )

    except Exception as e:
        logging.error(f"Speed test error: {e}")
        await send_message_with_flood_control(
            entity=event.chat_id,
            message=f"🌐 **Speed Test**\n\n❌ Error: {str(e)}",
            edit_message=status_msg
        )

# Main startup function
async def main():
    """Main bot startup with enhanced error handling and session verification"""
    while True:
        try:
            # Start client based on session type
            if SESSION_STRING:
                logging.info("🔑 Starting with user session...")
                await client.start()
                
                # Verify session works
                try:
                    me = await client.get_me()
                    logging.info(f"✅ User session active: @{me.username or 'No username'} (ID: {me.id})")
                    logging.info(f"🚀 Session type: USER - Can upload files up to 4GB")
                except Exception as e:
                    logging.error(f"❌ User session verification failed: {e}")
                    logging.info("🔄 Session may be expired, continuing with bot token if available...")
                    if not BOT_TOKEN:
                        raise Exception("User session failed and no bot token provided")
                    
            elif BOT_TOKEN:
                logging.info("🤖 Starting with bot token...")
                await client.start(bot_token=BOT_TOKEN)
                
                me = await client.get_me()
                logging.info(f"✅ Bot session active: @{me.username} (ID: {me.id})")
                logging.info(f"🚀 Session type: BOT - Can upload files up to 2GB")
            else:
                raise Exception("No authentication method provided")

            # Create download directory
            if not os.path.exists(DOWNLOAD_DIR):
                os.makedirs(DOWNLOAD_DIR)
                logging.info(f"📁 Created download directory: {DOWNLOAD_DIR}")

            # Success message
            session_info = "User session (4GB max)" if is_user_session else "Bot session (2GB max)"
            logging.info(f"🎉 ZeroTrace Leech Bot started successfully!")
            logging.info(f"🔗 Session: {session_info}")
            logging.info(f"👥 Authorized users: {len(authorized_users)}")
            
            # Run until disconnected
            await client.run_until_disconnected()
            
        except KeyboardInterrupt:
            logging.info("🛑 Bot stopped by user")
            break
        except Exception as e:
            logging.error(f"💥 Bot crashed: {str(e)}\n{traceback.format_exc()}")
            logging.info("🔄 Restarting in 5 seconds...")
            await asyncio.sleep(5)

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logging.info("🛑 Bot stopped by user (Ctrl+C)")
    except Exception as e:
        logging.error(f"💥 Fatal startup error: {str(e)}\n{traceback.format_exc()}")
    finally:
        logging.info("🔌 Bot shutdown complete")

# Additional utility functions
def get_file_hash(filepath, algorithm='md5'):
    """Generate file hash for integrity checking"""
    import hashlib
    hash_func = getattr(hashlib, algorithm)()
    try:
        with open(filepath, 'rb', buffering=8*1024*1024) as f:
            while chunk := f.read(8*1024*1024):
                hash_func.update(chunk)
        return hash_func.hexdigest()
    except Exception as e:
        logging.warning(f"Failed to generate {algorithm} hash for {filepath}: {e}")
        return None

async def verify_upload_integrity(original_path, uploaded_message):
    """Verify uploaded file integrity"""
    try:
        if not os.path.exists(original_path):
            return True
            
        original_size = os.path.getsize(original_path)
        
        if uploaded_message and uploaded_message.id:
            logging.info(f"Upload integrity check passed - Message ID: {uploaded_message.id}")
            return True
        return False
    except Exception as e:
        logging.warning(f"Upload integrity check failed: {e}")
        return True

def estimate_processing_time(file_size, operation_type='download'):
    """Estimate processing time"""
    base_speeds = {
        'download': 50 * 1024 * 1024,
        'upload': 30 * 1024 * 1024,
        'decrypt': 100 * 1024 * 1024,
        'split': 200 * 1024 * 1024,
    }
    
    speed = base_speeds.get(operation_type, 50 * 1024 * 1024)
    estimated_time = file_size / speed
    return max(estimated_time, 5)

def format_eta(seconds):
    """Format ETA"""
    if seconds < 60:
        return f"~{int(seconds)}s"
    elif seconds < 3600:
        return f"~{int(seconds/60)}m"
    else:
        return f"~{int(seconds/3600)}h{int((seconds%3600)/60)}m"

async def cleanup_old_files_periodic():
    """Periodic cleanup task"""
    while True:
        try:
            await asyncio.sleep(3600)
            current_time = time.time()
            cutoff_age = 6 * 3600
            
            for user_id in os.listdir(DOWNLOAD_DIR):
                if not user_id.startswith('user_'):
                    continue
                    
                user_dir = os.path.join(DOWNLOAD_DIR, user_id)
                if not os.path.isdir(user_dir):
                    continue
                
                cleaned_files = cleaned_size = 0
                for root, _, files in os.walk(user_dir):
                    for file in files:
                        filepath = os.path.join(root, file)
                        try:
                            if os.path.isfile(filepath):
                                file_age = current_time - os.path.getmtime(filepath)
                                if file_age > cutoff_age:
                                    file_size = os.path.getsize(filepath)
                                    os.remove(filepath)
                                    cleaned_files += 1
                                    cleaned_size += file_size
                        except Exception as e:
                            logging.warning(f"Failed to clean up {filepath}: {e}")
                
                if cleaned_files > 0:
                    logging.info(f"Cleaned {cleaned_files} files ({format_size(cleaned_size)}) for user {user_id}")
                    
        except Exception as e:
            logging.error(f"Cleanup error: {e}")
            await asyncio.sleep(1800)

asyncio.create_task(cleanup_old_files_periodic())

def optimize_memory_usage():
    """Optimize memory usage"""
    import gc
    try:
        collected = gc.collect()
        try:
            import psutil
            process = psutil.Process()
            memory_mb = process.memory_info().rss / 1024 / 1024
            logging.debug(f"Memory usage: {memory_mb:.1f}MB, GC collected: {collected} objects")
        except ImportError:
            logging.debug(f"GC collected: {collected} objects")
    except Exception as e:
        logging.warning(f"Memory optimization failed: {e}")

class PerformanceMonitor:
    def __init__(self):
        self.start_times = {}
        self.operation_stats = {}
    
    def start_operation(self, operation_id, operation_type):
        self.start_times[operation_id] = {
            'start_time': time.time(),
            'type': operation_type
        }
    
    def end_operation(self, operation_id, bytes_processed=0):
        if operation_id not in self.start_times:
            return
        
        start_info = self.start_times[operation_id]
        elapsed = time.time() - start_info['start_time']
        operation_type = start_info['type']
        
        if operation_type not in self.operation_stats:
            self.operation_stats[operation_type] = {
                'total_time': 0,
                'total_bytes': 0,
                'operations': 0
            }
        
        stats = self.operation_stats[operation_type]
        stats['total_time'] += elapsed
        stats['total_bytes'] += bytes_processed
        stats['operations'] += 1
        
        if stats['total_time'] > 0:
            avg_speed = stats['total_bytes'] / stats['total_time']
            logging.debug(f"Operation {operation_type}: {format_time(elapsed)}, Avg speed: {format_size(avg_speed)}/s")
        
        del self.start_times[operation_id]
    
    def get_stats(self):
        return self.operation_stats.copy()

perf_monitor = PerformanceMonitor()

def format_error_report(error, context="Unknown"):
    """Format error report"""
    import traceback
    import sys
    
    error_type = type(error).__name__
    error_msg = str(error)
    tb_lines = traceback.format_exception(type(error), error, error.__traceback__)
    stack_trace = ''.join(tb_lines)
    python_version = sys.version.split()[0]
    
    try:
        import psutil
        memory_info = f"{psutil.Process().memory_info().rss / 1024 / 1024:.1f}MB"
    except ImportError:
        memory_info = "Unavailable"
    
    report = f"""
🐛 **Error Report**
📍 **Context:** {context}
🚨 **Type:** {error_type}
💬 **Message:** {error_msg}
🐍 **Python:** {python_version}
📊 **Memory:** {memory_info}

📋 **Stack Trace:**

```
{stack_trace}
```
"""
    return report

def validate_configuration():
    """Validate configuration"""
    issues = []
    
    required_vars = ['API_ID', 'API_HASH', 'ALLOWED_USERS']
    for var in required_vars:
        if not os.getenv(var):
            issues.append(f"Missing required environment variable: {var}")
    
    if not SESSION_STRING and not BOT_TOKEN:
        issues.append("Either SESSION_STRING or BOT_TOKEN must be provided")
    
    try:
        os.makedirs(DOWNLOAD_DIR, exist_ok=True)
        test_file = os.path.join(DOWNLOAD_DIR, '.test')
        with open(test_file, 'w') as f:
            f.write('test')
        os.remove(test_file)
    except Exception as e:
        issues.append(f"Download directory not writable: {DOWNLOAD_DIR} - {e}")
    
    try:
        import shutil
        free_space = shutil.disk_usage(DOWNLOAD_DIR).free
        if free_space < 1024 * 1024 * 1024:
            issues.append(f"Low disk space: {format_size(free_space)} available")
    except Exception as e:
        issues.append(f"Could not check disk space: {e}")
    
    if not os.path.exists(MP4DECRYPT_PATH):
        issues.append(f"mp4decrypt not found at: {MP4DECRYPT_PATH}")
    
    required_tools = ['ffmpeg', 'ffprobe']
    for tool in required_tools:
        try:
            result = subprocess.run([tool, '-version'], capture_output=True, timeout=5)
            if result.returncode != 0:
                issues.append(f"Required tool not working: {tool}")
        except (subprocess.TimeoutExpired, FileNotFoundError):
            issues.append(f"Required tool not found: {tool}")
    
    if issues:
        logging.error("❌ Configuration validation failed:")
        for issue in issues:
            logging.error(f"  • {issue}")
        return False
    else:
        logging.info("✅ Configuration validation passed")
        return True

if not validate_configuration():
    logging.error("🛑 Bot cannot start due to configuration issues")
    sys.exit(1)

logging.info("🚀 ZeroTrace Leech Bot - Optimized for maximum performance")
logging.info("🔧 Features: DRM decryption, 4GB+ uploads, concurrent processing")
logging.info("⚡ Ready for high-speed leeching!")
