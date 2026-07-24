#!/usr/bin/env python3
import subprocess
import time
import urllib.request
import os

print("Launching Chrome GUI Browser Daemon on port 9222...")
env = os.environ.copy()
env["DISPLAY"] = os.environ.get("DISPLAY", ":0")

cmd = [
    "/snap/bin/chromium",
    "--user-data-dir=/tmp/chrome_gui_dev_profile",
    "--remote-debugging-port=9222",
    "--remote-allow-origins=*",
    "https://chatgpt.com/?temporary-chat=true"
]

proc = subprocess.Popen(cmd, env=env)
time.sleep(3)

try:
    data = urllib.request.urlopen("http://127.0.0.1:9222/json/version").read().decode()
    print("SUCCESS! CHROME DAEMON IS ALIVE ON PORT 9222:")
    print(data)
except Exception as e:
    print("ERROR CHECKING PORT 9222:", e)

# Keep daemon running in background
while True:
    time.sleep(10)
