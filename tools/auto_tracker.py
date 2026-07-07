import os
import time
import subprocess

REPO_DIR = "/home/goutev/repos/info-geometry-lean"

def auto_track():
    print("Auto-tracker active: constantly scanning for untracked files...")
    while True:
        try:
            # Check for any untracked files (respecting .gitignore)
            result = subprocess.run(
                ["git", "ls-files", "--others", "--exclude-standard"], 
                cwd=REPO_DIR, 
                capture_output=True, 
                text=True
            )
            
            if result.stdout.strip():
                # If there are untracked files, add them to the Git index
                subprocess.run(["git", "add", "-A"], cwd=REPO_DIR)
                files_tracked = len(result.stdout.strip().split('\n'))
                print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] Auto-staged {files_tracked} new/modified files.")
        except Exception as e:
            print(f"Auto-tracker error: {e}")
            
        time.sleep(5)  # Scan every 5 seconds

if __name__ == "__main__":
    auto_track()
