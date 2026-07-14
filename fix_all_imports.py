import subprocess
import re
import sys

while True:
    print("Running lake build InfoGeometry.All...")
    result = subprocess.run(["lake", "build", "InfoGeometry.All"], capture_output=True, text=True)
    if result.returncode == 0:
        print("Build succeeded!")
        sys.exit(0)
    
    match = re.search(r"import ([\w\.]+) failed, environment already contains", result.stderr)
    if not match:
        print("Build failed with a different error:")
        print(result.stderr)
        sys.exit(1)
    
    bad_import = match.group(1)
    print(f"Removing offending import: {bad_import}")
    
    with open("lean/InfoGeometry/All.lean", "r") as f:
        lines = f.readlines()
        
    with open("lean/InfoGeometry/All.lean", "w") as f:
        for line in lines:
            if bad_import not in line:
                f.write(line)
