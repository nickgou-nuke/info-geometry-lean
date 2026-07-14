import os
import subprocess

sandbox_dir = "sandbox"
canonical_dir = "lean/InfoGeometry"

for root, _, files in os.walk(sandbox_dir):
    for file in files:
        if file.endswith(".lean"):
            sandbox_path = os.path.join(root, file)
            # Find matching file in canonical_dir
            find_cmd = ["find", canonical_dir, "-name", file]
            result = subprocess.run(find_cmd, capture_output=True, text=True)
            matches = result.stdout.strip().split("\n")
            
            if len(matches) > 0 and matches[0]:
                canonical_path = matches[0]
                # Compare line counts
                wc_sand = int(subprocess.run(["wc", "-l", sandbox_path], capture_output=True, text=True).stdout.split()[0])
                wc_can = int(subprocess.run(["wc", "-l", canonical_path], capture_output=True, text=True).stdout.split()[0])
                
                if wc_sand > wc_can:
                    print(f"sandbox has MORE: {sandbox_path} ({wc_sand}) vs {canonical_path} ({wc_can})")
                elif wc_sand < wc_can:
                    print(f"canonical has MORE: {sandbox_path} ({wc_sand}) vs {canonical_path} ({wc_can})")
                else:
                    # check diff
                    diff = subprocess.run(["cmp", "-s", sandbox_path, canonical_path])
                    if diff.returncode != 0:
                        print(f"DIFFERENT content but same size: {sandbox_path} vs {canonical_path}")
