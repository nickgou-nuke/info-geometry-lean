import os
import subprocess

with open("/tmp/contested_files.txt", "r") as f:
    files = [line.strip() for line in f if line.strip().endswith(".lean")]

for file in files:
    basename = os.path.basename(file)
    os.makedirs(f"sandbox/reconciliation/{basename}_audit", exist_ok=True)
    
    # Get main version
    with open(f"sandbox/reconciliation/{basename}_audit/{basename}.main", "w") as out:
        subprocess.run(["git", "show", f"origin/main:{file}"], stdout=out)
        
    # Get local version
    with open(f"sandbox/reconciliation/{basename}_audit/{basename}.local", "w") as out:
        subprocess.run(["git", "show", f"HEAD:{file}"], stdout=out)

print("Sandbox preparation complete.")
