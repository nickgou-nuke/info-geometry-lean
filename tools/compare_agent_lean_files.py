import os

with open("scratch/all_agent_lean_files.txt") as f:
    agent_files = [line.strip() for line in f if line.strip()]

repo_files = set()
for root, _, files in os.walk("lean"):
    for file in files:
        if file.endswith(".lean"):
            repo_files.add(file)

lost_files = []
for file in agent_files:
    basename = os.path.basename(file)
    if basename not in repo_files:
        lost_files.append(file)

with open("scratch/lost_agent_files.txt", "w") as f:
    for f_name in lost_files:
        f.write(f_name + "\n")

print(f"Found {len(lost_files)} lost .lean files across all agents.")
