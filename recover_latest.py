import json
import os
import re

logs_dir = "/home/goutev/.gemini/antigravity-cli/brain"
repo_dir = "/home/goutev/repos/info-geometry-lean"

recovered_files = {}
file_timestamps = {}

# Sort conversations by modification time to process oldest to newest
conv_dirs = [os.path.join(logs_dir, d) for d in os.listdir(logs_dir)]
conv_dirs.sort(key=lambda x: os.path.getmtime(x) if os.path.exists(x) else 0)

for conv_path in conv_dirs:
    conv_id = os.path.basename(conv_path)
    log_path = os.path.join(conv_path, ".system_generated", "logs", "transcript_full.jsonl")
    if not os.path.exists(log_path):
        continue
    
    with open(log_path, 'r') as f:
        lines = f.readlines()
        
    for i in range(len(lines)):
        try:
            step = json.loads(lines[i])
        except json.JSONDecodeError:
            continue
            
        if step.get("type") == "PLANNER_RESPONSE" and step.get("tool_calls"):
            for call in step["tool_calls"]:
                if call.get("name") == "view_file":
                    args = call.get("args", {})
                    abs_path = args.get("AbsolutePath", "")
                    
                    if not isinstance(abs_path, str):
                        continue
                        
                    abs_path = abs_path.strip('"')
                    
                    if "/lean/InfoGeometry/" in abs_path:
                        for j in range(i + 1, min(i + 10, len(lines))):
                            try:
                                next_step = json.loads(lines[j])
                            except json.JSONDecodeError:
                                continue
                                
                            if next_step.get("type") == "VIEW_FILE":
                                output = next_step.get("content", "")
                                
                                if abs_path not in output:
                                    continue
                                
                                # Extract timestamp
                                timestamp = next_step.get("created_at", "")
                                
                                # Only keep the LATEST version
                                if abs_path not in file_timestamps or timestamp > file_timestamps[abs_path]:
                                    lines_with_nums = output.split('\n')
                                    recovered_content = []
                                    
                                    for line in lines_with_nums:
                                        if line.startswith("Showing lines"):
                                            continue
                                        if line.startswith("The following code has been modified"):
                                            continue
                                        if line.startswith("Total Lines") or line.startswith("Total Bytes") or line.startswith("File Path:") or line.startswith("Created At:") or line.startswith("Completed At:") or line.startswith("The above content shows the entire"):
                                            continue
                                            
                                        match = re.match(r'^[0-9]+: (.*)$', line)
                                        if match:
                                            recovered_content.append(match.group(1))
                                        else:
                                            if not line.startswith("The following code") and line.strip() != "":
                                                recovered_content.append(line)
                                                
                                    if recovered_content:
                                        recovered_files[abs_path] = '\n'.join(recovered_content)
                                        file_timestamps[abs_path] = timestamp
                                        print(f"Recovered {abs_path} from subagent {conv_id} at {timestamp}")
                                break

print(f"Total recovered files: {len(recovered_files)}")
for filepath, content in recovered_files.items():
    try:
        with open(filepath, 'w') as f:
            f.write(content)
        print(f"Written restored content to {filepath}")
    except Exception as e:
        print(f"Error writing to {filepath}: {e}")
