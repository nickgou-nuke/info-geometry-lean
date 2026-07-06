import json
import os
import re

logs_dir = "/home/goutev/.gemini/antigravity-cli/brain"
repo_dir = "/home/goutev/repos/info-geometry-lean"
out_dir = os.path.join(repo_dir, "agent_memory_recovery")

if not os.path.exists(out_dir):
    os.makedirs(out_dir)

total_snapshots = 0

conv_dirs = [os.path.join(logs_dir, d) for d in os.listdir(logs_dir)]

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
                    
                    if "/lean/" in abs_path:
                        # Find the VIEW_FILE response
                        for j in range(i + 1, min(i + 10, len(lines))):
                            try:
                                next_step = json.loads(lines[j])
                            except json.JSONDecodeError:
                                continue
                                
                            if next_step.get("type") == "VIEW_FILE":
                                output = next_step.get("content", "")
                                if abs_path not in output:
                                    continue
                                
                                timestamp = next_step.get("created_at", "unknown_time").replace(":", "-").replace("T", "_").replace("Z", "")
                                
                                lines_with_nums = output.split('\n')
                                recovered_content = []
                                
                                for line in lines_with_nums:
                                    if line.startswith("Showing lines") or line.startswith("The following code") or \
                                       line.startswith("Total Lines") or line.startswith("Total Bytes") or \
                                       line.startswith("File Path:") or line.startswith("Created At:") or \
                                       line.startswith("Completed At:") or line.startswith("The above content"):
                                        continue
                                        
                                    match = re.match(r'^[0-9]+: (.*)$', line)
                                    if match:
                                        recovered_content.append(match.group(1))
                                    else:
                                        if line.strip() != "":
                                            recovered_content.append(line)
                                            
                                if recovered_content:
                                    filename = os.path.basename(abs_path)
                                    file_out_dir = os.path.join(out_dir, filename)
                                    if not os.path.exists(file_out_dir):
                                        os.makedirs(file_out_dir)
                                        
                                    out_file = os.path.join(file_out_dir, f"{timestamp}_{conv_id[:8]}.lean")
                                    with open(out_file, 'w') as f:
                                        f.write('\n'.join(recovered_content))
                                    total_snapshots += 1
                                break

print(f"Extraction complete! Dumped {total_snapshots} historical file snapshots into {out_dir}")
