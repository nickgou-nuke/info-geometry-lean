import json
import os
import re

logs_dir = "/home/goutev/.gemini/antigravity-cli/brain"
repo_dir = "/home/goutev/repos/info-geometry-lean"

recovered_files = {}

# Iterate over all subagent conversation directories
for conv_id in os.listdir(logs_dir):
    log_path = os.path.join(logs_dir, conv_id, ".system_generated", "logs", "transcript_full.jsonl")
    if not os.path.exists(log_path):
        continue
    
    with open(log_path, 'r') as f:
        lines = f.readlines()
        
    for i in range(len(lines)):
        try:
            step = json.loads(lines[i])
        except json.JSONDecodeError:
            continue
            
        # Look for a view_file tool call
        if step.get("type") == "PLANNER_RESPONSE" and step.get("tool_calls"):
            for call in step["tool_calls"]:
                if call.get("name") == "view_file":
                    args = call.get("args", {})
                    abs_path = args.get("AbsolutePath", "")
                    
                    if not isinstance(abs_path, str):
                        continue
                        
                    # Remove surrounding quotes if they exist
                    abs_path = abs_path.strip('"')
                    
                    # Only recover files in lean/InfoGeometry that we don't already have a recovered version of
                    if "/lean/InfoGeometry/" in abs_path and abs_path not in recovered_files:
                        # The response is usually the next step
                        if i + 1 < len(lines):
                            try:
                                next_step = json.loads(lines[i + 1])
                            except json.JSONDecodeError:
                                continue
                                
                            if next_step.get("type") == "TOOL_RESPONSE":
                                output = next_step.get("content", "")
                                
                                # The output has line numbers added: "1: import Mathlib\n2: ..."
                                # We need to strip those out
                                lines_with_nums = output.split('\n')
                                recovered_content = []
                                
                                in_code_block = False
                                for line in lines_with_nums:
                                    if line.startswith("Showing lines"):
                                        continue
                                    if line.startswith("The following code has been modified"):
                                        continue
                                    if line.startswith("Total Lines") or line.startswith("Total Bytes") or line.startswith("File Path:") or line.startswith("Created At:") or line.startswith("Completed At:") or line.startswith("The above content shows the entire"):
                                        continue
                                        
                                    # Regex to remove the line number: "^[0-9]+: "
                                    match = re.match(r'^[0-9]+: (.*)$', line)
                                    if match:
                                        recovered_content.append(match.group(1))
                                    else:
                                        # Keep empty lines or lines without numbers (if any)
                                        if not line.startswith("The following code") and line.strip() != "":
                                            recovered_content.append(line)
                                
                                # Ensure we actually extracted something
                                if recovered_content:
                                    recovered_files[abs_path] = '\n'.join(recovered_content)
                                    print(f"Recovered {abs_path} from subagent {conv_id}")

print(f"Total recovered files: {len(recovered_files)}")
for filepath, content in recovered_files.items():
    with open(filepath, 'w') as f:
        f.write(content)
    print(f"Written restored content to {filepath}")
