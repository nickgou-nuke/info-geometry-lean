import json
import os
import re

logs_dir = "/home/goutev/.gemini/antigravity-cli/brain"
repo_dir = "/home/goutev/repos/info-geometry-lean"

for conv_id in os.listdir(logs_dir):
    log_path = os.path.join(logs_dir, conv_id, ".system_generated", "logs", "transcript.jsonl")
    log_full_path = os.path.join(logs_dir, conv_id, ".system_generated", "logs", "transcript_full.jsonl")
    
    if not os.path.exists(log_full_path):
        continue
    
    with open(log_full_path, 'r') as f:
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
                        # Some versions might store args as a JSON string?
                        print("args is not a dict?", type(args))
                        continue
                    
                    # It seems `args` could be a JSON string itself!
                    print(f"Subagent {conv_id} view_file AbsPath: {abs_path}")
