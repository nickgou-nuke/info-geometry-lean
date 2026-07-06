import os
import json
import glob
import re

brain_dir = "/home/goutev/.gemini/antigravity-cli/brain"
out_dir = "agent_writes_recovery_v2"
os.makedirs(out_dir, exist_ok=True)

# Find all full transcripts
transcripts = glob.glob(f"{brain_dir}/**/transcript_full.jsonl", recursive=True)

file_states = {} # map file_path -> (timestamp, content, source_agent)

rogue_keywords = ["vacuity", "purify", "purifier", "purification", "remove dummy", "sorry", "opaque"]
# We will check the first few messages (USER_INPUT or SYSTEM) to see if it's a rogue agent

for t_path in transcripts:
    is_rogue = False
    agent_id = t_path.split("/")[-4] if len(t_path.split("/")) > 4 else "unknown"
    
    # Read first 10 lines to check if it's rogue
    try:
        with open(t_path, 'r') as f:
            for i, line in enumerate(f):
                if i > 15:
                    break
                data = json.loads(line)
                if data.get("type") in ["USER_INPUT", "SYSTEM"]:
                    content = str(data.get("content", "")).lower()
                    if any(k in content for k in rogue_keywords):
                        is_rogue = True
                        break
    except Exception as e:
        pass
        
    if is_rogue:
        continue
        
    # Now parse the transcript for file contents
    try:
        with open(t_path, 'r') as f:
            for line in f:
                data = json.loads(line)
                timestamp = data.get("created_at", "")
                
                # Check tool calls for write_to_file
                if data.get("type") == "PLANNER_RESPONSE":
                    for call in data.get("tool_calls", []):
                        if call.get("name") == "write_to_file":
                            args = call.get("args", {})
                            path = args.get("TargetFile")
                            content = args.get("CodeContent")
                            if path and content:
                                if path not in file_states or timestamp > file_states[path][0]:
                                    file_states[path] = (timestamp, content, agent_id)
                
                # Check tool responses for view_file
                if data.get("type") == "TOOL_RESPONSE":
                    for resp in data.get("tool_responses", []):
                        if resp.get("name") == "view_file":
                            # The response output usually contains the file content
                            # We might need to parse it if it has "1: ... 2: ..."
                            output = resp.get("output", "")
                            # If it was called by the agent, we might not have the path in the response directly,
                            # but we can try to guess from the output if there's a file path printed, or we could track it.
                            # Actually, a simpler way is just to parse dump_history.py's output, but dump_history might have missed write_to_file!
    except Exception as e:
        pass

# Let's write a more robust parser for view_file that tracks the call args.
