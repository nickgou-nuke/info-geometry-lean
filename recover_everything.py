import glob
import json
import os
import re

brain_dir = "/home/goutev/.gemini/antigravity-cli/brain"
out_dir = "agent_writes_recovery_v3"
os.makedirs(out_dir, exist_ok=True)

transcripts = glob.glob(f"{brain_dir}/**/transcript_full.jsonl", recursive=True)

file_states = {} # abs_path -> (timestamp, content, source_transcript)

rogue_keywords = ["vacuity", "purify", "purifier", "purification", "remove dummy", "sorry", "opaque"]

for t_path in transcripts:
    is_rogue = False
    
    try:
        with open(t_path, 'r') as f:
            for i, line in enumerate(f):
                if i > 20: break
                data = json.loads(line)
                if data.get("type") in ["USER_INPUT", "SYSTEM"]:
                    content = str(data.get("content", "")).lower()
                    if any(k in content for k in rogue_keywords):
                        is_rogue = True
                        break
    except Exception:
        pass
        
    if is_rogue:
        continue

    try:
        with open(t_path, 'r') as f:
            pending_views = [] # list of (path, timestamp)
            for line in f:
                data = json.loads(line)
                timestamp = data.get("created_at", "")
                step_type = data.get("type")
                
                if step_type == "PLANNER_RESPONSE":
                    for call in data.get("tool_calls", []):
                        name = call.get("name")
                        args = call.get("args", {})
                        if name == "view_file":
                            path = args.get("AbsolutePath")
                            if path:
                                pending_views.append((path, timestamp))
                        elif name == "write_to_file":
                            path = args.get("TargetFile")
                            content = args.get("CodeContent")
                            if path and content:
                                if path not in file_states or timestamp > file_states[path][0]:
                                    file_states[path] = (timestamp, content, t_path)
                        # Ignoring multi_replace for a moment, let's just get write_to_file and view_file
                elif step_type == "SYSTEM" and pending_views:
                    # The system response might contain the view_file output
                    content = str(data.get("content", ""))
                    if "The following code" in content or "1:" in content:
                        # Extract code
                        code_lines = []
                        for out_line in content.split('\n'):
                            m = re.match(r'^[0-9]+: (.*)$', out_line)
                            if m:
                                code_lines.append(m.group(1))
                            elif not out_line.startswith("The following code") and out_line.strip() != "":
                                code_lines.append(out_line)
                        full_code = "\n".join(code_lines)
                        
                        path, ts = pending_views.pop(0) # naive match
                        if path not in file_states or ts > file_states[path][0]:
                            file_states[path] = (ts, full_code, t_path)
    except Exception:
        pass

for path, (ts, content, source) in file_states.items():
    if not path.startswith("/home/goutev/repos/info-geometry-lean/lean/"):
        continue
    rel_path = os.path.relpath(path, "/home/goutev/repos/info-geometry-lean")
    dest_path = os.path.join(out_dir, rel_path)
    os.makedirs(os.path.dirname(dest_path), exist_ok=True)
    with open(dest_path, "w") as f:
        f.write(content)

print(f"Recovered {len(file_states)} files.")
