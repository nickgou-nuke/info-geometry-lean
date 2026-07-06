import json
import os

transcript_path = "/home/goutev/.gemini/antigravity-cli/brain/69a72ecd-b2d0-4a83-b43d-328025f28438/.system_generated/logs/transcript_full.jsonl"
out_dir = "agent_writes_recovery"

os.makedirs(out_dir, exist_ok=True)

with open(transcript_path, 'r') as f:
    for line in f:
        try:
            data = json.loads(line)
        except:
            continue
        
        if data.get("type") == "PLANNER_RESPONSE":
            tool_calls = data.get("tool_calls", [])
            for call in tool_calls:
                name = call.get("name")
                args = call.get("args", {})
                
                if name in ["write_to_file", "replace_file_content", "multi_replace_file_content"]:
                    target = args.get("TargetFile")
                    if target:
                        safe_name = target.replace("/", "_")
                        timestamp = data.get("created_at", "unknown_time").replace(":", "-")
                        file_out = os.path.join(out_dir, f"{timestamp}_{safe_name}.json")
                        with open(file_out, "w") as out_f:
                            json.dump(args, out_f, indent=2)
