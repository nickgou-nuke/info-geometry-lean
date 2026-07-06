import glob
import json
import os

brain_dir = "/home/goutev/.gemini/antigravity-cli/brain"
transcripts = glob.glob(f"{brain_dir}/**/transcript_full.jsonl", recursive=True)

rogue_keywords = ["vacuity", "purify", "purifier", "purification", "remove dummy", "sorry", "opaque"]

found = 0
for t_path in transcripts:
    is_rogue = False
    try:
        with open(t_path, 'r') as f:
            for i, line in enumerate(f):
                if i > 20: break
                try:
                    step = json.loads(line)
                    if step.get("type") in ["USER_INPUT", "SYSTEM"]:
                        content = str(step.get("content", "")).lower()
                        if any(k in content for k in rogue_keywords):
                            is_rogue = True
                            break
                except Exception:
                    pass
    except Exception:
        pass

    if is_rogue:
        continue
    
    with open(t_path, 'r') as f:
        for line in f:
            data = json.loads(line)
            if data.get("type") == "PLANNER_RESPONSE":
                for call in data.get("tool_calls", []):
                    if call.get("name") in ["replace_file_content", "multi_replace_file_content", "write_to_file"]:
                        target = call.get("args", {}).get("TargetFile", "")
                        if "HestenesKreinModularGeometry" in target or "FiveGradedCentralizer" in target:
                            print(f"Found {call.get('name')} in {t_path} at {data.get('created_at')}")
                            found += 1

print(f"Total found: {found}")
