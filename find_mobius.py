import json
import glob
import sys

for f_name in glob.glob("/home/goutev/.gemini/antigravity-cli/brain/*/.system_generated/logs/transcript_full.jsonl"):
    try:
        with open(f_name) as f:
            for line in f:
                if "MobiusGeometry.lean" in line:
                    data = json.loads(line)
                    if data.get("type") == "PLANNER_RESPONSE":
                        calls = data.get("tool_calls", [])
                        for call in calls:
                            if call["name"] in ["replace_file_content", "multi_replace_file_content", "write_to_file"]:
                                if "MobiusGeometry.lean" in str(call):
                                    print(f"Found modification in {f_name}")
                                    sys.exit(0)
    except Exception as e:
        pass
