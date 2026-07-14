import json

with open("/home/goutev/.gemini/antigravity-cli/brain/516fc029-194e-48d5-8d81-7c4c6194fa88/.system_generated/logs/transcript_full.jsonl") as f:
    for line in f:
        try:
            data = json.loads(line)
            if data.get("type") == "PLANNER_RESPONSE":
                for call in data.get("tool_calls", []):
                    if call["name"] in ["replace_file_content", "multi_replace_file_content", "write_to_file"]:
                        if "MobiusGeometry.lean" in str(call):
                            print("-------------------")
                            print("TOOL:", call["name"])
                            args = call.get("args", {})
                            print("ReplacementContent len:", len(args.get("ReplacementContent", "")))
        except Exception:
            pass
