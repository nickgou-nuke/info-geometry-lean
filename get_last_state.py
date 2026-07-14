import json

last_content = ""
for f_name in ["/home/goutev/.gemini/antigravity-cli/brain/4891de22-1ca1-4896-a4ff-f42469ff1635/.system_generated/logs/transcript_full.jsonl",
               "/home/goutev/.gemini/antigravity-cli/brain/164fbd0b-cd44-4992-8f90-ae58a5db0345/.system_generated/logs/transcript_full.jsonl"]:
    with open(f_name) as f:
        for line in f:
            try:
                data = json.loads(line)
                if data.get("type") == "PLANNER_RESPONSE":
                    for call in data.get("tool_calls", []):
                        if call["name"] in ["replace_file_content", "multi_replace_file_content", "write_to_file"]:
                            if "MobiusGeometry.lean" in str(call):
                                args = call.get("args", {})
                                if call["name"] == "write_to_file":
                                    last_content = args.get("CodeContent", "")
                                elif call["name"] == "replace_file_content":
                                    target = args.get("TargetContent", "")
                                    repl = args.get("ReplacementContent", "")
                                    if target in last_content:
                                        last_content = last_content.replace(target, repl)
            except Exception:
                pass
print("Lines in last_content:", len(last_content.split("\n")))
if len(last_content.split("\n")) > 1000:
    with open("MobiusGeometry_recovered.lean", "w") as out:
        out.write(last_content)
    print("Recovered to MobiusGeometry_recovered.lean!")
