import json
import sys

with open("/home/goutev/.gemini/antigravity-cli/brain/5ef8c132-3a11-442e-9067-a6b304a3c7e7/.system_generated/logs/transcript_full.jsonl") as f:
    for line in f:
        data = json.loads(line)
        if "diff --git a/lean/InfoGeometry/Topology/MobiusGeometry.lean" in data.get("content", ""):
            content = data["content"]
            lines = content.split("\n")
            diff_lines = []
            in_diff = False
            for l in lines:
                if l.startswith("diff --git"):
                    in_diff = True
                if in_diff:
                    diff_lines.append(l)
            with open("recover.patch", "w") as out:
                out.write("\n".join(diff_lines))
            print("Recovered patch!")
            sys.exit(0)
