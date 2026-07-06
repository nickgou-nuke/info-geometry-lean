import glob
import json
import os

brain_dir = "/home/goutev/.gemini/antigravity-cli/brain"
transcripts = glob.glob(f"{brain_dir}/**/transcript_full.jsonl", recursive=True)

with open("bash_edits.txt", "w") as out:
    for t_path in transcripts:
        try:
            with open(t_path, 'r') as f:
                for line in f:
                    data = json.loads(line)
                    if data.get("type") == "PLANNER_RESPONSE":
                        for call in data.get("tool_calls", []):
                            if call.get("name") == "run_command":
                                cmd = call.get("args", {}).get("CommandLine", "")
                                if "sed " in cmd or "echo " in cmd or "awk " in cmd:
                                    out.write(f"{t_path} : {cmd}\n")
        except Exception:
            pass
