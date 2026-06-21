import json

with open("/home/goutev/.gemini/antigravity-cli/brain/958b6d2f-df75-46a3-89f9-523aa320b53a/.system_generated/logs/transcript_full.jsonl") as f:
    for line in f:
        data = json.loads(line)
        if data.get("step_index") == 8967:
            print(data.get("content", ""))
