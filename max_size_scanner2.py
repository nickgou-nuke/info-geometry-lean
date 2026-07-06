import glob
import json
import os
import re

brain_dir = "/home/goutev/.gemini/antigravity-cli/brain"
transcripts = glob.glob(f"{brain_dir}/**/transcript_full.jsonl", recursive=True)

file_sizes = {}
file_contents = {}

for t_path in transcripts:
    try:
        with open(t_path, 'r') as f:
            call_map = {}
            for line in f:
                data = json.loads(line)
                if data.get("type") == "PLANNER_RESPONSE":
                    for call in data.get("tool_calls", []):
                        if call.get("name") == "view_file":
                            call_id = call.get("id")
                            target = call.get("args", {}).get("AbsolutePath")
                            if call_id and target:
                                call_map[call_id] = target
                        elif call.get("name") in ["write_to_file", "replace_file_content", "multi_replace_file_content"]:
                            target = call.get("args", {}).get("TargetFile")
                            content = call.get("args", {}).get("CodeContent", call.get("args", {}).get("ReplacementContent", ""))
                            if target:
                                size = len(content)
                                if target not in file_sizes or size > file_sizes[target]:
                                    file_sizes[target] = size
                                    file_contents[target] = (size, t_path)
                
                elif data.get("type") == "TOOL_RESPONSE":
                    for resp in data.get("tool_responses", []):
                        if resp.get("name") == "view_file":
                            call_id = resp.get("id")
                            if call_id in call_map:
                                target = call_map[call_id]
                                output = resp.get("output", "")
                                # extract the actual code
                                code_lines = []
                                for out_line in output.split('\n'):
                                    m = re.match(r'^[0-9]+: (.*)$', out_line)
                                    if m:
                                        code_lines.append(m.group(1))
                                    elif not out_line.startswith("The following code") and out_line.strip() != "":
                                        code_lines.append(out_line)
                                full_code = "\n".join(code_lines)
                                size = len(full_code)
                                if target not in file_sizes or size > file_sizes[target]:
                                    file_sizes[target] = size
                                    file_contents[target] = (size, t_path)
    except Exception as e:
        pass

for k, v in file_contents.items():
    if "HestenesKreinModularGeometry" in k:
        print(f"{k}: max size {v[0]} bytes in {v[1]}")

print(len(file_contents))