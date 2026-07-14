import os
import re

brain_dir = os.path.expanduser("~/.gemini/antigravity-cli/brain/")
print(f"Searching in {brain_dir}...")

pattern = re.compile(r"theorem non_parabolic_normal_form.*?(?=theorem|def|lemma|/-|/--|```|\Z)", re.DOTALL)

for root, dirs, files in os.walk(brain_dir):
    for file in files:
        if file.endswith(".log") or file.endswith(".jsonl") or file.endswith(".md") or file.endswith(".txt") or file.endswith(".lean"):
            filepath = os.path.join(root, file)
            try:
                with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
                    content = f.read()
                    matches = pattern.finditer(content)
                    for m in matches:
                        snippet = m.group(0)
                        if "sorry" not in snippet:
                            print(f"--- Found non-sorry proof in {filepath} ---")
                            print(snippet[:500]) # print start of snippet
            except Exception as e:
                pass
print("Done searching.")
