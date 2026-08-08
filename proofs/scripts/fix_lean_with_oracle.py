#!/usr/bin/env python3
"""Send a broken Lean file to the ChatGPT Oracle for fixing.

Usage: python3 scripts/fix_lean_with_oracle.py proofs/FibAnyonThm4.lean
"""
import json, urllib.request, subprocess, sys, os

filepath = sys.argv[1] if len(sys.argv) > 1 else "proofs/FibAnyonThm4.lean"

# Read API key
with open('.DEEPSEEK_API_KEY') as f:
    for line in f:
        if line.startswith('export'):
            api_key = line.split('=')[1].strip().strip('"').strip("'")
            break

# Read the broken file
with open(filepath) as f:
    code = f.read()

# Get the error output
result = subprocess.run(
    ['timeout', '30', 'lake', 'env', 'lean', os.path.abspath(filepath)],
    capture_output=True, text=True,
    cwd='/home/goutev/info-geometry-lean'
)
errors = result.stderr[-2000:] if result.stderr else "No errors"

prompt = f"""You are a Lean 4 expert. The following Lean file has compilation errors.
Fix ALL errors and return the COMPLETE corrected file as a single code block.

ERRORS:
```
{errors}
```

LEAN FILE TO FIX:
```lean4
{code}
```

Requirements:
1. Fix ALL compilation errors
2. Keep the same theorem names and structure
3. Use `field_simp`, `ring`, `nlinarith`, `calc` for proofs
4. For complex identities over ℂ, use `field_simp` then `ring`
5. Return ONLY the complete corrected code, no explanation"""

data = json.dumps({"model": "deepseek-chat", "messages": [
    {"role": "system", "content": "You are a Lean 4 expert. Fix all errors and return the complete corrected file."},
    {"role": "user", "content": prompt}
], "max_tokens": 8192, "temperature": 0.1}).encode()

req = urllib.request.Request(
    "https://api.deepseek.com/v1/chat/completions",
    data=data, headers={"Content-Type": "application/json", "Authorization": f"Bearer {api_key}"}
)

print("📤 Sending to Oracle for fixing...")
resp = urllib.request.urlopen(req, timeout=60)
content = json.loads(resp.read())['choices'][0]['message']['content']

# Extract Lean code
if '```lean4' in content:
    fixed = content.split('```lean4')[1].split('```')[0]
elif '```lean' in content:
    fixed = content.split('```lean')[1].split('```')[0]
elif '```' in content:
    fixed = content.split('```')[1].split('```')[0]
else:
    fixed = content

# Write fixed file
with open(filepath, 'w') as f:
    f.write(fixed)

print(f"✅ Oracle responded, wrote {len(fixed)} chars to {filepath}")
print("Attempting compilation...")

result = subprocess.run(
    ['timeout', '45', 'lake', 'env', 'lean', os.path.abspath(filepath)],
    capture_output=True, text=True,
    cwd='/home/goutev/info-geometry-lean'
)
if result.returncode == 0:
    print("✅✅✅ COMPILATION SUCCESS!")
else:
    print(f"❌ Still broken ({result.returncode}). Re-run to try again.")
    print(result.stderr[-500:])
