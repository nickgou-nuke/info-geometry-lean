#!/usr/bin/env python3
"""
socratic_buffer.py — Extract a single theorem to a temp buffer, send to ChatGPT
via aiClaw REST API, capture the fix, compile it.

Usage:
    python3 tools/infra/socratic_buffer.py \
        --file lean/InfoGeometry/Canonical/KMSInteriorPoint.lean \
        --theorem flow_uniformly_continuous \
        --buffer-dir /tmp/socratic_buffers

No original files are modified. All artifacts go to --buffer-dir.
"""

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
AICLAW_URL = "http://127.0.0.1:10088/api/v1/ai/message"
PLATFORM = "chatgpt"

def parse_args():
    p = argparse.ArgumentParser(description="Buffer-based socratic oracle")
    p.add_argument("--file", required=True, type=Path, help="Original Lean file")
    p.add_argument("--theorem", required=True, help="Theorem name to extract")
    p.add_argument("--buffer-dir", default="/tmp/socratic_buffers", type=Path)
    p.add_argument("--dry-run", action="store_true", help="Only extract, don't send")
    return p.parse_args()

def extract_theorem(lean_file: Path, theorem: str) -> str | None:
    """Extract minimal compilable context for a theorem — just copy the
    entire file preamble up to and including the theorem, dropping
    everything after."""
    content = lean_file.read_text()
    lines = content.split("\n")
    found = -1
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith(f"theorem {theorem}") or stripped.startswith(f"lemma {theorem}"):
            found = i
            break
    if found == -1:
        return None
    # Return everything from the start up to and including the theorem block.
    # The theorem block ends at the first blank line after the proof.
    result = lines[:found]
    i = found
    depth = 0
    while i < len(lines):
        result.append(lines[i])
        stripped = lines[i].strip()
        if ":=" in stripped:
            depth += stripped.count(":=")
        if stripped == "" and depth == 1:
            break
        i += 1
    return "\n".join(result)

def build_buffer(extracted: str) -> str:
    """Wrap the extracted theorem in a minimal compilable buffer."""
    lines = extracted.split("\n")
    # Pull imports to the top
    imports = [l for l in lines if l.strip().startswith("import ")]
    rest = [l for l in lines if not l.strip().startswith("import ")]
    # Strip unterminated doc comments (/-! without -/)
    cleaned = []
    in_block_comment = False
    for l in rest:
        if in_block_comment:
            if "-/" in l:
                in_block_comment = False
            continue
        if l.strip().startswith("/-"):
            if "-/" not in l:
                in_block_comment = True
            continue
        cleaned.append(l)
    return "\n".join(imports + [""] + cleaned)

def compile_check(buffer_path: Path) -> tuple[int, str]:
    """Run lake env lean on the buffer, return (exit_code, output)."""
    cmd = ["lake", "env", "lean", str(buffer_path)]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=120, cwd=REPO)
    return r.returncode, r.stdout + r.stderr

def send_to_aiclaw(prompt: str, dry_run: bool = False) -> str | None:
    """Send a prompt to ChatGPT via the aiClaw REST bridge."""
    if dry_run:
        print(f"[dry-run] Would send {len(prompt)} chars to {AICLAW_URL}")
        return None
    print(f"Sending {len(prompt)} chars to ChatGPT via aiClaw...")
    payload = {"message": prompt, "platform": PLATFORM}
    try:
        r = requests.post(AICLAW_URL, json=payload, timeout=120)
        r.raise_for_status()
        resp = r.json()
        return resp.get("response") or resp.get("text") or str(resp)
    except Exception as e:
        return f"[ERROR] aiClaw call failed: {e}"

def main():
    import requests  # lazy import
    args = parse_args()

    # 1. Extract theorem
    extracted = extract_theorem(args.file, args.theorem)
    if extracted is None:
        print(f"ERROR: theorem '{args.theorem}' not found in {args.file}")
        sys.exit(1)
    print(f"Extracted theorem '{args.theorem}' ({len(extracted)} chars)")

    # 2. Build buffer
    buffer = build_buffer(extracted)
    args.buffer_dir.mkdir(parents=True, exist_ok=True)
    buffer_path = args.buffer_dir / f"{args.theorem}.lean"
    buffer_path.write_text(buffer)
    print(f"Buffer written to {buffer_path}")

    # 3. Dry-run compile check
    ec, output = compile_check(buffer_path)
    if ec == 0:
        print(f"Buffer compiles cleanly — no sorry to fix!")
        sys.exit(0)
    print(f"Buffer compile exited {ec}")
    # Print last 5 lines of error
    err_lines = output.split("\n")[-8:]
    for l in err_lines:
        print(f"  | {l}")

    # 4. Send to ChatGPT
    prompt = f"""Fix this Lean 4 proof. The buffer file is:

```lean4
{buffer}
```

The compile error is:

```
{output}
```

Return ONLY the corrected code block, nothing else."""
    if args.dry_run:
        print("\n[dry-run] Exiting without sending to ChatGPT.")
        sys.exit(0)

    response = send_to_aiclaw(prompt)
    if response is None:
        print("ERROR: No response from aiClaw")
        sys.exit(1)

    # 5. Extract code block from response, if any
    fix_path = args.buffer_dir / f"{args.theorem}_fix.lean"
    # Try to find a lean code block in the response
    if "```lean4" in response:
        code = response.split("```lean4")[1].split("```")[0].strip()
        fix_path.write_text(code)
    elif "```lean" in response:
        code = response.split("```lean")[1].split("```")[0].strip()
        fix_path.write_text(code)
    else:
        fix_path.write_text(response)

    # 6. Compile the fix
    print(f"\nCompiling fix from {fix_path}...")
    ec2, output2 = compile_check(fix_path)
    if ec2 == 0:
        print(f"✅ FIX COMPILES — {fix_path}")
    else:
        print(f"❌ Fix did not compile (exit {ec2})")
        for l in output2.split("\n")[-5:]:
            print(f"  | {l}")

if __name__ == "__main__":
    main()
