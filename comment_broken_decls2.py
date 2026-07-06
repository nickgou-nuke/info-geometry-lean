import subprocess
import re

def process_file(filepath):
    print(f"Checking {filepath}...")
    result = subprocess.run(
        ["lake", "env", "lean", filepath],
        capture_output=True,
        text=True
    )
    
    if result.returncode == 0:
        print(f"{filepath} is OK.")
        return
        
    error_lines = set()
    for line in result.stderr.split('\n') + result.stdout.split('\n'):
        m = re.match(rf"^{re.escape(filepath)}:(\d+):\d+: error", line)
        if m:
            error_lines.add(int(m.group(1)))
            
    if not error_lines:
        print(f"Could not find error line numbers for {filepath}.")
        return
        
    print(f"Found errors on lines: {sorted(error_lines)}")
    
    with open(filepath, 'r') as f:
        lines = f.read().split('\n')
        
    blocks = []
    current_block_start = -1
    for i, line in enumerate(lines):
        if re.match(r'^(theorem|def|instance|structure|class|inductive|@[^ ]+) ', line) or line.startswith('@[') or line.startswith('theorem ') or line.startswith('def ') or line.startswith('instance '):
            if current_block_start != -1:
                blocks.append((current_block_start, i - 1))
            current_block_start = i
    if current_block_start != -1:
        blocks.append((current_block_start, len(lines) - 1))
        
    blocks_to_comment = set()
    for err_line in error_lines:
        idx = err_line - 1
        for b_start, b_end in blocks:
            if b_start <= idx <= b_end:
                blocks_to_comment.add((b_start, b_end))
                break
                
    for b_start, b_end in sorted(blocks_to_comment, reverse=True):
        print(f"Commenting out block from {b_start+1} to {b_end+1}")
        lines.insert(b_end + 1, "-/")
        lines.insert(b_start, "/-- BROKEN DECLARATION:")
        
    with open(filepath, 'w') as f:
        f.write('\n'.join(lines))
        
files = [
    "lean/InfoGeometry/Algebra/OrbitClassificationBridge.lean",
    "lean/InfoGeometry/Algebra/GeometricBridge.lean",
    "lean/InfoGeometry/Algebra/Zorn/TrialityTriple.lean"
]

for f in files:
    process_file(f)

