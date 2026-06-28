import os, re, subprocess

tactics = ["by rfl", "by simp", "by aesop", "by simp_all", "by ext; rfl", "by ext; simp", "by decide", "by trivial"]

def test_file(path):
    res = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
    # If there's an error (not a warning), return False
    return "error:" not in res.stderr and res.returncode == 0

with open("sorry_list.txt", "w") as f_list:
    pass # we'll find them again

# Let's read the previously printed list, but wait, we can just run the finder.
sorrys = []
for root, _, files in os.walk('lean/InfoGeometry'):
    if any(x in root for x in ['/Eval', '/External', '/Meta', '/SelfReference', '/Lint']): continue
    for file in files:
        if not file.endswith('.lean'): continue
        path = os.path.join(root, file)
        with open(path, 'r', encoding='utf-8') as f:
            content = f.read()
        lines = content.split('\n')
        for i, line in enumerate(lines):
            line_stripped = line.split('--')[0]
            if re.search(r'\bsorry\b', line_stripped):
                sorrys.append((path, i))

print(f"Found {len(sorrys)} sorrys to fix.")

fixed = 0
for path, line_idx in sorrys:
    with open(path, 'r', encoding='utf-8') as f:
        lines = f.read().split('\n')
    
    orig_line = lines[line_idx]
    success = False
    
    for tactic in tactics:
        lines[line_idx] = re.sub(r'\bsorry\b', tactic, orig_line)
        with open(path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines))
        
        if test_file(path):
            print(f"Fixed {path}:{line_idx+1} with {tactic}")
            success = True
            fixed += 1
            break
            
    if not success:
        # Revert
        lines[line_idx] = orig_line
        with open(path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines))
        print(f"Could not fix {path}:{line_idx+1}")

print(f"Fixed {fixed}/{len(sorrys)} sorrys automatically.")
