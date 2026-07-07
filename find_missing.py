import os

recovery_dirs = ['agent_writes_recovery_v4/lean/InfoGeometry', 'agent_memory_recovery/untracked_lean']
live_dir = 'lean/InfoGeometry'

live_files = {}
for root, _, files in os.walk(live_dir):
    for f in files:
        if f.endswith('.lean'):
            live_files[f] = os.path.join(root, f)

for rec_dir in recovery_dirs:
    for root, _, files in os.walk(rec_dir):
        for f in files:
            if f.endswith('.lean'):
                rec_path = os.path.join(root, f)
                if f in live_files:
                    # check if different
                    with open(rec_path, 'r') as f1, open(live_files[f], 'r') as f2:
                        if f1.read() != f2.read():
                            print(f"DIFFERENT: {rec_path} -> {live_files[f]}")
                else:
                    print(f"MISSING: {rec_path}")
