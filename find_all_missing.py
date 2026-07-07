import os

recovery_dirs = [
    'agent_writes_recovery',
    'agent_writes_recovery_v2',
    'agent_writes_recovery_v3',
    'agent_writes_recovery_v4',
    'agent_memory_recovery',
    'agent_memory_recovery_stitched',
    'recovery',
    'archive/scratch_recovery'
]

live_dir = 'lean'

live_files = {}
for root, _, files in os.walk(live_dir):
    for f in files:
        if f.endswith('.lean'):
            live_files[f] = os.path.join(root, f)

unique_missing_or_diff = {}

for rec_dir in recovery_dirs:
    if not os.path.exists(rec_dir): continue
    for root, _, files in os.walk(rec_dir):
        for f in files:
            if f.endswith('.lean'):
                rec_path = os.path.join(root, f)
                if f in live_files:
                    with open(rec_path, 'r') as f1, open(live_files[f], 'r') as f2:
                        content1 = f1.read().strip()
                        content2 = f2.read().strip()
                        if content1 and content1 != content2:
                            unique_missing_or_diff[f] = (rec_path, live_files[f])
                else:
                    unique_missing_or_diff[f] = (rec_path, None)

for f, (rec, live) in unique_missing_or_diff.items():
    if live:
        print(f"DIFFERENT: {rec} -> {live}")
    else:
        print(f"MISSING: {rec}")
