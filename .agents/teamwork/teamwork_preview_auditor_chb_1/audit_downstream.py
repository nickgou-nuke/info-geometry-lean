#!/usr/bin/env python3
import os
import sys
import subprocess
from pathlib import Path

sys.path.insert(0, os.path.abspath("."))
from tools.build_lock import acquire_build_lock

sandbox_chb = Path('.agents/sandbox_connes_hodge/lean/DAG/ConnesHodgeBridge.lean').read_text()
dag_content = Path('lean/DAG.lean').read_text()

all_imports = set()
for line in (sandbox_chb + '\n' + dag_content).splitlines():
    if line.startswith('import '):
        imp = line.split()[1].strip()
        if imp != 'DAG.ConnesHodgeBridge':
            all_imports.add(f'import {imp}')

def strip_imports(text):
    return '\n'.join([line for line in text.splitlines() if not line.startswith('import ')])

chb_body = strip_imports(sandbox_chb)
dag_body = strip_imports(dag_content)

full_input = '\n'.join(sorted(all_imports)) + '\n\n' + chb_body + '\n\n' + dag_body

print('=== Independent Downstream Verification: DAG.lean with Sandbox ConnesHodgeBridge ===')
with acquire_build_lock(None, 'auditor_downstream', block=True):
    proc = subprocess.run(
        ['lake', 'env', 'lean', '--stdin'],
        input=full_input,
        text=True,
        capture_output=True
    )

print('Return code:', proc.returncode)
filtered_err = [l for l in proc.stderr.splitlines() if 'manifest out of date' not in l]
if filtered_err:
    print('STDERR (filtered):\n', '\n'.join(filtered_err))
else:
    print('STDERR: Clean')
assert proc.returncode == 0, f"DAG.lean compilation failed with code {proc.returncode}"
print("=== Downstream DAG.lean PASSED ===")
