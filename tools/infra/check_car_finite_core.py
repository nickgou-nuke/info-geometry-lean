"""Check the finite algebraic core independently of the blocked owner adapters."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import check_car_majorana_bridge as checker

if '--owners' in sys.argv:
    checker.TARGETS = [
        'InfoGeometry.Canonical.CARMajoranaOwnerAdapters',
        'InfoGeometry.Canonical.KreinMajoranaKernelCriterion',
    ]
else:
    checker.TARGETS = [
        'InfoGeometry.Canonical.MajoranaLinearKernel',
        'InfoGeometry.Canonical.CARMajoranaFiniteBridge',
    ]

checker.main()
out = Path(os.environ.get('RUNNER_TEMP', tempfile.gettempdir())) / 'car-majorana-deliverable'
status = json.loads((out / 'status.json').read_text())
for relative in ['tools/infra/check_car_finite_core.py',
                 'lean/InfoGeometry/Canonical/CARMajoranaOwnerAdapters.lean',
                 'lean/InfoGeometry/Canonical/KreinMajoranaKernelCriterion.lean']:
    destination = out / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(relative, destination)
    status['source_sha256'][relative] = hashlib.sha256(Path(relative).read_bytes()).hexdigest()
status['integration_adapters_checked'] = '--owners' in sys.argv
status['scope'] = ('full owner integration' if '--owners' in sys.argv else
                  'finite algebraic core only; full-owner adapters are excluded and unverified')
(out / 'status.json').write_text(json.dumps(status, indent=2))
