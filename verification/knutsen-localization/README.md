# Knutsen localization: reproducible source and axiom checks

The seven new mathematical owners are listed in `targets.json`. Their current
repository source closure has 16 modules: the seven owners and nine reused
owners. This check uses the canonical `lean/` sources and the repository's
unchanged Lean 4.34.1 and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Run the complete selected check

Initialize a separate Mathlib checkout at the exact revision in the root
`lake-manifest.json`, with its matching dependency caches. Set
`KNUTSEN_MATHLIB_ROOT` to that directory and optionally `KNUTSEN_LEAN` to the
pinned Lean executable. Run from the repository root:

```python
import json, os, subprocess, sys
from pathlib import Path
from tools.quality.check_reviewed_prs import closure

roots = json.loads(Path('verification/knutsen-localization/targets.json').read_text())
owners, _, _ = closure(Path.cwd(), roots)
command = [sys.executable, 'tools/quality/check_clifford_dirac.py',
           '--mathlib-root', os.environ['KNUTSEN_MATHLIB_ROOT'],
           '--lean', os.environ.get('KNUTSEN_LEAN', 'lean'),
           '--output', '../knutsen-evidence']
for owner in owners:
    command += ['--target', owner]
subprocess.run(command, check=True)
report = json.loads(Path('../knutsen-evidence/report.json').read_text())
assert all(m['warnings'] == 0 for m in report['modules'] if m['module'] in roots)
```

The maintained checker copies and hashes the exact source closure, verifies the
pinned Lean and Mathlib revision, acquires `/tmp/info-geometry-build.lock`,
compiles the copied modules in dependency order, and generates a native Lean
audit over all explicitly selected module owners. The audit includes private
and generated declarations and permits only `propext`, `Classical.choice`, and
`Quot.sound` as transitive foundational axioms. Source and verifier hashes are
checked again after execution.

CI runs this command without incremental reuse. The local verification record
states separately whether each module was freshly elaborated or reused after
source, dependency-fingerprint, and artifact-hash checks.

## Hygiene and interpretation checks

For every new owner file, run the maintained `placeholder_audit.py` with
`--strict` and `semantic_vacuity_gate.py` with `--fail-on warning`, under the
shared build lock. Preserve and individually review heuristic findings. The
dedicated workflow rejects hard placeholder findings and semantic errors,
while retaining warning output. It additionally rejects compiler warnings in
any new owner.

The independent review and exact local command receipts are preserved under
`docs/verification/knutsen-localization/`. The root Lake build and actual Git
publication hooks have separate receipts; passing this focused check does not
certify them or either complete umbrella.

## Mathematical scope

This is a formalization of projection localization, isometric range corners,
finite operator frames and Weyl masks, real porosity-loss arithmetic, metric
hole preservation, and conditional multiscale estimates. It constructs no
Gaussian STFT or Bargmann transform, no Fock sampling inequality, and no
analytic fractal uncertainty exponent. See
`docs/KNUTSEN_LOCALIZATION_CONTRACT.md` for the precise hypotheses, provenance,
and paper correspondence.
