# Peirce defect boundaries: focused verification

This package compiles the exact repository sources with the root Lean and
Mathlib pins. It does not change the root dependency declarations or depend
on the root project's optional external reference checkouts.

```bash
python3 verification/peirce-defect-boundaries/audit.py
python3 verification/peirce-defect-boundaries/check.py build
python3 verification/peirce-defect-boundaries/check.py env lean lean/InfoGeometry/OperatorAlgebra/PeirceDefectBoundaryAudit.lean
python3 verification/peirce-defect-boundaries/audit.py --log peirce-defect-axioms.log
```

The third command's complete output must be captured in the file passed to
the fourth command. The wrapper uses the repository's shared compiler lock
and rejects linked worktrees and symlinked Lake roots. It does not certify
whole-repository build health.

`audit.py --write` regenerates the explicit audit inventory from all public
named definitions, abbreviations, and theorems in the seven new mathematical
owners. The coverage check rejects a stale inventory. Private helpers are
included through the reported declarations' transitive axiom dependencies.
The log check requires every listed declaration and allows only `propext`,
`Classical.choice`, and `Quot.sound`.

The corresponding GitHub workflow also screens all new owners and retains
the build and fresh axiom logs. Source screening, kernel compilation, and
independent mathematical review are separate checks.
