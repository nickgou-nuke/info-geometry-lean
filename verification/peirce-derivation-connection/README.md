# Peirce derivation connection: focused verification

This verification surface reuses the existing `peirce-defect-boundaries`
package, its exact root pins, canonical `../../lean` source directory, and
shared compiler lock. It adds no dependency manifest or copied build wrapper.
Pass the new targets explicitly; the reused package's defaults are unchanged.

```bash
python3 verification/peirce-derivation-connection/audit.py
python3 verification/peirce-defect-boundaries/check.py build \
  InfoGeometry.OperatorAlgebra.PeirceDerivationConnection \
  InfoGeometry.OperatorAlgebra.PeirceDerivationConnectionAudit
python3 verification/peirce-defect-boundaries/check.py env lean \
  -DwarningAsError=true lean/InfoGeometry/OperatorAlgebra/PeirceDerivationConnection.lean
python3 verification/peirce-defect-boundaries/check.py env lean \
  -DwarningAsError=true lean/InfoGeometry/OperatorAlgebra/PeirceDerivationConnectionAudit.lean \
  > peirce-derivation-axioms.log 2>&1
python3 verification/peirce-derivation-connection/audit.py --log peirce-derivation-axioms.log
python3 verification/peirce-defect-boundaries/check.py env lean --run \
  tools/infra/axiom_check.lean \
  verification/peirce-defect-boundaries/.lake/build/lib/lean/InfoGeometry/OperatorAlgebra/PeirceDerivationConnection.olean
```

The source inventory includes every public declaration in the new owner.
The compiled-module replay checks private/generated declarations as well.
The only permitted transitive axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Source screening and independent mathematical review are separate
from kernel compilation.

The theorem contract and preserved intake live in
[`docs/PEIRCE_DERIVATION_CONNECTION_CONTRACT.md`](../../docs/PEIRCE_DERIVATION_CONNECTION_CONTRACT.md).
The CI workflow uses these explicit targets. Focused success establishes the
reported algebraic theorem, not full-root build health or the intake's physical
interpretations.
