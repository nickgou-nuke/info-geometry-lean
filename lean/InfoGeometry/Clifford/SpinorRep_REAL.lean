import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Clifford.SpinorRep_REAL

Compatibility import for the canonical real split spinor representation.

The owner implementation is `InfoGeometry.Clifford.SpinorRep`.  It uses the
repo-native split form `Qsplit`, mathlib's `CliffordAlgebra.lift`, and the
real `Cl(1,1)` atom with signs `(+1,-1)`.  This file intentionally declares no
second Pauli tower and no theorem aliases.
-/
