# Finite real Fock metric candidate

Uncompiled implementation of the accepted research contract
scratch/FiniteRealFockMetric20261024.md (preserved unchanged).
Imports accepted native InfoGeometry.Clifford.FockTailExteriorBasis,
Mathlib.Analysis.InnerProductSpace.PiL2 and LinearMap.

Actual carrier is SpinorSpace(Vector n), with the exact existing exterior basis.
fockCoordinates is Basis.equivFun followed by WithLp.linearEquiv.symm for p=2.
The two named reducible structures fockNormedAddCommGroup and fockInnerProductSpace
use native induced constructions. Their instance attributes are LOCAL only.
No global metric instance, new carrier, arbitrary metric input, or scalar change.

Named lemmas expose coordinate norm and inner sum, basis orthonormality, tail
inner preservation first on basis vectors and then by two finite basis expansions.
Native fockTailMap_exteriorBasis plus Finset.map_injective supplies the basis step.
fockTailLinearIsometry is LinearMap.isometryOfInner applied to the existing map;
its application is definitionally fockTailMap. Norm preservation follows.
No completeness, complex carrier, creation/contraction adjoints, coupled-family
construction, or completed colimit is asserted.

Independent QA should check induced norm/inner parent alignment and the finite
sum proof normal form. No budgets or linter suppression, no builds/tests/live edits.
All previous metric research and other agent candidates are preserved.
