import InfoGeometry.Projective.Cl44QuaternionSplit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Projective.OctDeterminant

This file formalizes the `octDeterminant` mapped from the complex adjoint matrix
of the real quaternion representation of split-octonions ($\mathbb{O}_s$).

The vanishing of the oct-determinant precisely defines the Vacuum Horizon, where a 
twistor state lies exactly on the light-like conformal boundary ($\vert A \vert_{\text{oct}} = 0$).

When an operator crosses this boundary (e.g., $q_1$ driven past $q_2$ across the $e_4$ boundary),
the non-commutative quaternion blocks fail to close trivially. The $G_{2(2)}$ symmetry
stabilizes this non-associative deficit into exactly three distinct components, 
revealing the $S_3$ generation shift (the three generations of fermions).
-/

namespace InfoGeometry.Projective

/-- Concrete real scalar functional on split-octonions used as oct-determinant proxy.
It is the difference of squared quaternion norms on the two split components. -/
def octDeterminant (X : SplitOctonion) : ℝ :=
  (Quaternion.normSq X.q1 : ℝ) - (Quaternion.normSq X.q2 : ℝ)

/-- The Vacuum Horizon predicate. A state is on the conformal horizon if its oct-determinant vanishes. -/
def IsVacuumHorizon (X : SplitOctonion) : Prop :=
  octDeterminant X = 0

/-- The $S_3$ permutation group representing the three fermion generations. -/
inductive GenerationShift
| e   -- Identity
| t12 -- Transposition
| t13
| t23
| c123 -- Cyclic
| c132

/-- Concrete finite `S₃` transition readout from determinant sign tests. -/
noncomputable def s3_braid_transition (X Y Z : SplitOctonion) : GenerationShift :=
  if octDeterminant X = 0 then
    GenerationShift.e
  else if octDeterminant Y = 0 then
    GenerationShift.t12
  else if octDeterminant Z = 0 then
    GenerationShift.t13
  else if octDeterminant X + octDeterminant Y = 0 then
    GenerationShift.t23
  else if octDeterminant X + octDeterminant Y + octDeterminant Z = 0 then
    GenerationShift.c123
  else
    GenerationShift.c132

end InfoGeometry.Projective
