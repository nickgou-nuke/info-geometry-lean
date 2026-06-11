import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Canonical.CuntzPrimitiveExactness

/-!
# Cuntz exactness bridge

This file isolates the Hilbert-space Cuntz defect calculation.

For continuous linear maps on a complex Hilbert space, the Cuntz child
decomposition attached to two branches is

`S_L ∘ A ∘ S_L† + S_R ∘ A ∘ S_R†`.

The only closed theorem proved here is algebraic: if the two branch range
operators sum to the identity, then the defect of the identity operator is zero.
Conversely, a zero defect is exactly the corresponding child decomposition.

#### BUCKET 1: CLOSED FINITE THEOREMS
The identity operator has zero Cuntz defect under an explicit partition
hypothesis, and zero defect rearranges to the child decomposition.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
All theorems are conditional on explicit continuous-linear-map branch data and,
for the identity theorem, an explicit partition hypothesis.

#### BUCKET 3: OPEN CLOSURE DEBT
No theorem here derives branch maps, a Cuntz representation, K-theory,
holonomy, or analytic primitive exactness from the Hilbert-space defect.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzExactnessBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
Discrete Cuntz defect of an operator `A` with respect to two branch maps.

It measures the difference between the parent operator and the sum of its two
branch-compressed children.
-/
def cuntzDerivative
    (S_L S_R A : H →L[ℂ] H) : H →L[ℂ] H :=
  A -
    (S_L ∘L A ∘L ContinuousLinearMap.adjoint S_L +
      S_R ∘L A ∘L ContinuousLinearMap.adjoint S_R)

/--
The identity operator has zero Cuntz defect under the explicit partition
`S_L S_L† + S_R S_R† = id`.
-/
theorem cuntz_vacuum_is_exact
    (S_L S_R : H →L[ℂ] H)
    (h_partition :
      S_L ∘L ContinuousLinearMap.adjoint S_L +
        S_R ∘L ContinuousLinearMap.adjoint S_R = ContinuousLinearMap.id ℂ H) :
    cuntzDerivative S_L S_R (ContinuousLinearMap.id ℂ H) = 0 := by
  unfold cuntzDerivative
  simp [h_partition]

/--
Zero Cuntz defect is exactly the statement that the parent operator is recovered
from the two branch-compressed children.
-/
theorem exactness_prevents_anomaly
    (S_L S_R A : H →L[ℂ] H)
    (h_exact : cuntzDerivative S_L S_R A = 0) :
    A =
      S_L ∘L A ∘L ContinuousLinearMap.adjoint S_L +
        S_R ∘L A ∘L ContinuousLinearMap.adjoint S_R := by
  exact sub_eq_zero.mp h_exact

end InfoGeometry.Canonical.CuntzExactnessBridge

end noncomputable section
