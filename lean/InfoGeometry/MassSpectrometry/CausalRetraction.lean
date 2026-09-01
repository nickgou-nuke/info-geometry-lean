import Mathlib
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.MassSpectrometry.PeakFragmentMatching
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling

/-!
# Moore-Penrose causal retraction

This module does not redefine the Penrose equations. Matrix-level retractions
reuse `InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse`; the actual
closed-range Hilbert-space construction is re-exported from
`InfoGeometry.Singular.MoorePenrose`.

The doubled projectivity tensor is even with respect to the mass-spectrometry
chiral grading because it is a product of two odd doubled operators.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open Matrix

namespace CanonicalMP

abbrev IsMoorePenroseInverse {R : Type*} [Ring R] [StarRing R] :=
  InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse (R := R)

abbrev leftProjector {R : Type*} [Ring R] [StarRing R] :=
  InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector (R := R)

abbrev rightProjector {R : Type*} [Ring R] [StarRing R] :=
  InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector (R := R)

end CanonicalMP

/-- A directed matrix together with a certified Moore-Penrose inverse. -/
structure CausalRetraction {n : ℕ} (K : AssignmentMatrix n) where
  pinv : AssignmentMatrix n
  penrose : CanonicalMP.IsMoorePenroseInverse K pinv

namespace CausalRetraction

variable {n : ℕ} {K : AssignmentMatrix n} (R : CausalRetraction K)

/-- Orthogonal parent/co-range projector `K† K`. -/
def parentProjector : AssignmentMatrix n :=
  R.pinv * K

/-- Orthogonal fragment/range projector `K K†`. -/
def fragmentProjector : AssignmentMatrix n :=
  K * R.pinv

/-- The parent projector is exactly the repository-owned Moore-Penrose left projector. -/
theorem parentProjector_eq_owner :
    R.parentProjector = CanonicalMP.leftProjector K R.pinv := by
  rfl

/-- The fragment projector is exactly the repository-owned Moore-Penrose right projector. -/
theorem fragmentProjector_eq_owner :
    R.fragmentProjector = CanonicalMP.rightProjector K R.pinv := by
  rfl

/-- `K† K` is idempotent. -/
theorem parentProjector_idempotent :
    R.parentProjector * R.parentProjector = R.parentProjector := by
  exact
    InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector_idempotent
      R.penrose

/-- `K K†` is idempotent. -/
theorem fragmentProjector_idempotent :
    R.fragmentProjector * R.fragmentProjector = R.fragmentProjector := by
  exact
    InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector_idempotent
      R.penrose

/-- `K† K` is self-adjoint in the native star structure. -/
theorem parentProjector_star :
    star R.parentProjector = R.parentProjector := by
  exact
    InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector_star
      R.penrose

/-- `K K†` is self-adjoint in the native star structure. -/
theorem fragmentProjector_star :
    star R.fragmentProjector = R.fragmentProjector := by
  exact
    InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector_star
      R.penrose

/-- Chiral doubled Moore-Penrose reverse operator
`[[0,(K†)ᵀ],[K†,0]]`. -/
def doubledPinv : Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  doubledOperator R.pinv.transpose

/-- Forward-backward projectivity tensor `D_{K†} D_K`. -/
def causalProjectivityTensor : Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  R.doubledPinv * doubledOperator K

/-- The doubled Moore-Penrose reverse operator is odd under the grading. -/
theorem doubledPinv_anticommutes_grading :
    gradingMatrix n * R.doubledPinv + R.doubledPinv * gradingMatrix n = 0 := by
  simpa [doubledPinv] using
    grading_anticommute_doubledOperator (n := n) R.pinv.transpose

/-- The causal projectivity tensor is grading-even:
`Γ P = P Γ`. This uses only the two oddness laws; no extra physical
interpretation is assumed. -/
theorem projectivity_commutes_with_grading :
    gradingMatrix n * R.causalProjectivityTensor =
      R.causalProjectivityTensor * gradingMatrix n := by
  have hA :
      gradingMatrix n * R.doubledPinv =
        -(R.doubledPinv * gradingMatrix n) :=
    eq_neg_of_add_eq_zero_left R.doubledPinv_anticommutes_grading
  have hB :
      gradingMatrix n * doubledOperator K =
        -(doubledOperator K * gradingMatrix n) :=
    eq_neg_of_add_eq_zero_left
      (grading_anticommute_doubledOperator (n := n) K)
  unfold causalProjectivityTensor
  calc
    gradingMatrix n * (R.doubledPinv * doubledOperator K) =
        (gradingMatrix n * R.doubledPinv) * doubledOperator K := by
          simp only [Matrix.mul_assoc]
    _ = (-(R.doubledPinv * gradingMatrix n)) * doubledOperator K := by rw [hA]
    _ = -(R.doubledPinv * (gradingMatrix n * doubledOperator K)) := by
          simp only [neg_mul, Matrix.mul_assoc]
    _ = -(R.doubledPinv * (-(doubledOperator K * gradingMatrix n))) := by rw [hB]
    _ = (R.doubledPinv * doubledOperator K) * gradingMatrix n := by
          simp only [mul_neg, neg_neg, Matrix.mul_assoc]

/-- Equivalently the projectivity tensor is fixed by grading conjugation. -/
theorem grading_conjugates_projectivity_to_self :
    gradingMatrix n * R.causalProjectivityTensor * gradingMatrix n =
      R.causalProjectivityTensor := by
  rw [R.projectivity_commutes_with_grading]
  simp only [Matrix.mul_assoc, gradingMatrix_sq, Matrix.mul_one]

end CausalRetraction

/-! ## Constructive closed-range Hilbert owner -/

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Repository-owned constructive Moore-Penrose retraction for a closed-range
continuous linear map. -/
noncomputable def closedRangeCausalRetraction
    (A : E →L[𝕜] F) (hClosedRange : IsClosed (A.range : Set F)) :
    F →L[𝕜] E :=
  InfoGeometry.Singular.MoorePenrose.moorePenroseInverse A hClosedRange

/-- The closed-range construction satisfies all four Penrose identities. -/
theorem closedRangeCausalRetraction_isMoorePenrose
    (A : E →L[𝕜] F) (hClosedRange : IsClosed (A.range : Set F)) :
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverseCLM
      A (closedRangeCausalRetraction A hClosedRange) := by
  exact
    InfoGeometry.Singular.MoorePenrose.isMoorePenroseInverse_moorePenroseInverse
      A hClosedRange

end Hilbert

end InfoGeometry.MassSpectrometry
