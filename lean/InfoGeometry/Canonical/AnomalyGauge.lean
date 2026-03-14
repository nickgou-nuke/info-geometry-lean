import Mathlib
import InfoGeometry.Canonical.MoorePenroseAdjoint
import InfoGeometry.Canonical.DrazinAdjoint
import InfoGeometry.Canonical.KreinNaturalFlow
import InfoGeometry.Canonical.Krein

/-!
# The Anomaly Gauge Field

This module proves the geometric nature of the Chiral Anomaly on the singular boundary.
Because the anomaly is the commutator of two geometric projectors (Moore-Penrose and Drazin),
it is intrinsically skew-adjoint. In the Krein space, this means the Anomaly is an 
Infinitesimal Isometry (a Lie algebra generator), acting as a gauge rotation that 
preserves the degenerate causal boundary.
-/

namespace InfoGeometry.Canonical.AnomalyGauge

open InfoGeometry.Singular.MoorePenroseAdjoint
open InfoGeometry.Singular.DrazinAdjoint
open InfoGeometry.Singular.Architecture
open InfoGeometry.Krein

section AbstractGaugeTheory

variable {R : Type*} [Ring R] [StarRing R]

/-- 
**The Fundamental Commutator Lemma:**
In any star ring, the commutator
of two self-adjoint elements is strictly skew-adjoint.
-/
lemma commutator_is_skew_adjoint (A B : R) (hA : A† = A) (hB : B† = B) :
    (A * B - B * A)† = -(A * B - B * A) := by
  calc
    (A * B - B * A)† = (B * A - A * B) := by
      simp [sub_eq_add_neg, hA, hB]
    _ = -(A * B - B * A) := by
      simp [sub_eq_add_neg]

/-- 
**The Anomaly is a Gauge Field:**
The Chiral Anomaly, being the commutator of the Moore-Penrose and Drazin projectors,
is strictly skew-adjoint (assuming the Drazin projector preserves the metric's symmetries).
-/
theorem ChiralAnomaly_is_SkewAdjoint
    (G G_pinv D_inv : R) (k : ℕ)
    (hMP : IsMoorePenroseInverse G G_pinv)
    (hD : IsDrazinInverse G D_inv k)
    (hD_symm : (Drazin_Projector G D_inv k hD)† = Drazin_Projector G D_inv k hD) :
    (ChiralAnomaly G G_pinv D_inv k hMP hD)† = -(ChiralAnomaly G G_pinv D_inv k hMP hD) := by
  unfold ChiralAnomaly
  apply commutator_is_skew_adjoint
  · exact MP_Projector_self_adjoint hMP
  · exact hD_symm

end AbstractGaugeTheory

section KreinAnomaly

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E][CompleteSpace E]

/-- 
**Geometric Realization:**
A skew-adjoint operator on the Hilbert carrier mathematically corresponds to an 
operator preserving the Krein metric. 
-/
lemma skew_adjoint_is_krein_skew_adjoint
    (X : HilbertDoubled E →L[ℝ] HilbertDoubled E)
    (hSkew : X† = -X) : 
    IsKreinSkewAdjointH (E := E) X := hSkew

/-- 
**The Master Theorem of the Singular Boundary:**
The Chiral Anomaly physically generates a metric-preserving flow (a rotation) 
along the causal boundary. It does not destroy the symmetric space; it acts as 
an internal Lie algebra generator!
-/
theorem anomaly_generates_isometry
    (G G_pinv D_inv : HilbertDoubled E →L[ℝ] HilbertDoubled E) (k : ℕ)
    (hMP : IsMoorePenroseInverse G G_pinv)
    (hD : IsDrazinInverse G D_inv k)
    (hD_symm : (Drazin_Projector G D_inv k hD)† = Drazin_Projector G D_inv k hD) :
    IsKreinSkewAdjointH (E := E) (ChiralAnomaly G G_pinv D_inv k hMP hD) := by
  apply skew_adjoint_is_krein_skew_adjoint
  exact ChiralAnomaly_is_SkewAdjoint G G_pinv D_inv k hMP hD hD_symm

end KreinAnomaly
end InfoGeometry.Canonical.AnomalyGauge
