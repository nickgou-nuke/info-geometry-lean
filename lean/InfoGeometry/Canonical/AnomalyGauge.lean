import Mathlib
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Singular.Drazin
import InfoGeometry.Canonical.KreinNaturalFlow
import InfoGeometry.Canonical.Krein

/-!
# The Anomaly Gauge Field

This module proves the geometric nature of the Chiral Anomaly on the singular boundary.
When the Moore-Penrose and Drazin projectors are self-adjoint, their commutator
is skew-adjoint. In the Krein space, this places the anomaly in the infinitesimal
symmetry algebra: it is a Lie algebra generator for a gauge rotation on the
degenerate causal boundary.
-/

namespace InfoGeometry.Canonical.AnomalyGauge

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.Drazin
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
is strictly skew-adjoint once the Drazin projector is assumed self-adjoint.
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
Krein-skew-adjoint operator, i.e. an infinitesimal Krein isometry.
-/
lemma skew_adjoint_is_krein_skew_adjoint
    (X : HilbertDoubled E →L[ℝ] HilbertDoubled E)
    (hSkew : X† = -X) : 
    IsKreinSkewAdjointH (E := E) X := by
  simpa [IsKreinSkewAdjointH] using hSkew

/-- 
**The Master Theorem of the Singular Boundary:**
The Chiral Anomaly is Krein-skew-adjoint, hence it defines an infinitesimal
Krein isometry along the causal boundary. This is the Lie algebra statement,
not yet the exponentiated flow/isometry statement.
-/
theorem anomaly_generates_krein_infinitesimal_isometry
    (G G_pinv D_inv : HilbertDoubled E →L[ℝ] HilbertDoubled E) (k : ℕ)
    (hMP : IsMoorePenroseInverse G G_pinv)
    (hD : IsDrazinInverse G D_inv k)
    (hD_symm : (Drazin_Projector G D_inv k hD)† = Drazin_Projector G D_inv k hD) :
    IsKreinSkewAdjointH (E := E) (ChiralAnomaly G G_pinv D_inv k hMP hD) := by
  exact skew_adjoint_is_krein_skew_adjoint _
    (ChiralAnomaly_is_SkewAdjoint G G_pinv D_inv k hMP hD hD_symm)

/--
Legacy name for the infinitesimal-isometry statement.
-/
@[deprecated anomaly_generates_krein_infinitesimal_isometry (since := "2026-03-21")]
theorem anomaly_generates_isometry
    (G G_pinv D_inv : HilbertDoubled E →L[ℝ] HilbertDoubled E) (k : ℕ)
    (hMP : IsMoorePenroseInverse G G_pinv)
    (hD : IsDrazinInverse G D_inv k)
    (hD_symm : (Drazin_Projector G D_inv k hD)† = Drazin_Projector G D_inv k hD) :
    IsKreinSkewAdjointH (E := E) (ChiralAnomaly G G_pinv D_inv k hMP hD) :=
  anomaly_generates_krein_infinitesimal_isometry G G_pinv D_inv k hMP hD hD_symm

end KreinAnomaly
end InfoGeometry.Canonical.AnomalyGauge
