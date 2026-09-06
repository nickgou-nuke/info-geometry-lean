import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

noncomputable section

namespace InfoGeometry.Canonical.BiQuaternionKahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def KaehlerMetric (X Y : E) : ℝ :=
  @inner ℝ _ _ X Y

def IsSkewSymmetric (A : E →L[ℝ] E) : Prop :=
  ∀ X Y : E, KaehlerMetric (A X) Y = - KaehlerMetric X (A Y)

-- The directional derivative (gradient action) of the potential V along a vector v.
variable (gradV : E → E)

def IsPotentialInvariant (A : E →L[ℝ] E) : Prop :=
  ∀ Φ : E, KaehlerMetric (gradV Φ) (A Φ) = 0

def NoetherCharge (A : E →L[ℝ] E) (Φ P : E) : ℝ :=
  KaehlerMetric (A Φ) P

def NoetherChargeTimeDeriv (A : E →L[ℝ] E) (Φ P : E) : ℝ :=
  KaehlerMetric (A P) P + KaehlerMetric (A Φ) (- gradV Φ)

theorem skew_symmetric_self_orthogonal (A : E →L[ℝ] E) (hA : IsSkewSymmetric A) (P : E) :
    KaehlerMetric (A P) P = 0 := by
  have h1 : KaehlerMetric (A P) P = - KaehlerMetric P (A P) := hA P P
  have h2 : KaehlerMetric P (A P) = KaehlerMetric (A P) P := @real_inner_comm E _ _ P (A P)
  linarith

theorem noether_charge_conserved (A : E →L[ℝ] E) (hA : IsSkewSymmetric A) (hV : IsPotentialInvariant gradV A) (Φ P : E) :
    NoetherChargeTimeDeriv gradV A Φ P = 0 := by
  unfold NoetherChargeTimeDeriv
  rw [skew_symmetric_self_orthogonal A hA P]
  have h_inv : KaehlerMetric (gradV Φ) (A Φ) = 0 := hV Φ
  have h_inner_neg : KaehlerMetric (A Φ) (- gradV Φ) = - KaehlerMetric (A Φ) (gradV Φ) := @inner_neg_right ℝ E _ _ _ (A Φ) (gradV Φ)
  rw [h_inner_neg]
  have h_comm : KaehlerMetric (A Φ) (gradV Φ) = KaehlerMetric (gradV Φ) (A Φ) := @real_inner_comm E _ _ (A Φ) (gradV Φ)
  rw [h_comm, h_inv]
  ring

end InfoGeometry.Canonical.BiQuaternionKahler
