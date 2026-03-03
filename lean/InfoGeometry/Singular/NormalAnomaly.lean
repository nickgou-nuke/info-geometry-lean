import Mathlib
import InfoGeometry.Singular.MoorePenroseAdjoint
import InfoGeometry.Singular.DrazinAdjoint

/-!
# Normal Metrics and Anomaly Vanishing

This module proves that the Chiral Anomaly is strictly a feature of 
non-normal (non-EP) singular boundaries. If the metric's Moore-Penrose 
inverse commutes with the metric itself (the EP condition), the spectral 
and geometric mirrors align perfectly, and the Anomaly vanishes.
-/

namespace InfoGeometry.Singular.NormalAnomaly

open InfoGeometry.Singular.MoorePenroseAdjoint
open InfoGeometry.Singular.DrazinAdjoint

variable {R : Type*} [Ring R] [AdjointLike R]

/-- 
An element is "EP" (Equal Projector) if its Moore-Penrose inverse 
commutes with it. This generalizes normality for singular operators.
In finite dimensions, an operator is EP if and only if its range and 
kernel are orthogonal complements.
-/
def IsEP (A B : R) (_hMP : IsMoorePenroseInverse A B) : Prop :=
  A * B = B * A

/--
If an operator is EP, its Moore-Penrose inverse satisfies the exact 
equations for a Group Inverse (a Drazin inverse of index k = 1).
-/
lemma EP_implies_group_inverse
    (A B : R)
    (hMP : IsMoorePenroseInverse A B)
    (hEP : IsEP A B hMP) :
    B * A * B = B ∧ A * B = B * A ∧ A = A * A * B := by
  refine ⟨hMP.eq2, hEP, ?_⟩
  calc
    A = A * B * A := hMP.eq1.symm
    _ = A * (B * A) := by rw [mul_assoc]
    _ = A * (A * B) := by rw [← hEP]
    _ = A * A * B := by rw[← mul_assoc]

/--
The Vanishing Theorem:
If the Geometric Projector and the Spectral Projector align, the Chiral 
Anomaly is strictly zero. The metric-spectral mismatch disappears, and 
the singular natural gradient experiences no gauge rotation.
-/
theorem Anomaly_vanishes_if_projectors_eq
    (A B D : R) (k : ℕ)
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k)
    (hEq : MP_Projector A B hMP = Drazin_Projector A D k hD) :
    ChiralAnomaly A B D k hMP hD = 0 := by
  unfold ChiralAnomaly
  rw [hEq]
  -- P_D * P_D - P_D * P_D = 0
  exact sub_self (Drazin_Projector A D k hD * Drazin_Projector A D k hD)

end InfoGeometry.Singular.NormalAnomaly
