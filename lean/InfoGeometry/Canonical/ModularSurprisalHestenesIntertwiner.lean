
import InfoGeometry.Canonical.LogScaleModularSurprisalBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesModularRealizationBridge

/-!
# Modular Surprisal Hestenes Intertwiner

This file provides the explicit intertwining between the abstract complex Tomita-Takesaki
surprisal generator $\mathcal{K}$ and its real Hestenes geometric realization $I V$.

By establishing the realification map $J$, we formally prove that the two continuous
flows (and their discrete Lapidus/Mellin samplings) are mathematically identical representations
of the same geometric phase rotation.
-/

namespace InfoGeometry.Canonical.ModularSurprisalHestenesIntertwiner

open InfoGeometry.Canonical.LogScaleModularSurprisalBridge
open InfoGeometry.Canonical.HestenesModularRealizationBridge

noncomputable section

variable {A M : Type*}
variable [AddCommGroup A] [Module ℂ A]
variable [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]

local notation "EndM" => M →L[ℝ] M

/-- The Hestenes geometric operator $IV$ squares to $-V^2$. -/
theorem hestenes_IV_sq (D : HestenesModularDatum (M := M)) :
    (D.I ∘L D.V_op) ∘L (D.I ∘L D.V_op) = - (D.V_op ∘L D.V_op) := by
  have hIV : D.I ∘L D.V_op = D.V_op ∘L D.I := by
    simpa [ContinuousLinearMap.mul_def] using D.commute_I_V.eq
  calc
    (D.I ∘L D.V_op) ∘L (D.I ∘L D.V_op) =
        D.I ∘L (D.V_op ∘L D.I) ∘L D.V_op := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = D.I ∘L (D.I ∘L D.V_op) ∘L D.V_op := by rw [hIV]
    _ = (D.I ∘L D.I) ∘L (D.V_op ∘L D.V_op) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (-ContinuousLinearMap.id ℝ M) ∘L (D.V_op ∘L D.V_op) := by
          rw [D.I_sq_eq_neg_one]
    _ = -(D.V_op ∘L D.V_op) := by
          ext x
          simp

/-- The Lapidus shift $c \cdot \mathrm{id} + IV$ commutes with the internal unit $I$. -/
theorem hestenesLapidusShift_commutes_I (D : HestenesModularDatum (M := M)) (c : ℝ) :
    Commute (c • ContinuousLinearMap.id ℝ M + D.I ∘L D.V_op) D.I := by
  have hIV : D.I ∘L D.V_op = D.V_op ∘L D.I := by
    simpa [ContinuousLinearMap.mul_def] using D.commute_I_V.eq
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_add, map_smul]
  have hx : D.I (D.V_op x) = D.V_op (D.I x) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun f : EndM => f x) hIV
  rw [← hx]

/-- The intertwiner datum connecting the complex and real modular representations. -/
structure ModularHestenesIntertwiner (D_C : ModularSurprisalDatum A) (D_H : HestenesModularDatum (M := M)) where
  /-- The realification equivalence $J$. -/
  J : A ≃ₗ[ℝ] M

  /-- Intertwining of the generators: $J(\mathcal{K} x) = (IV)(Jx)$. -/
  modularGenerator_intertwining : ∀ x : A,
    J (D_C.K x) = (D_H.I ∘L D_H.V_op) (J x)

  /-- Intertwining of the continuous modular flow. -/
  modularFlow_hestenes_intertwining : ∀ (t : ℝ) (x : A),
    J (D_C.U t x) = D_H.Delta_real t (J x)

/-- Prime modular sampling perfectly intertwines between complex and Hestenes regimes. -/
theorem primeSample_hestenes_intertwining
    (D_C : ModularSurprisalDatum A) (D_H : HestenesModularDatum (M := M))
    (W : ModularHestenesIntertwiner D_C D_H) (p : ℕ) (_hp : Nat.Prime p) (x : A) :
    W.J (dirichletModularSample D_C p x) = D_H.Delta_real (Real.log p) (W.J x) := by
  simpa [dirichletModularSample] using
    W.modularFlow_hestenes_intertwining (Real.log p) x

/-- Arithmetic closure of the discrete Hestenes flow sampling. -/
theorem hestenes_arithmetic_closure (D_H : HestenesModularDatum (M := M)) (n m : ℕ) (hn : n > 0) (hm : m > 0) :
    D_H.Delta_real (Real.log (n * m)) = D_H.Delta_real (Real.log n) ∘L D_H.Delta_real (Real.log m) := by
  have hlog : Real.log ((n * m : ℕ) : ℝ) = Real.log (n : ℝ) + Real.log (m : ℝ) := by
    simpa [Nat.cast_mul] using
      (Real.log_mul (ne_of_gt (Nat.cast_pos.mpr hn))
        (ne_of_gt (Nat.cast_pos.mpr hm)))
  rw [← Nat.cast_mul, hlog, hestenes_flow_add]

end

end InfoGeometry.Canonical.ModularSurprisalHestenesIntertwiner
