import InfoGeometry.Krein.DoubledSpace
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# InfoGeometry.Krein.HilbertBridge

Compatibility layer for the neutral-space bridge API.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev HilbertDoubled (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  DoubledSpace E

abbrev NeutralSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  DoubledSpace E

namespace NeutralSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev val (u : NeutralSpace E) : WithLp (2 : ENNReal) (E × E) := u
abbrev ofWithLp (u : WithLp (2 : ENNReal) (E × E)) : NeutralSpace E := u
abbrev toLp (v : E × E) : NeutralSpace E := WithLp.toLp 2 v

lemma val_ofWithLp (u : WithLp (2 : ENNReal) (E × E)) : (ofWithLp (E := E) u).val = u := rfl
lemma ofWithLp_val (u : NeutralSpace E) : ofWithLp (E := E) u.val = u := rfl
@[simp] lemma val_toLp (v : E × E) : (toLp (E := E) v).val = WithLp.toLp 2 v := rfl

@[ext] lemma ext {u v : NeutralSpace E} (h : u.val = v.val) : u = v := h

noncomputable abbrev neutralJ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    NeutralSpace E ≃ₗᵢ[ℝ] NeutralSpace E :=
  KreinSpace.J (H := NeutralSpace E)

private lemma one_div_sqrt_two_sq : ((1 / Real.sqrt 2 : ℝ) ^ 2) = (1 / 2 : ℝ) := by
  have hs0 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hsqrt : (Real.sqrt 2)^2 = (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  field_simp [hs0]
  nlinarith [hsqrt]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private lemma fst_add (u v : DoubledSpace E) :
    WithLp.fst (u + v) = WithLp.fst u + WithLp.fst v := by
  simp [WithLp.add_fst]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private lemma snd_add (u v : DoubledSpace E) :
    WithLp.snd (u + v) = WithLp.snd u + WithLp.snd v := by
  simp [WithLp.add_snd]

omit [CompleteSpace E] in
private lemma fst_smul (a : ℝ) (u : DoubledSpace E) :
    WithLp.fst (a • u) = a • WithLp.fst u := by
  simp [WithLp.smul_fst]

omit [CompleteSpace E] in
private lemma snd_smul (a : ℝ) (u : DoubledSpace E) :
    WithLp.snd (a • u) = a • WithLp.snd u := by
  simp [WithLp.smul_snd]

omit [CompleteSpace E] in
private lemma rotation45_norm (u : DoubledSpace E) :
    ‖InfoGeometry.Krein.to_doubled
        (((1 / Real.sqrt 2 : ℝ)) • WithLp.fst u + ((1 / Real.sqrt 2 : ℝ)) • WithLp.snd u)
        (((1 / Real.sqrt 2 : ℝ)) • WithLp.fst u - ((1 / Real.sqrt 2 : ℝ)) • WithLp.snd u)‖ = ‖u‖ := by
  let c : ℝ := 1 / Real.sqrt 2
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hcnorm : ‖c‖ = c := by
    simpa [Real.norm_eq_abs] using (abs_of_pos hcpos)
  have hc2 : c ^ 2 = (1 / 2 : ℝ) := by
    dsimp [c]
    exact one_div_sqrt_two_sq
  have hpar :
      ‖WithLp.fst u + WithLp.snd u‖ ^ 2 + ‖WithLp.fst u - WithLp.snd u‖ ^ 2
        = 2 * (‖WithLp.fst u‖ ^ 2 + ‖WithLp.snd u‖ ^ 2) := by
    nlinarith [norm_add_sq_real (WithLp.fst u) (WithLp.snd u),
      norm_sub_sq_real (WithLp.fst u) (WithLp.snd u)]
  have h1 :
      ‖c • WithLp.fst u + c • WithLp.snd u‖ ^ 2
        = c ^ 2 * ‖WithLp.fst u + WithLp.snd u‖ ^ 2 := by
    rw [← smul_add, norm_smul, hcnorm]
    ring
  have h2 :
      ‖c • WithLp.fst u - c • WithLp.snd u‖ ^ 2
        = c ^ 2 * ‖WithLp.fst u - WithLp.snd u‖ ^ 2 := by
    rw [← smul_sub, norm_smul, hcnorm]
    ring
  have hsq :
      ‖InfoGeometry.Krein.to_doubled
          (c • WithLp.fst u + c • WithLp.snd u)
          (c • WithLp.fst u - c • WithLp.snd u)‖ ^ 2
        = ‖u‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    simp only [fst_to_doubled, snd_to_doubled]
    rw [h1, h2, hc2]
    nlinarith [hpar]
  have hnonneg1 :
      0 ≤ ‖InfoGeometry.Krein.to_doubled
            (c • WithLp.fst u + c • WithLp.snd u)
            (c • WithLp.fst u - c • WithLp.snd u)‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖u‖ := norm_nonneg _
  nlinarith [hsq, hnonneg1, hnonneg2]

noncomputable def rotation45 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E ≃ₗᵢ[ℝ] NeutralSpace E where
  toFun u := by
    let c : ℝ := 1 / Real.sqrt 2
    exact InfoGeometry.Krein.to_doubled
      (c • WithLp.fst u + c • WithLp.snd u)
      (c • WithLp.fst u - c • WithLp.snd u)
  invFun v := by
    let c : ℝ := 1 / Real.sqrt 2
    exact InfoGeometry.Krein.to_doubled
      (c • WithLp.fst v + c • WithLp.snd v)
      (c • WithLp.fst v - c • WithLp.snd v)
  left_inv := by
    intro u
    let c : ℝ := 1 / Real.sqrt 2
    have hc2 : c * c = (1 / 2 : ℝ) := by
      simpa [c, pow_two] using (one_div_sqrt_two_sq)
    have hsum : c * c + c * c = (1 : ℝ) := by
      nlinarith [hc2]
    apply InfoGeometry.Krein.DoubledSpace.ext
    · change
        c • (c • WithLp.fst u + c • WithLp.snd u) +
          c • (c • WithLp.fst u - c • WithLp.snd u) = WithLp.fst u
      calc
        c • (c • WithLp.fst u + c • WithLp.snd u) +
            c • (c • WithLp.fst u - c • WithLp.snd u)
            = (c * c + c * c) • WithLp.fst u := by
                simp [smul_add, smul_smul, sub_eq_add_neg,
                  add_left_comm, add_smul]
        _ = WithLp.fst u := by
            simp [hsum]
    · change
        c • (c • WithLp.fst u + c • WithLp.snd u) -
          c • (c • WithLp.fst u - c • WithLp.snd u) = WithLp.snd u
      calc
        c • (c • WithLp.fst u + c • WithLp.snd u) -
            c • (c • WithLp.fst u - c • WithLp.snd u)
            = (c * c + c * c) • WithLp.snd u := by
                simp [smul_add, smul_smul, sub_eq_add_neg,
                  add_left_comm, add_smul]
        _ = WithLp.snd u := by
            simp [hsum]

  right_inv := by
    intro u
    let c : ℝ := 1 / Real.sqrt 2
    have hc2 : c * c = (1 / 2 : ℝ) := by
      simpa [c, pow_two] using (one_div_sqrt_two_sq)
    have hsum : c * c + c * c = (1 : ℝ) := by
      nlinarith [hc2]
    apply InfoGeometry.Krein.DoubledSpace.ext
    · change
        c • (c • WithLp.fst u + c • WithLp.snd u) +
          c • (c • WithLp.fst u - c • WithLp.snd u) = WithLp.fst u
      calc
        c • (c • WithLp.fst u + c • WithLp.snd u) +
            c • (c • WithLp.fst u - c • WithLp.snd u)
            = (c * c + c * c) • WithLp.fst u := by
                simp [smul_add, smul_smul, sub_eq_add_neg,
                  add_left_comm, add_smul]
        _ = WithLp.fst u := by
            simp [hsum]
    · change
        c • (c • WithLp.fst u + c • WithLp.snd u) -
          c • (c • WithLp.fst u - c • WithLp.snd u) = WithLp.snd u
      calc
        c • (c • WithLp.fst u + c • WithLp.snd u) -
            c • (c • WithLp.fst u - c • WithLp.snd u)
            = (c * c + c * c) • WithLp.snd u := by
                simp [smul_add, smul_smul, sub_eq_add_neg,
                  add_left_comm, add_smul]
        _ = WithLp.snd u := by
            simp [hsum]
  map_add' := by
    intro u v
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;>
      simp [InfoGeometry.Krein.to_doubled, sub_eq_add_neg,
        smul_add, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a u
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;>
      simp [InfoGeometry.Krein.to_doubled, smul_add, smul_sub,
        smul_smul, mul_comm]
  norm_map' := by
    intro u
    simpa using rotation45_norm (E := E) u

noncomputable abbrev rotation45Isometry (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    NeutralSpace E ≃ₗᵢ[ℝ] DoubledSpace E :=
  (rotation45 (E := E)).symm

noncomputable abbrev rotation45ContinuousLinearEquiv
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    NeutralSpace E ≃L[ℝ] DoubledSpace E :=
  (rotation45Isometry (E := E)).toContinuousLinearEquiv

/-- Keep this only if you actually transport the Krein structure to `NeutralSpace`.
With the current alias model, the 45° map is not a Krein equivalence. -/

noncomputable def neutralLift (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    NeutralSpace E →L[ℝ] NeutralSpace E :=
  ((rotation45 (E := E)).toLinearIsometry.toContinuousLinearMap).comp
    (A.comp ((rotation45 (E := E)).symm.toLinearIsometry.toContinuousLinearMap))

@[simp] lemma neutralLift_apply (A : DoubledSpace E →L[ℝ] DoubledSpace E) (u : NeutralSpace E) :
    neutralLift (E := E) A u = (rotation45 (E := E)) (A ((rotation45 (E := E)).symm u)) := rfl

end NeutralSpace

end InfoGeometry.Krein
