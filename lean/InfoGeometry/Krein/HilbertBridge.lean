import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# InfoGeometry.Krein.HilbertBridge

Hardened Hilbert/neutral bridge API over type-distinct wrappers of `DoubledSpace`.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev HilbertDoubled (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  ULift.{u} (DoubledSpace E)

namespace HilbertDoubled

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable instance : NormedAddCommGroup (HilbertDoubled E) := inferInstance
noncomputable instance : NormedSpace ℝ (HilbertDoubled E) := inferInstance
noncomputable instance : CompleteSpace (HilbertDoubled E) := inferInstance

instance : Coe (HilbertDoubled E) (DoubledSpace E) := ⟨ULift.down⟩
instance : CoeTC (HilbertDoubled E) (WithLp (2 : ENNReal) (E × E)) := ⟨fun u => (u : DoubledSpace E)⟩
instance : CoeTC (WithLp (2 : ENNReal) (E × E)) (HilbertDoubled E) := ⟨fun u => ⟨u⟩⟩

noncomputable instance : Inner ℝ (HilbertDoubled E) where
  inner u v := ⟪((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)),
    (((v : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))⟫_ℝ

noncomputable instance : InnerProductSpace ℝ (HilbertDoubled E) where
  norm_sq_eq_re_inner := by
    intro u
    change ‖((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E))‖ ^ 2 =
      RCLike.re ⟪((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)),
        (((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))⟫_ℝ
    simp
  conj_inner_symm := by
    intro u v
    exact
      (inner_conj_symm (𝕜 := ℝ)
        (((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))
        (((v : DoubledSpace E) : WithLp (2 : ENNReal) (E × E))))
  add_left := by
    intro u v w
    simpa using
      (inner_add_left
        (((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))
        (((v : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))
        (((w : DoubledSpace E) : WithLp (2 : ENNReal) (E × E))))
  smul_left := by
    intro u v r
    simpa using
      (real_inner_smul_left
        (((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))
        (((v : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))
        r)

noncomputable instance : KreinSpace (HilbertDoubled E) where
  J :=
    { toFun := fun u => ⟨KreinSpace.J (H := DoubledSpace E) (u : DoubledSpace E)⟩
      invFun := fun u => ⟨KreinSpace.J (H := DoubledSpace E) (u : DoubledSpace E)⟩
      left_inv := by
        intro u
        apply ULift.ext
        simpa using (KreinSpace.J_invol (H := DoubledSpace E) (u : DoubledSpace E))
      right_inv := by
        intro u
        apply ULift.ext
        simpa using (KreinSpace.J_invol (H := DoubledSpace E) (u : DoubledSpace E))
      map_add' := by
        intro u v
        apply ULift.ext
        simp
      map_smul' := by
        intro a u
        apply ULift.ext
        simp
      norm_map' := by
        intro u
        exact (KreinSpace.J (H := DoubledSpace E)).norm_map (u : DoubledSpace E) }
  J_invol := by
    intro u
    apply ULift.ext
    simpa using (KreinSpace.J_invol (H := DoubledSpace E) (u : DoubledSpace E))
  J_selfAdj := by
    intro u v
    simpa using
      (KreinSpace.J_selfAdj (H := DoubledSpace E)
        ((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E))
        (((v : DoubledSpace E) : WithLp (2 : ENNReal) (E × E))))

abbrev val (u : HilbertDoubled E) : WithLp (2 : ENNReal) (E × E) := (u : DoubledSpace E)
abbrev ofLp (u : HilbertDoubled E) : E × E := WithLp.ofLp (u : DoubledSpace E)
abbrev ofWithLp (u : WithLp (2 : ENNReal) (E × E)) : HilbertDoubled E := ⟨u⟩
abbrev toLp (v : E × E) : HilbertDoubled E := ⟨WithLp.toLp 2 v⟩

lemma val_ofWithLp (u : WithLp (2 : ENNReal) (E × E)) : (ofWithLp (E := E) u).val = u := rfl
lemma ofWithLp_val (u : HilbertDoubled E) : ofWithLp (E := E) u.val = u := by
  cases u
  rfl
@[simp] lemma val_toLp (v : E × E) : (toLp (E := E) v).val = WithLp.toLp 2 v := rfl
@[simp] lemma coe_toLp (v : E × E) : ((toLp (E := E) v : HilbertDoubled E) : DoubledSpace E) = WithLp.toLp 2 v := rfl
@[simp] lemma ofLp_toLp (v : E × E) : ofLp (toLp (E := E) v) = v := rfl
@[simp] lemma toLp_ofLp (u : HilbertDoubled E) : toLp (E := E) (ofLp u) = u := by
  cases u
  rfl
@[simp] lemma fst_ofWithLp (u : WithLp (2 : ENNReal) (E × E)) :
    WithLp.fst (ofWithLp (E := E) u).val = WithLp.fst u := rfl
@[simp] lemma snd_ofWithLp (u : WithLp (2 : ENNReal) (E × E)) :
    WithLp.snd (ofWithLp (E := E) u).val = WithLp.snd u := rfl
@[simp] lemma fst_toLp (v : E × E) : WithLp.fst (toLp (E := E) v).val = v.1 := rfl
@[simp] lemma snd_toLp (v : E × E) : WithLp.snd (toLp (E := E) v).val = v.2 := rfl

@[ext] lemma ext {u v : HilbertDoubled E} (h : u.val = v.val) : u = v := by
  cases u
  cases v
  simp at h
  cases h
  rfl

noncomputable def ofDoubledLIE : DoubledSpace E ≃ₗᵢ[ℝ] HilbertDoubled E where
  toLinearEquiv :=
    { toFun := fun u => ⟨u⟩
      invFun := fun u => (u : DoubledSpace E)
      left_inv := by
        intro u
        rfl
      right_inv := by
        intro u
        apply ext
        rfl
      map_add' := by
        intro u v
        rfl
      map_smul' := by
        intro a u
        rfl }
  norm_map' := by
    intro u
    rfl

noncomputable abbrev toDoubledLIE : HilbertDoubled E ≃ₗᵢ[ℝ] DoubledSpace E :=
  (ofDoubledLIE (E := E)).symm

noncomputable abbrev ofDoubledContinuousLinearEquiv : DoubledSpace E ≃L[ℝ] HilbertDoubled E :=
  (ofDoubledLIE (E := E)).toContinuousLinearEquiv

noncomputable abbrev toDoubledContinuousLinearEquiv : HilbertDoubled E ≃L[ℝ] DoubledSpace E :=
  (toDoubledLIE (E := E)).toContinuousLinearEquiv

@[simp] lemma ofDoubledLIE_apply (u : DoubledSpace E) :
    ofDoubledLIE (E := E) u = ⟨u⟩ := rfl

@[simp] lemma toDoubledLIE_apply (u : HilbertDoubled E) :
    toDoubledLIE (E := E) u = (u : DoubledSpace E) := rfl

@[simp] lemma ofDoubledContinuousLinearEquiv_apply (u : DoubledSpace E) :
    ofDoubledContinuousLinearEquiv (E := E) u = ⟨u⟩ := rfl

@[simp] lemma toDoubledContinuousLinearEquiv_apply (u : HilbertDoubled E) :
    toDoubledContinuousLinearEquiv (E := E) u = (u : DoubledSpace E) := rfl

end HilbertDoubled

/--
Neutral carrier wrapper used to keep the Hessian/neutral chart type-distinct from the diagonal
`DoubledSpace` carrier.
-/
abbrev NeutralSpace (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  ULift.{u} (DoubledSpace E)

namespace NeutralSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable instance : NormedAddCommGroup (NeutralSpace E) := inferInstance
noncomputable instance : NormedSpace ℝ (NeutralSpace E) := inferInstance
noncomputable instance : CompleteSpace (NeutralSpace E) := inferInstance

instance : Coe (NeutralSpace E) (DoubledSpace E) := ⟨ULift.down⟩

noncomputable instance : Inner ℝ (NeutralSpace E) where
  inner u v := ⟪((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)),
    (((v : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))⟫_ℝ

noncomputable instance : InnerProductSpace ℝ (NeutralSpace E) where
  norm_sq_eq_re_inner := by
    intro u
    change ‖((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E))‖ ^ 2 =
      RCLike.re ⟪((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)),
        (((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))⟫_ℝ
    simp
  conj_inner_symm := by
    intro u v
    exact
      (inner_conj_symm (𝕜 := ℝ)
        (((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))
        (((v : DoubledSpace E) : WithLp (2 : ENNReal) (E × E))))
  add_left := by
    intro u v w
    simpa using
      (inner_add_left
        (((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))
        (((v : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))
        (((w : DoubledSpace E) : WithLp (2 : ENNReal) (E × E))))
  smul_left := by
    intro u v r
    simpa using
      (real_inner_smul_left
        (((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))
        (((v : DoubledSpace E) : WithLp (2 : ENNReal) (E × E)))
        r)

noncomputable instance : KreinSpace (NeutralSpace E) where
  J :=
    { toFun := fun u => ⟨KreinSpace.J (H := DoubledSpace E) (u : DoubledSpace E)⟩
      invFun := fun u => ⟨KreinSpace.J (H := DoubledSpace E) (u : DoubledSpace E)⟩
      left_inv := by
        intro u
        apply ULift.ext
        simpa using (KreinSpace.J_invol (H := DoubledSpace E) (u : DoubledSpace E))
      right_inv := by
        intro u
        apply ULift.ext
        simpa using (KreinSpace.J_invol (H := DoubledSpace E) (u : DoubledSpace E))
      map_add' := by
        intro u v
        apply ULift.ext
        simp
      map_smul' := by
        intro a u
        apply ULift.ext
        simp
      norm_map' := by
        intro u
        exact (KreinSpace.J (H := DoubledSpace E)).norm_map (u : DoubledSpace E) }
  J_invol := by
    intro u
    apply ULift.ext
    simpa using (KreinSpace.J_invol (H := DoubledSpace E) (u : DoubledSpace E))
  J_selfAdj := by
    intro u v
    simpa using
      (KreinSpace.J_selfAdj (H := DoubledSpace E)
        ((u : DoubledSpace E) : WithLp (2 : ENNReal) (E × E))
        (((v : DoubledSpace E) : WithLp (2 : ENNReal) (E × E))))

abbrev val (u : NeutralSpace E) : WithLp (2 : ENNReal) (E × E) := (u : DoubledSpace E)
abbrev ofLp (u : NeutralSpace E) : E × E := WithLp.ofLp (u : DoubledSpace E)
abbrev ofWithLp (u : WithLp (2 : ENNReal) (E × E)) : NeutralSpace E := ⟨u⟩
abbrev toLp (v : E × E) : NeutralSpace E := ⟨WithLp.toLp 2 v⟩

lemma val_ofWithLp (u : WithLp (2 : ENNReal) (E × E)) : (ofWithLp (E := E) u).val = u := rfl
lemma ofWithLp_val (u : NeutralSpace E) : ofWithLp (E := E) u.val = u := by
  cases u
  rfl
@[simp] lemma val_toLp (v : E × E) : (toLp (E := E) v).val = WithLp.toLp 2 v := rfl
lemma fst_coe (u : NeutralSpace E) : WithLp.fst (u : DoubledSpace E) = u.ofLp.1 := rfl
lemma snd_coe (u : NeutralSpace E) : WithLp.snd (u : DoubledSpace E) = u.ofLp.2 := rfl
lemma fst_val (u : NeutralSpace E) : WithLp.fst u.val = u.ofLp.1 := rfl
lemma snd_val (u : NeutralSpace E) : WithLp.snd u.val = u.ofLp.2 := rfl
@[simp] lemma fst_ofWithLp (u : WithLp (2 : ENNReal) (E × E)) :
    WithLp.fst (ofWithLp (E := E) u).val = WithLp.fst u := rfl
@[simp] lemma snd_ofWithLp (u : WithLp (2 : ENNReal) (E × E)) :
    WithLp.snd (ofWithLp (E := E) u).val = WithLp.snd u := rfl
@[simp] lemma fst_toLp (v : E × E) : WithLp.fst (toLp (E := E) v).val = v.1 := rfl
@[simp] lemma snd_toLp (v : E × E) : WithLp.snd (toLp (E := E) v).val = v.2 := rfl

@[ext] lemma ext {u v : NeutralSpace E} (h : u.val = v.val) : u = v := by
  cases u
  cases v
  simp at h
  cases h
  rfl

noncomputable abbrev neutralJ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    NeutralSpace E ≃ₗᵢ[ℝ] NeutralSpace E :=
  KreinSpace.J (H := NeutralSpace E)

@[simp] lemma neutralJ_eq_J :
    neutralJ (E := E) = KreinSpace.J (H := NeutralSpace E) := rfl

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

noncomputable def rotation45 (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E ≃ₗᵢ[ℝ] NeutralSpace E where
  toFun u := by
    let c : ℝ := 1 / Real.sqrt 2
    exact NeutralSpace.ofWithLp (E := E) <|
      InfoGeometry.Krein.to_doubled
      (c • WithLp.fst u + c • WithLp.snd u)
      (c • WithLp.fst u - c • WithLp.snd u)
  invFun v := by
    let c : ℝ := 1 / Real.sqrt 2
    exact InfoGeometry.Krein.to_doubled
      (c • WithLp.fst (v : DoubledSpace E) + c • WithLp.snd (v : DoubledSpace E))
      (c • WithLp.fst (v : DoubledSpace E) - c • WithLp.snd (v : DoubledSpace E))
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
    apply NeutralSpace.ext
    apply InfoGeometry.Krein.DoubledSpace.ext
    · change
        c • (c • WithLp.fst (u : DoubledSpace E) + c • WithLp.snd (u : DoubledSpace E)) +
          c • (c • WithLp.fst (u : DoubledSpace E) - c • WithLp.snd (u : DoubledSpace E)) =
            WithLp.fst (u : DoubledSpace E)
      calc
        c • (c • WithLp.fst (u : DoubledSpace E) + c • WithLp.snd (u : DoubledSpace E)) +
            c • (c • WithLp.fst (u : DoubledSpace E) - c • WithLp.snd (u : DoubledSpace E))
            = (c * c + c * c) • WithLp.fst (u : DoubledSpace E) := by
                simp [smul_add, smul_smul, sub_eq_add_neg,
                  add_left_comm, add_smul]
        _ = WithLp.fst (u : DoubledSpace E) := by
            simp [hsum]
    · change
        c • (c • WithLp.fst (u : DoubledSpace E) + c • WithLp.snd (u : DoubledSpace E)) -
          c • (c • WithLp.fst (u : DoubledSpace E) - c • WithLp.snd (u : DoubledSpace E)) =
            WithLp.snd (u : DoubledSpace E)
      calc
        c • (c • WithLp.fst (u : DoubledSpace E) + c • WithLp.snd (u : DoubledSpace E)) -
            c • (c • WithLp.fst (u : DoubledSpace E) - c • WithLp.snd (u : DoubledSpace E))
            = (c * c + c * c) • WithLp.snd (u : DoubledSpace E) := by
                simp [smul_add, smul_smul, sub_eq_add_neg,
                  add_left_comm, add_smul]
        _ = WithLp.snd (u : DoubledSpace E) := by
            simp [hsum]
  map_add' := by
    intro u v
    apply NeutralSpace.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;>
      simp [InfoGeometry.Krein.to_doubled, sub_eq_add_neg,
        smul_add, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a u
    apply NeutralSpace.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;>
      simp [InfoGeometry.Krein.to_doubled, smul_add, smul_sub,
        smul_smul, mul_comm]
  norm_map' := by
    intro u
    simpa using rotation45_norm (E := E) u

noncomputable abbrev rotation45Isometry (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    NeutralSpace E ≃ₗᵢ[ℝ] DoubledSpace E :=
  (rotation45 (E := E)).symm

noncomputable abbrev rotation45ContinuousLinearEquiv
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    NeutralSpace E ≃L[ℝ] DoubledSpace E :=
  (rotation45Isometry (E := E)).toContinuousLinearEquiv

noncomputable abbrev rotation45ToHilbert
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    NeutralSpace E ≃ₗᵢ[ℝ] HilbertDoubled E :=
  (rotation45Isometry (E := E)).trans (HilbertDoubled.ofDoubledLIE (E := E))

noncomputable abbrev rotation45ToHilbertContinuousLinearEquiv
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    NeutralSpace E ≃L[ℝ] HilbertDoubled E :=
  (rotation45ToHilbert (E := E)).toContinuousLinearEquiv

@[simp] lemma rotation45ToHilbert_apply (u : NeutralSpace E) :
    rotation45ToHilbert (E := E) u =
      HilbertDoubled.ofDoubledLIE (E := E) (rotation45Isometry (E := E) u) := rfl

@[simp] lemma rotation45ToHilbertContinuousLinearEquiv_apply (u : NeutralSpace E) :
    rotation45ToHilbertContinuousLinearEquiv (E := E) u =
      HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E) (rotation45Isometry (E := E) u) := rfl

@[simp] lemma rotation45_symm_toLp_pair
    (x ξ : E) :
    ((rotation45 (E := E)).symm) (toLp (E := E) (x, ξ)) =
      let c : ℝ := 1 / Real.sqrt 2
      InfoGeometry.Krein.to_doubled (c • x + c • ξ) (c • x - c • ξ) := rfl

/-- Keep this only if you actually transport the Krein structure to `NeutralSpace`.
In the hardened wrapper model, the 45° map is a Hilbert/linear transport bridge; a full
`KreinEquiv` statement would require additional structure-preservation proofs. -/

noncomputable def neutralLift (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    NeutralSpace E →L[ℝ] NeutralSpace E :=
  ((rotation45 (E := E)).toLinearIsometry.toContinuousLinearMap).comp
    (A.comp ((rotation45 (E := E)).symm.toLinearIsometry.toContinuousLinearMap))

@[simp] lemma neutralLift_apply (A : DoubledSpace E →L[ℝ] DoubledSpace E) (u : NeutralSpace E) :
    neutralLift (E := E) A u = (rotation45 (E := E)) (A ((rotation45 (E := E)).symm u)) := rfl

end NeutralSpace

end InfoGeometry.Krein
