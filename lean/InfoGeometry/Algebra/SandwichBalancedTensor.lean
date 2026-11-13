/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SandwichLocalizationStar
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.TransferInstance

/-!
# The balanced tensor description of two-sided localization

The scalar centralizer may be noncommutative. Accordingly the ambient tensor
products are native tensor products over `ℤ`, and balancing over the entire
centralizer is imposed by a native submodule quotient. The resulting quotient
is explicitly equivalent to the two-sided additive direct limit.

Both directions are constructed. Compatibility of the inverse uses the
existing central-power bonding equations and never cancels a denominator.
The equivalence therefore also covers singular denominators and their
saturated quotient. No multiplication on the sandwich space is asserted.
-/

namespace InfoGeometry.Algebra.SandwichLocalization.BalancedTensor

open scoped TensorProduct

variable {B : Type*} [Ring B]

/-- The unrestricted threefold integer tensor product. -/
abbrev Total (s : B) := (Scalars s ⊗[ℤ] B) ⊗[ℤ] Scalars s

/-- Both balancing relations, for every element of the actual centralizer. -/
noncomputable def relations (s : B) : Submodule ℤ (Total s) :=
  Submodule.span ℤ {t |
    (∃ (q r : Scalars s) (c : Centralizer s) (x : B),
      t = ((q * CentralPowerLocalization.of (denominator s) c) ⊗ₜ[ℤ] x) ⊗ₜ[ℤ] r -
        (q ⊗ₜ[ℤ] ((c : B) * x)) ⊗ₜ[ℤ] r) ∨
    (∃ (q r : Scalars s) (c : Centralizer s) (x : B),
      t = (q ⊗ₜ[ℤ] (x * (c : B))) ⊗ₜ[ℤ] r -
        (q ⊗ₜ[ℤ] x) ⊗ₜ[ℤ] (CentralPowerLocalization.of (denominator s) c * r))}

/-- The native integer-module quotient imposing noncommutative balancing. -/
abbrev Balanced (s : B) := Total s ⧸ relations s

/-- The class of an elementary threefold tensor. -/
noncomputable def pure (s : B) (q : Scalars s) (x : B) (r : Scalars s) : Balanced s :=
  (relations s).mkQ ((q ⊗ₜ[ℤ] x) ⊗ₜ[ℤ] r)

/-- A scalar on the right of the first factor acts on the left of the numerator. -/
theorem balance_left (s : B) (q r : Scalars s) (c : Centralizer s) (x : B) :
    pure s (q * CentralPowerLocalization.of (denominator s) c) x r =
      pure s q ((c : B) * x) r := by
  apply (Submodule.Quotient.eq (relations s)).mpr
  exact Submodule.subset_span (Or.inl ⟨q, r, c, x, rfl⟩)

/-- A scalar on the right of the numerator moves to the left of the last factor. -/
theorem balance_right (s : B) (q r : Scalars s) (c : Centralizer s) (x : B) :
    pure s q (x * (c : B)) r =
      pure s q x (CentralPowerLocalization.of (denominator s) c * r) := by
  apply (Submodule.Quotient.eq (relations s)).mpr
  exact Submodule.subset_span (Or.inr ⟨q, r, c, x, rfl⟩)

private noncomputable def rightLinear (s : B) (q : Scalars s) (x : B) :
    Scalars s →ₗ[ℤ] Space s :=
  ({ toFun := fun r => q • (MulOpposite.op r • of s x)
     map_zero' := by
       change q • ((0 : (Scalars s)ᵐᵒᵖ) • of s x) = 0
       rw [zero_smul, smul_zero]
     map_add' := fun r t => by
       change q • ((MulOpposite.op r + MulOpposite.op t) • of s x) = _
       rw [add_smul, smul_add] } : Scalars s →+ Space s).toIntLinearMap

private noncomputable def middleLinear (s : B) (q : Scalars s) :
    B →ₗ[ℤ] Scalars s →ₗ[ℤ] Space s :=
  ({ toFun := rightLinear s q
     map_zero' := by
       ext r
       change q • (MulOpposite.op r • of s 0) = 0
       rw [map_zero, smul_zero, smul_zero]
     map_add' := fun x y => by
       ext r
       change q • (MulOpposite.op r • of s (x + y)) =
         q • (MulOpposite.op r • of s x) + q • (MulOpposite.op r • of s y)
       rw [map_add, smul_add, smul_add] } :
    B →+ Scalars s →ₗ[ℤ] Space s).toIntLinearMap

private noncomputable def tripleLinear (s : B) :
    Scalars s →ₗ[ℤ] B →ₗ[ℤ] Scalars s →ₗ[ℤ] Space s :=
  ({ toFun := middleLinear s
     map_zero' := by
       ext x r
       change (0 : Scalars s) • (MulOpposite.op r • of s x) = 0
       rw [zero_smul]
     map_add' := fun q t => by
       ext x r
       change (q + t) • (MulOpposite.op r • of s x) =
         q • (MulOpposite.op r • of s x) + t • (MulOpposite.op r • of s x)
       rw [add_smul] } :
    Scalars s →+ B →ₗ[ℤ] Scalars s →ₗ[ℤ] Space s).toIntLinearMap

/-- The actual linear evaluation map before centralizer balancing. -/
noncomputable def evaluateTensor (s : B) : Total s →ₗ[ℤ] Space s :=
  TensorProduct.lift (TensorProduct.lift (tripleLinear s))

@[simp] theorem evaluateTensor_tmul (s : B) (q r : Scalars s) (x : B) :
    evaluateTensor s ((q ⊗ₜ[ℤ] x) ⊗ₜ[ℤ] r) = q • (MulOpposite.op r • of s x) := rfl

private theorem scalar_of_left (s : B) (c : Centralizer s) (x : B) :
    CentralPowerLocalization.of (denominator s) c • of s x = of s ((c : B) * x) := by
  change CentralPowerLocalization.of (denominator s) c • repr s 0 x 0 =
    repr s 0 ((c : B) * x) 0
  simpa only [CentralPowerLocalization.repr_zero, Nat.zero_add, Nat.add_zero] using
    left_smul_repr s 0 0 0 c x

private theorem scalar_of_right (s : B) (c : Centralizer s) (x : B) :
    MulOpposite.op (CentralPowerLocalization.of (denominator s) c) • of s x =
      of s (x * (c : B)) := by
  change MulOpposite.op (CentralPowerLocalization.of (denominator s) c) • repr s 0 x 0 =
    repr s 0 (x * (c : B)) 0
  simpa only [CentralPowerLocalization.repr_zero, Nat.zero_add, Nat.add_zero] using
    right_smul_repr s 0 0 0 c x

/-- Evaluation kills every balancing generator, hence their full integer span. -/
theorem relations_le_ker_evaluateTensor (s : B) :
    relations s ≤ LinearMap.ker (evaluateTensor s) := by
  apply Submodule.span_le.mpr
  rintro t (⟨q, r, c, x, rfl⟩ | ⟨q, r, c, x, rfl⟩)
  · change evaluateTensor s (_ - _) = 0
    rw [map_sub, evaluateTensor_tmul, evaluateTensor_tmul, sub_eq_zero]
    rw [mul_smul,
      smul_comm (CentralPowerLocalization.of (denominator s) c) (MulOpposite.op r),
      scalar_of_left]
  · change evaluateTensor s (_ - _) = 0
    rw [map_sub, evaluateTensor_tmul, evaluateTensor_tmul, sub_eq_zero]
    rw [← scalar_of_right s c x]
    change q • (MulOpposite.op r •
        (MulOpposite.op (CentralPowerLocalization.of (denominator s) c) • of s x)) =
      q • ((MulOpposite.op r *
        MulOpposite.op (CentralPowerLocalization.of (denominator s) c)) • of s x)
    rw [mul_smul]

/-- The constructed map out of the balanced quotient. -/
noncomputable def evaluate (s : B) : Balanced s →ₗ[ℤ] Space s :=
  (relations s).liftQ (evaluateTensor s) (relations_le_ker_evaluateTensor s)

@[simp] theorem evaluate_pure (s : B) (q r : Scalars s) (x : B) :
    evaluate s (pure s q x r) = q • (MulOpposite.op r • of s x) := rfl

theorem evaluate_pure_repr (s : B) (k l : ℕ) (u v : Centralizer s) (x : B) :
    evaluate s (pure s (CentralPowerLocalization.repr (denominator s) k u) x
        (CentralPowerLocalization.repr (denominator s) l v)) =
      repr s k ((u : B) * x * (v : B)) l := by
  rw [evaluate_pure]
  change CentralPowerLocalization.repr (denominator s) k u •
      (MulOpposite.op (CentralPowerLocalization.repr (denominator s) l v) • repr s 0 x 0) =
    repr s k ((u : B) * x * (v : B)) l
  simpa only [Nat.zero_add] using bimodule_repr s k l 0 0 u v x

private theorem repr_one_mul_of (s : B) (k : ℕ) (u : Centralizer s) :
    CentralPowerLocalization.repr (denominator s) k 1 *
        CentralPowerLocalization.of (denominator s) u =
      CentralPowerLocalization.repr (denominator s) k u := by
  rw [← CentralPowerLocalization.repr_zero (denominator s) u,
    CentralPowerLocalization.repr_mul, Nat.add_zero, one_mul]

private theorem of_mul_repr_one (s : B) (k : ℕ) (u : Centralizer s) :
    CentralPowerLocalization.of (denominator s) u *
        CentralPowerLocalization.repr (denominator s) k 1 =
      CentralPowerLocalization.repr (denominator s) k u := by
  rw [← CentralPowerLocalization.repr_zero (denominator s) u,
    CentralPowerLocalization.repr_mul, Nat.zero_add, mul_one]

private theorem left_denominator_bond (s : B) (k a : ℕ) :
    CentralPowerLocalization.repr (denominator s) (k + a) 1 *
        CentralPowerLocalization.of (denominator s) (denominator s ^ a) =
      CentralPowerLocalization.repr (denominator s) k 1 := by
  rw [repr_one_mul_of]
  simpa only [mul_one] using (CentralPowerLocalization.repr_bond (denominator s) k a 1).symm

private theorem right_denominator_bond (s : B) (l b : ℕ) :
    CentralPowerLocalization.of (denominator s) (denominator s ^ b) *
        CentralPowerLocalization.repr (denominator s) (l + b) 1 =
      CentralPowerLocalization.repr (denominator s) l 1 := by
  rw [of_mul_repr_one]
  simpa only [mul_one] using (CentralPowerLocalization.repr_bond (denominator s) l b 1).symm

/-- The actual integer-linear cocone used to construct the inverse. -/
noncomputable def inverseStage (s : B) (k l : ℕ) : B →ₗ[ℤ] Balanced s :=
  (relations s).mkQ.comp
    (((TensorProduct.mk ℤ (Scalars s ⊗[ℤ] B) (Scalars s)).flip
      (CentralPowerLocalization.repr (denominator s) l 1)).comp
      ((TensorProduct.mk ℤ (Scalars s) B)
        (CentralPowerLocalization.repr (denominator s) k 1)))

@[simp] theorem inverseStage_apply (s : B) (k l : ℕ) (x : B) :
    inverseStage s k l x = pure s (CentralPowerLocalization.repr (denominator s) k 1) x
      (CentralPowerLocalization.repr (denominator s) l 1) := rfl

/-- Compatibility follows from balancing and fraction bonds, including singular denominators. -/
theorem inverseStage_bond (s : B) (k l a b : ℕ) (x : B) :
    inverseStage s (k + a) (l + b) (s ^ a * x * s ^ b) = inverseStage s k l x := by
  simp only [inverseStage_apply]
  calc
    _ = pure s (CentralPowerLocalization.repr (denominator s) (k + a) 1) (s ^ a * x)
        (CentralPowerLocalization.of (denominator s) (denominator s ^ b) *
          CentralPowerLocalization.repr (denominator s) (l + b) 1) := by
      simpa only [Subring.coe_pow, coe_denominator] using
        balance_right s (CentralPowerLocalization.repr (denominator s) (k + a) 1)
          (CentralPowerLocalization.repr (denominator s) (l + b) 1)
          (denominator s ^ b) (s ^ a * x)
    _ = pure s
        (CentralPowerLocalization.repr (denominator s) (k + a) 1 *
          CentralPowerLocalization.of (denominator s) (denominator s ^ a)) x
        (CentralPowerLocalization.of (denominator s) (denominator s ^ b) *
          CentralPowerLocalization.repr (denominator s) (l + b) 1) := by
      simpa only [Subring.coe_pow, coe_denominator] using
        (balance_left s (CentralPowerLocalization.repr (denominator s) (k + a) 1)
          (CentralPowerLocalization.of (denominator s) (denominator s ^ b) *
            CentralPowerLocalization.repr (denominator s) (l + b) 1)
          (denominator s ^ a) x).symm
    _ = _ := by rw [left_denominator_bond, right_denominator_bond]

/-- The inverse is descended from a proved cocone on the native direct limit. -/
noncomputable def toBalanced (s : B) : Space s →ₗ[ℤ] Balanced s :=
  (additiveDesc s (fun k l => (inverseStage s k l).toAddMonoidHom)
    (inverseStage_bond s)).toIntLinearMap

@[simp] theorem toBalanced_repr (s : B) (k l : ℕ) (x : B) :
    toBalanced s (repr s k x l) =
      pure s (CentralPowerLocalization.repr (denominator s) k 1) x
        (CentralPowerLocalization.repr (denominator s) l 1) := rfl

/-- Evaluation after the constructed inverse fixes every direct-limit element. -/
theorem evaluate_toBalanced (s : B) (z : Space s) : evaluate s (toBalanced s z) = z := by
  obtain ⟨k, x, l, rfl⟩ := exists_repr s z
  rw [toBalanced_repr, evaluate_pure_repr]
  simp only [Subring.coe_one, one_mul, mul_one]

/-- The inverse after evaluation fixes every elementary balanced tensor. -/
theorem toBalanced_evaluate_pure (s : B) (q r : Scalars s) (x : B) :
    toBalanced s (evaluate s (pure s q x r)) = pure s q x r := by
  obtain ⟨k, u, rfl⟩ := CentralPowerLocalization.exists_repr (denominator s) q
  obtain ⟨l, v, rfl⟩ := CentralPowerLocalization.exists_repr (denominator s) r
  rw [evaluate_pure_repr, toBalanced_repr]
  rw [balance_right s _ _ v ((u : B) * x), ← balance_left s _ _ u x,
    repr_one_mul_of, of_mul_repr_one]

/-- Native tensor extensionality and quotient surjectivity extend that identity to the whole quotient. -/
theorem toBalanced_evaluate (s : B) (z : Balanced s) : toBalanced s (evaluate s z) = z := by
  have h : ((toBalanced s).comp (evaluate s)).comp (relations s).mkQ = (relations s).mkQ := by
    apply TensorProduct.ext_threefold
    intro q x r
    exact toBalanced_evaluate_pure s q r x
  obtain ⟨t, rfl⟩ := (relations s).mkQ_surjective z
  exact LinearMap.congr_fun h t

/-- The proved balanced tensor equivalence, with no regularity assumption. -/
noncomputable def equivalence (s : B) : Balanced s ≃ₗ[ℤ] Space s where
  __ := evaluate s
  invFun := toBalanced s
  left_inv := toBalanced_evaluate s
  right_inv := evaluate_toBalanced s

@[simp] theorem equivalence_pure (s : B) (q r : Scalars s) (x : B) :
    equivalence s (pure s q x r) = q • (MulOpposite.op r • of s x) := rfl

@[simp] theorem equivalence_symm_repr (s : B) (k l : ℕ) (x : B) :
    (equivalence s).symm (repr s k x l) =
      pure s (CentralPowerLocalization.repr (denominator s) k 1) x
        (CentralPowerLocalization.repr (denominator s) l 1) := rfl

/-- The constructed quotient equivalence transports the actual left scalar action. -/
noncomputable instance leftModule (s : B) : Module (Scalars s) (Balanced s) :=
  (equivalence s).toAddEquiv.module (Scalars s)

/-- The right action is transported as a native module over the opposite scalar ring. -/
noncomputable instance rightModule (s : B) : Module (Scalars s)ᵐᵒᵖ (Balanced s) :=
  (equivalence s).toAddEquiv.module (Scalars s)ᵐᵒᵖ

@[simp] theorem equivalence_left_smul (s : B) (q : Scalars s) (z : Balanced s) :
    equivalence s (q • z) = q • equivalence s z := by
  change equivalence s ((equivalence s).symm (q • equivalence s z)) = _
  exact (equivalence s).apply_symm_apply _

@[simp] theorem equivalence_right_smul (s : B) (r : (Scalars s)ᵐᵒᵖ) (z : Balanced s) :
    equivalence s (r • z) = r • equivalence s z := by
  change equivalence s ((equivalence s).symm (r • equivalence s z)) = _
  exact (equivalence s).apply_symm_apply _

/-- The two transported actions commute on the entire balanced quotient. -/
noncomputable instance scalarActionsCommute (s : B) :
    SMulCommClass (Scalars s) (Scalars s)ᵐᵒᵖ (Balanced s) where
  smul_comm q r z := by
    apply (equivalence s).injective
    simp only [equivalence_left_smul, equivalence_right_smul]
    exact smul_comm q r (equivalence s z)

/-- The transported left action is exactly multiplication of the first tensor factor. -/
theorem left_smul_pure (s : B) (q a b : Scalars s) (x : B) :
    q • pure s a x b = pure s (q * a) x b := by
  apply (equivalence s).injective
  simp only [equivalence_left_smul, equivalence_pure, mul_smul]

/-- The transported right action is exactly ordered multiplication of the last tensor factor. -/
theorem right_smul_pure (s : B) (q a b : Scalars s) (x : B) :
    MulOpposite.op q • pure s a x b = pure s a x (b * q) := by
  apply (equivalence s).injective
  rw [equivalence_right_smul, equivalence_pure, equivalence_pure]
  change MulOpposite.op q • (a • (MulOpposite.op b • of s x)) =
    a • ((MulOpposite.op q * MulOpposite.op b) • of s x)
  rw [mul_smul, smul_comm a (MulOpposite.op q)]

/-- The same explicit equivalence is linear for the actual left scalar modules. -/
noncomputable def equivalenceLeft (s : B) : Balanced s ≃ₗ[Scalars s] Space s where
  __ := (equivalence s).toAddEquiv
  map_smul' := equivalence_left_smul s

/-- It is simultaneously linear for the right modules, expressed with opposite scalars. -/
noncomputable def equivalenceRight (s : B) :
    Balanced s ≃ₗ[(Scalars s)ᵐᵒᵖ] Space s where
  __ := (equivalence s).toAddEquiv
  map_smul' := equivalence_right_smul s

section Star

variable [StarRing B] (s : B) [Fact (star s = s)]

/-- The balanced quotient inherits the actual swapped involution through the proved equivalence. -/
noncomputable instance balancedStar : Star (Balanced s) where
  star z := (equivalence s).symm (star (equivalence s z))

@[simp] theorem equivalence_star (z : Balanced s) :
    equivalence s (star z) = star (equivalence s z) := by
  change equivalence s ((equivalence s).symm (star (equivalence s z))) = _
  exact (equivalence s).apply_symm_apply _

noncomputable instance balancedStarAddMonoid : StarAddMonoid (Balanced s) where
  star_involutive z := by
    apply (equivalence s).injective
    simp only [equivalence_star, star_star]
  star_add z w := by
    apply (equivalence s).injective
    simp only [equivalence_star, map_add, star_add]

/-- On elementary tensors the actual involution reverses all three factors. -/
theorem star_pure (q r : Scalars s) (x : B) :
    star (pure s q x r) = pure s (star r) (star x) (star q) := by
  apply (equivalence s).injective
  simp only [equivalence_star, equivalence_pure,
    InfoGeometry.Algebra.SandwichLocalization.star_left_smul,
    InfoGeometry.Algebra.SandwichLocalization.star_right_smul,
    InfoGeometry.Algebra.SandwichLocalization.star_of]
  exact (smul_comm (star r) (MulOpposite.op (star q)) (of s (star x))).symm

/-- Star exchanges the two native scalar actions on the balanced quotient. -/
theorem star_left_smul (q : Scalars s) (z : Balanced s) :
    star (q • z) = MulOpposite.op (star q) • star z := by
  apply (equivalence s).injective
  simp only [equivalence_star, equivalence_left_smul, equivalence_right_smul,
    InfoGeometry.Algebra.SandwichLocalization.star_left_smul]

theorem star_right_smul (q : Scalars s) (z : Balanced s) :
    star (MulOpposite.op q • z) = star q • star z := by
  apply (equivalence s).injective
  simp only [equivalence_star, equivalence_left_smul, equivalence_right_smul,
    InfoGeometry.Algebra.SandwichLocalization.star_right_smul]

end Star

end InfoGeometry.Algebra.SandwichLocalization.BalancedTensor
