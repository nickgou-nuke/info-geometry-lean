/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.Physics.ConnesCyclicCohomology

/-!
# Universal first-order forms for a noncommutative ring

The universal one-form carrier is the kernel of multiplication
`A ⊗[ℤ] A →ₗ[ℤ] A`.  Its universal differential is
`d a = 1 ⊗ a - a ⊗ 1`.  This is the carrier-level construction needed before
specializing a derivation into a geometric one-form representation.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms

open scoped TensorProduct

variable (A : Type*) [Ring A]

/-- Multiplication on a possibly noncommutative ring, curried as a
`ℤ`-bilinear map. -/
def multiplicationBilinear : A →ₗ[ℤ] A →ₗ[ℤ] A where
  toFun x :=
    { toFun := fun y => x * y
      map_add' := by intro y z; exact mul_add x y z
      map_smul' := by
        intro n y
        exact map_zsmul (AddMonoidHom.mk' (fun z : A => x * z) (fun z w => mul_add x z w)) n y }
  map_add' := by
    intro x y
    ext z
    exact add_mul x y z
  map_smul' := by
    intro n x
    apply LinearMap.ext
    intro y
    change (n • x) * y = n • (x * y)
    exact map_zsmul (AddMonoidHom.mk' (fun z : A => z * y) (fun z w => add_mul z w y)) n x

/-- Multiplication as a linear map out of the noncommutative tensor product. -/
def multiplicationTensor : A ⊗[ℤ] A →ₗ[ℤ] A :=
  TensorProduct.lift (multiplicationBilinear A)

@[simp] theorem multiplicationTensor_tmul (x y : A) :
    multiplicationTensor A (x ⊗ₜ[ℤ] y) = x * y :=
  rfl

/-- Universal first-order forms of `A`, represented as the kernel of the
product map. -/
abbrev OneForms := LinearMap.ker (multiplicationTensor A)

/-- The universal differential `a ↦ 1 ⊗ a - a ⊗ 1`, valued in the
kernel of multiplication. -/
def differential (a : A) : OneForms A := by
  refine ⟨(1 : A) ⊗ₜ[ℤ] a - a ⊗ₜ[ℤ] (1 : A), ?_⟩
  simp [OneForms, multiplicationTensor_tmul]

@[simp] theorem differential_val (a : A) :
    (differential A a).val = (1 : A) ⊗ₜ[ℤ] a - a ⊗ₜ[ℤ] (1 : A) :=
  rfl

/-- The raw tensor representing `a · dᵤ b` in the universal bimodule of
one-forms. -/
def leftDifferentialTensor (a b : A) : A ⊗[ℤ] A :=
  a ⊗ₜ[ℤ] b - (a * b) ⊗ₜ[ℤ] (1 : A)

/-- The raw tensor representing `(dᵤ a) · b` in the universal bimodule of
one-forms. -/
def rightDifferentialTensor (a b : A) : A ⊗[ℤ] A :=
  (1 : A) ⊗ₜ[ℤ] (a * b) - a ⊗ₜ[ℤ] b

/-- The one-form represented by `a · dᵤ b`. -/
def leftDifferentialForm (a b : A) : OneForms A :=
  ⟨leftDifferentialTensor A a b, by
    simp [OneForms, leftDifferentialTensor, multiplicationTensor_tmul]⟩

/-- Normalize a tensor into the kernel of multiplication by subtracting its
product tensored with the unit. -/
def normalizeTensor (x : A ⊗[ℤ] A) : OneForms A :=
  ⟨x - (multiplicationTensor A x) ⊗ₜ[ℤ] (1 : A), by
    simp [OneForms, multiplicationTensor_tmul]⟩

@[simp] theorem normalizeTensor_tmul (a b : A) :
    normalizeTensor A (a ⊗ₜ[ℤ] b) = leftDifferentialForm A a b := by
  apply Subtype.ext
  simp [normalizeTensor, leftDifferentialForm, leftDifferentialTensor,
    multiplicationTensor_tmul]

theorem normalizeTensor_add (x y : A ⊗[ℤ] A) :
    normalizeTensor A (x + y) = normalizeTensor A x + normalizeTensor A y := by
  apply Subtype.ext
  simp only [normalizeTensor, Subtype.coe_mk, Submodule.coe_add, map_add,
    TensorProduct.add_tmul]
  abel

/-- The multiplication kernel is spanned as an additive subgroup by the
actual one-forms `a · dᵤ b`. -/
theorem oneForms_mem_span (ω : OneForms A) :
    ω ∈ Submodule.span ℤ
      (Set.range fun p : A × A => leftDifferentialForm A p.1 p.2) := by
  have hnorm : normalizeTensor A ω.val = ω := by
    apply Subtype.ext
    simp [normalizeTensor]
  rw [← hnorm]
  induction ω.val using TensorProduct.inductionOn with
  | tmul a b =>
      rw [normalizeTensor_tmul]
      exact Submodule.subset_span ⟨(a, b), rfl⟩
  | add x y hx hy =>
      rw [normalizeTensor_add]
      exact Submodule.add_mem _ hx hy

/-- Additive maps out of the universal one-form carrier are determined by
their values on the universal generators `a · dᵤ b`. This is the uniqueness
half of the first-order universal property. -/
theorem oneForms_addHom_ext {M : Type*} [AddCommGroup M]
    (f g : OneForms A →+ M)
    (h : ∀ a b : A, f (leftDifferentialForm A a b) =
      g (leftDifferentialForm A a b)) :
    f = g := by
  apply AddMonoidHom.ext
  intro ω
  refine Submodule.span_induction
    (p := fun x _ => f x = g x) ?_ ?_ ?_ ?_ (oneForms_mem_span A ω)
  · rintro x ⟨⟨a, b⟩, rfl⟩
    exact h a b
  · simp
  · intro x y hx hy hfx hgy
    simp [hfx, hgy]
  · intro z x hx hfx
    simp [map_zsmul, hfx]

/-- The universal differential satisfies the Leibniz rule when its left and
right module terms are written in the tensor-kernel carrier. -/
theorem differential_mul (a b : A) :
    differential A (a * b) =
      ⟨leftDifferentialTensor A a b + rightDifferentialTensor A a b, by
        simp [OneForms, leftDifferentialTensor, rightDifferentialTensor,
          multiplicationTensor_tmul]⟩ := by
  apply Subtype.ext
  simp [differential, leftDifferentialTensor, rightDifferentialTensor]

/-- Every tensor is congruent modulo the multiplication map to a linear
combination of the tensors `a · dᵤ b`.  This is the spanning calculation
underlying the universal property of `ker μ`. -/
theorem tensor_normalForm_mem_span (x : A ⊗[ℤ] A) :
    x - (multiplicationTensor A x) ⊗ₜ[ℤ] (1 : A) ∈
      Submodule.span ℤ (Set.range fun p : A × A => leftDifferentialTensor A p.1 p.2) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      change leftDifferentialTensor A a b ∈ _
      exact Submodule.subset_span ⟨(a, b), rfl⟩
  | add x y hx hy =>
      have hrewrite :
          x + y - (multiplicationTensor A (x + y)) ⊗ₜ[ℤ] (1 : A) =
            (x - (multiplicationTensor A x) ⊗ₜ[ℤ] (1 : A)) +
              (y - (multiplicationTensor A y) ⊗ₜ[ℤ] (1 : A)) := by
        simp only [map_add, TensorProduct.add_tmul]
        abel
      rw [hrewrite]
      exact Submodule.add_mem _ hx hy

/-- Every universal one-form is generated by the left differential tensors
`a · dᵤ b`. -/
theorem oneForm_mem_span (ω : OneForms A) :
    ω.val ∈ Submodule.span ℤ
      (Set.range fun p : A × A => leftDifferentialTensor A p.1 p.2) := by
  have h := tensor_normalForm_mem_span A ω.val
  rw [ω.property] at h
  simpa using h

/-- The additive tensor map induced by a pairing on `A × A` that is balanced
for the canonical integer actions. -/
def tensorAddHom {M : Type*} [AddCommGroup M]
    (f : A →+ A →+ M)
    (balanced : ∀ (n : ℤ) (x y : A), f (n • x) y = f x (n • y)) :
    A ⊗[ℤ] A →+ M :=
  TensorProduct.liftAddHom f balanced

/-- On a universal differential, a bilinear tensor map evaluates as the
difference of its two unit-edge values. -/
theorem tensorAddHom_differential {M : Type*} [AddCommGroup M]
    (f : A →+ A →+ M)
    (balanced : ∀ (n : ℤ) (x y : A), f (n • x) y = f x (n • y)) (a : A) :
    tensorAddHom A f balanced (differential A a).val = f 1 a - f a 1 := by
  simp [tensorAddHom, differential]

/-- Evaluation of a left differential tensor is the left Leibniz pairing
minus its unit correction. -/
theorem tensorAddHom_leftDifferentialTensor {M : Type*} [AddCommGroup M]
    (f : A →+ A →+ M)
    (balanced : ∀ (n : ℤ) (x y : A), f (n • x) y = f x (n • y))
    (a b : A) :
    tensorAddHom A f balanced (leftDifferentialTensor A a b) =
      f a b - f (a * b) 1 := by
  simp [tensorAddHom, leftDifferentialTensor]

section Bimodule

/-- The one-form represented by `(dᵤ a) · b`. -/
def rightDifferentialForm (a b : A) : OneForms A :=
  ⟨rightDifferentialTensor A a b, by
    simp [OneForms, rightDifferentialTensor, multiplicationTensor_tmul]⟩

@[simp] theorem rightDifferentialForm_val (a b : A) :
    (rightDifferentialForm A a b).val = (1 : A) ⊗ₜ[ℤ] (a * b) - a ⊗ₜ[ℤ] b :=
  rfl

@[simp] theorem leftDifferentialForm_val (a b : A) :
    (leftDifferentialForm A a b).val = a ⊗ₜ[ℤ] b - (a * b) ⊗ₜ[ℤ] (1 : A) :=
  rfl

/-- Additive decomposition of `dᵤ (a * b)` in `OneForms A`. -/
theorem differential_mul_forms (a b : A) :
    differential A (a * b) =
      leftDifferentialForm A a b + rightDifferentialForm A a b := by
  apply Subtype.ext
  simp [differential_val, leftDifferentialForm_val, rightDifferentialForm_val]

private def leftMulPair (c : A) : A →+ A →+ A ⊗[ℤ] A where
  toFun a :=
    { toFun := fun b => (c * a) ⊗ₜ[ℤ] b
      map_zero' := by simp
      map_add' := fun b₁ b₂ => TensorProduct.tmul_add (c * a) b₁ b₂ }
  map_zero' := by
    ext b
    simp
  map_add' a₁ a₂ := by
    ext b
    simp [mul_add, TensorProduct.add_tmul]

private theorem leftMulPair_balanced (c : A) (n : ℤ) (a b : A) :
    leftMulPair A c (n • a) b = leftMulPair A c a (n • b) := by
  change (c * (n • a)) ⊗ₜ[ℤ] b = (c * a) ⊗ₜ[ℤ] (n • b)
  rw [mul_smul_comm, TensorProduct.smul_tmul]

/-- Left multiplication by `c : A` on `A ⊗[ℤ] A`. -/
def leftMulTensor (c : A) : A ⊗[ℤ] A →+ A ⊗[ℤ] A :=
  tensorAddHom A (leftMulPair A c) (leftMulPair_balanced A c)

@[simp] theorem leftMulTensor_tmul (c a b : A) :
    leftMulTensor A c (a ⊗ₜ[ℤ] b) = (c * a) ⊗ₜ[ℤ] b :=
  rfl

theorem multiplicationTensor_leftMulTensor (c : A) (x : A ⊗[ℤ] A) :
    multiplicationTensor A (leftMulTensor A c x) = c * multiplicationTensor A x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp [leftMulTensor_tmul, multiplicationTensor_tmul, mul_assoc]
  | add x y hx hy =>
    simp only [map_add, hx, hy, mul_add]

/-- Left `A`-module action on `OneForms A`. -/
def leftAction (c : A) : OneForms A →+ OneForms A where
  toFun ω :=
    ⟨leftMulTensor A c ω.val, by
      change multiplicationTensor A (leftMulTensor A c ω.val) = 0
      rw [multiplicationTensor_leftMulTensor, ω.property, mul_zero]⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' ω₁ ω₂ := by
    apply Subtype.ext
    simp [map_add]

@[simp] theorem leftAction_val (c : A) (ω : OneForms A) :
    (leftAction A c ω).val = leftMulTensor A c ω.val :=
  rfl

@[simp] theorem leftAction_differential (c a : A) :
    leftAction A c (differential A a) = leftDifferentialForm A c a := by
  apply Subtype.ext
  simp [leftAction_val, differential_val, map_sub, leftMulTensor_tmul, mul_one,
    leftDifferentialForm_val]

@[simp] theorem leftAction_leftDifferentialForm (c a b : A) :
    leftAction A c (leftDifferentialForm A a b) = leftDifferentialForm A (c * a) b := by
  apply Subtype.ext
  simp [leftAction_val, leftDifferentialForm_val, map_sub, leftMulTensor_tmul, mul_assoc]

@[simp] theorem leftAction_one (ω : OneForms A) :
    leftAction A 1 ω = ω := by
  apply Subtype.ext
  change leftMulTensor A 1 ω.val = ω.val
  induction ω.val using TensorProduct.inductionOn with
  | tmul a b =>
    simp [leftMulTensor_tmul]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

theorem leftAction_mul (c₁ c₂ : A) (ω : OneForms A) :
    leftAction A (c₁ * c₂) ω = leftAction A c₁ (leftAction A c₂ ω) := by
  apply Subtype.ext
  change leftMulTensor A (c₁ * c₂) ω.val = leftMulTensor A c₁ (leftMulTensor A c₂ ω.val)
  induction ω.val using TensorProduct.inductionOn with
  | tmul a b =>
    simp [leftMulTensor_tmul, mul_assoc]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

private def rightMulPair (c : A) : A →+ A →+ A ⊗[ℤ] A where
  toFun a :=
    { toFun := fun b => a ⊗ₜ[ℤ] (b * c)
      map_zero' := by simp
      map_add' := fun b₁ b₂ => by simp [add_mul, TensorProduct.tmul_add] }
  map_zero' := by
    ext b
    simp
  map_add' a₁ a₂ := by
    ext b
    simp [TensorProduct.add_tmul]

private theorem rightMulPair_balanced (c : A) (n : ℤ) (a b : A) :
    rightMulPair A c (n • a) b = rightMulPair A c a (n • b) := by
  change (n • a) ⊗ₜ[ℤ] (b * c) = a ⊗ₜ[ℤ] ((n • b) * c)
  rw [smul_mul_assoc, TensorProduct.smul_tmul]

/-- Right multiplication by `c : A` on `A ⊗[ℤ] A`. -/
def rightMulTensor (c : A) : A ⊗[ℤ] A →+ A ⊗[ℤ] A :=
  tensorAddHom A (rightMulPair A c) (rightMulPair_balanced A c)

@[simp] theorem rightMulTensor_tmul (c a b : A) :
    rightMulTensor A c (a ⊗ₜ[ℤ] b) = a ⊗ₜ[ℤ] (b * c) :=
  rfl

theorem multiplicationTensor_rightMulTensor (c : A) (x : A ⊗[ℤ] A) :
    multiplicationTensor A (rightMulTensor A c x) = multiplicationTensor A x * c := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp [rightMulTensor_tmul, multiplicationTensor_tmul, mul_assoc]
  | add x y hx hy =>
    simp only [map_add, hx, hy, add_mul]

/-- Right `A`-module action on `OneForms A`. -/
def rightAction (c : A) : OneForms A →+ OneForms A where
  toFun ω :=
    ⟨rightMulTensor A c ω.val, by
      change multiplicationTensor A (rightMulTensor A c ω.val) = 0
      rw [multiplicationTensor_rightMulTensor, ω.property, zero_mul]⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' ω₁ ω₂ := by
    apply Subtype.ext
    simp [map_add]

@[simp] theorem rightAction_val (c : A) (ω : OneForms A) :
    (rightAction A c ω).val = rightMulTensor A c ω.val :=
  rfl

@[simp] theorem rightAction_differential (a b : A) :
    rightAction A b (differential A a) = rightDifferentialForm A a b := by
  apply Subtype.ext
  simp [rightAction_val, differential_val, map_sub, rightMulTensor_tmul, one_mul,
    rightDifferentialForm_val]

theorem differential_mul_bimodule (a b : A) :
    differential A (a * b) =
      leftAction A a (differential A b) + rightAction A b (differential A a) := by
  rw [leftAction_differential, rightAction_differential]
  exact differential_mul_forms A a b

theorem rightAction_leftDifferentialForm (a b c : A) :
    rightAction A c (leftDifferentialForm A a b) =
      leftDifferentialForm A a (b * c) - leftDifferentialForm A (a * b) c := by
  apply Subtype.ext
  simp only [Submodule.coe_sub, rightAction_val, leftDifferentialForm_val, map_sub,
    rightMulTensor_tmul, one_mul, mul_assoc]
  abel

end Bimodule

end InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms

open scoped TensorProduct
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane

/-! ## Universal Factorization to `ActionOperatorForm` and `DerivationOperatorForm` -/

section UniversalFactorization

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Degree-0 linear equivalence `A ≃ₗ[R] ActionOperatorForm K 0`. -/
def actionZeroFormEquiv (K : LieActionLane R A) : A ≃ₗ[R] ActionOperatorForm K 0 :=
  AlternatingMap.constLinearEquivOfIsEmpty

@[simp] theorem actionZeroFormEquiv_apply (K : LieActionLane R A) (a : A) (v : Fin 0 → K.L) :
    actionZeroFormEquiv K a v = a :=
  rfl

/-- Degree-1 linear equivalence `(K.L →ₗ[R] A) ≃ₗ[R] ActionOperatorForm K 1`. -/
def actionOneFormEquiv (K : LieActionLane R A) : (K.L →ₗ[R] A) ≃ₗ[R] ActionOperatorForm K 1 where
  toLinearMap :=
    { toFun := AlternatingMap.ofSubsingleton R K.L A (0 : Fin 1)
      map_add' := fun _ _ => by ext v; rfl
      map_smul' := fun _ _ => by ext v; rfl }
  invFun η :=
    { toFun := fun x => η (fun _ => x)
      map_add' := fun x y => by
        have h : (fun _ : Fin 1 => x + y) = Function.update (fun _ => x) 0 (x + y) :=
          funext fun i => by fin_cases i; rfl
        have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
          funext fun i => by fin_cases i; rfl
        have h1 : (fun _ : Fin 1 => y) = Function.update (fun _ => x) 0 y :=
          funext fun i => by fin_cases i; rfl
        rw [h, η.map_update_add, ← h0, ← h1]
      map_smul' := fun c x => by
        have h : (fun _ : Fin 1 => c • x) = Function.update (fun _ => x) 0 (c • x) :=
          funext fun i => by fin_cases i; rfl
        have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
          funext fun i => by fin_cases i; rfl
        change η (fun _ => c • x) = c • η (fun _ => x)
        rw [h, η.map_update_smul, ← h0] }
  left_inv _ := by ext x; rfl
  right_inv η := by
    ext v
    change η (fun _ => v 0) = η v
    congr 1
    ext i
    rw [Fin.eq_zero i]

@[simp] theorem actionOneFormEquiv_apply (K : LieActionLane R A)
    (ω : K.L →ₗ[R] A) (v : Fin 1 → K.L) :
    actionOneFormEquiv K ω v = ω (v 0) :=
  rfl

@[simp] theorem actionOneFormEquiv_symm_apply (K : LieActionLane R A)
    (η : ActionOperatorForm K 1) (x : K.L) :
    (actionOneFormEquiv K).symm η x = η (fun _ => x) :=
  rfl

/-- Additive `(A, A)`-pairing `(a, b) ↦ (x ↦ a * K.operatorAction x b)` valued in
`ActionOperatorForm K 1`. -/
def actionFormPairing (K : LieActionLane R A) : A →+ A →+ ActionOperatorForm K 1 where
  toFun a :=
    { toFun := fun b =>
        actionOneFormEquiv K
          { toFun := fun x => a * K.operatorAction x b
            map_add' := fun x y => by simp only [map_add, LinearMap.add_apply, mul_add]
            map_smul' := fun r x => by
              simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, Algebra.mul_smul_comm] }
      map_zero' := by
        ext v
        simp
      map_add' := fun b₁ b₂ => by
        ext v
        simp only [actionOneFormEquiv_apply, LinearMap.coe_mk, AddHom.coe_mk,
          AlternatingMap.add_apply, map_add, mul_add] }
  map_zero' := by
    ext b v
    simp
  map_add' a₁ a₂ := by
    ext b v
    change (a₁ + a₂) * K.operatorAction (v 0) b =
      a₁ * K.operatorAction (v 0) b + a₂ * K.operatorAction (v 0) b
    exact add_mul a₁ a₂ (K.operatorAction (v 0) b)

@[simp] theorem actionFormPairing_apply (K : LieActionLane R A)
    (a b : A) (v : Fin 1 → K.L) :
    actionFormPairing K a b v = a * K.operatorAction (v 0) b :=
  rfl

theorem actionFormPairing_balanced (K : LieActionLane R A) (n : ℤ) (a b : A) :
    actionFormPairing K (n • a) b = actionFormPairing K a (n • b) := by
  ext v
  change (n • a) * K.operatorAction (v 0) b = a * K.operatorAction (v 0) (n • b)
  rw [smul_mul_assoc, map_zsmul, mul_smul_comm]

/-- Universal factorization of `OneForms A` into `ActionOperatorForm K 1`
for any `LieActionLane R A`. -/
def universalOneFormToActionForm (K : LieActionLane R A) :
    OneForms A →+ ActionOperatorForm K 1 where
  toFun ω := tensorAddHom A (actionFormPairing K) (actionFormPairing_balanced K) ω.val
  map_zero' := by
    change tensorAddHom A (actionFormPairing K) (actionFormPairing_balanced K) 0 = 0
    exact map_zero _
  map_add' ω₁ ω₂ := by
    change tensorAddHom A (actionFormPairing K) (actionFormPairing_balanced K)
        (ω₁.val + ω₂.val) = _
    exact map_add _ ω₁.val ω₂.val

theorem isLeibnizAction_map_one {K : LieActionLane R A} (hK : IsLeibnizAction K) (x : K.L) :
    K.operatorAction x 1 = 0 := by
  have h := hK x 1 1
  simp only [mul_one, one_mul] at h
  have h' : K.operatorAction x 1 + 0 = K.operatorAction x 1 + K.operatorAction x 1 := by
    simpa using h
  exact (add_left_cancel h').symm

theorem universalOneFormToActionForm_leftDifferentialForm_raw (K : LieActionLane R A)
    (a b : A) (v : Fin 1 → K.L) :
    universalOneFormToActionForm K (leftDifferentialForm A a b) v =
      a * K.operatorAction (v 0) b - (a * b) * K.operatorAction (v 0) 1 := by
  change tensorAddHom A (actionFormPairing K) (actionFormPairing_balanced K)
      (leftDifferentialTensor A a b) v = _
  rw [tensorAddHom_leftDifferentialTensor]
  rfl

@[simp] theorem universalOneFormToActionForm_leftDifferentialForm {K : LieActionLane R A}
    (hK : IsLeibnizAction K) (a b : A) (v : Fin 1 → K.L) :
    universalOneFormToActionForm K (leftDifferentialForm A a b) v =
      a * K.operatorAction (v 0) b := by
  rw [universalOneFormToActionForm_leftDifferentialForm_raw, isLeibnizAction_map_one hK,
    mul_zero, sub_zero]

theorem universalOneFormToActionForm_differential {K : LieActionLane R A}
    (hK : IsLeibnizAction K) (a : A) :
    universalOneFormToActionForm K (differential A a) =
      actionExteriorDerivative K 0 (actionZeroFormEquiv K a) := by
  ext v
  change tensorAddHom A (actionFormPairing K) (actionFormPairing_balanced K)
      (differential A a).val v = _
  rw [tensorAddHom_differential]
  simp only [AlternatingMap.sub_apply, actionFormPairing_apply, one_mul,
    isLeibnizAction_map_one hK, mul_zero, sub_zero, actionExteriorDerivative_zero_apply,
    actionZeroFormEquiv_apply]

@[simp] theorem universalOneFormToActionForm_rightDifferentialForm {K : LieActionLane R A}
    (hK : IsLeibnizAction K) (a b : A) (v : Fin 1 → K.L) :
    universalOneFormToActionForm K (rightDifferentialForm A a b) v =
      K.operatorAction (v 0) a * b := by
  have hdiff := congrArg (fun ω => universalOneFormToActionForm K ω v)
    (differential_mul_forms A a b)
  rw [map_add, AlternatingMap.add_apply, universalOneFormToActionForm_differential hK,
    actionExteriorDerivative_zero_apply, actionZeroFormEquiv_apply,
    hK (v 0) a b, universalOneFormToActionForm_leftDifferentialForm hK] at hdiff
  have hdiff' : K.operatorAction (v 0) a * b + a * K.operatorAction (v 0) b =
      universalOneFormToActionForm K (rightDifferentialForm A a b) v +
        a * K.operatorAction (v 0) b := by
    rw [hdiff, add_comm]
  exact (add_right_cancel hdiff').symm

theorem universalOneFormToActionForm_differential_mul {K : LieActionLane R A}
    (hK : IsLeibnizAction K) (a b : A) (v : Fin 1 → K.L) :
    universalOneFormToActionForm K (differential A (a * b)) v =
      a * K.operatorAction (v 0) b + K.operatorAction (v 0) a * b := by
  rw [universalOneFormToActionForm_differential hK, actionExteriorDerivative_zero_apply,
    actionZeroFormEquiv_apply, hK (v 0) a b, add_comm]

theorem universalOneFormToActionForm_leftDifferentialForm_smul_left (K : LieActionLane R A)
    (r : R) (a b : A) :
    universalOneFormToActionForm K (leftDifferentialForm A (r • a) b) =
      r • universalOneFormToActionForm K (leftDifferentialForm A a b) := by
  ext v
  simp only [universalOneFormToActionForm_leftDifferentialForm_raw, AlternatingMap.smul_apply,
    Algebra.smul_mul_assoc, smul_sub]

theorem universalOneFormToActionForm_leftDifferentialForm_smul_right {K : LieActionLane R A}
    (hK : IsLeibnizAction K) (r : R) (a b : A) :
    universalOneFormToActionForm K (leftDifferentialForm A a (r • b)) =
      r • universalOneFormToActionForm K (leftDifferentialForm A a b) := by
  ext v
  simp only [universalOneFormToActionForm_leftDifferentialForm hK, AlternatingMap.smul_apply,
    map_smul, Algebra.mul_smul_comm]

theorem universalOneFormToActionForm_leftAction (K : LieActionLane R A)
    (c : A) (ω : OneForms A) (v : Fin 1 → K.L) :
    universalOneFormToActionForm K (leftAction A c ω) v =
      c * universalOneFormToActionForm K ω v := by
  let f : OneForms A →+ ActionOperatorForm K 1 :=
    (universalOneFormToActionForm K).comp (leftAction A c)
  let g : OneForms A →+ ActionOperatorForm K 1 :=
    { toFun := fun η => actionOneFormEquiv K
        { toFun := fun x => c * universalOneFormToActionForm K η (fun _ => x)
          map_add' := fun x y => by
            have hx : (fun _ : Fin 1 => x + y) =
                Function.update (fun _ => x) 0 (x + y) :=
              funext fun i => by fin_cases i; rfl
            have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
              funext fun i => by fin_cases i; rfl
            have h1 : (fun _ : Fin 1 => y) = Function.update (fun _ => x) 0 y :=
              funext fun i => by fin_cases i; rfl
            rw [hx, (universalOneFormToActionForm K η).map_update_add, ← h0, ← h1, mul_add]
          map_smul' := fun r x => by
            have hx : (fun _ : Fin 1 => r • x) =
                Function.update (fun _ => x) 0 (r • x) :=
              funext fun i => by fin_cases i; rfl
            have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
              funext fun i => by fin_cases i; rfl
            change c * universalOneFormToActionForm K η (fun _ => r • x) =
              r • (c * universalOneFormToActionForm K η (fun _ => x))
            rw [hx, (universalOneFormToActionForm K η).map_update_smul, ← h0,
              Algebra.mul_smul_comm] }
      map_zero' := by ext u; simp
      map_add' := fun η₁ η₂ => by ext u; simp [mul_add] }
  have hfg : f = g := by
    apply oneForms_addHom_ext A f g
    intro a b
    ext u
    dsimp [f, g]
    rw [leftAction_leftDifferentialForm]
    have hconst : (fun _ : Fin 1 => u 0) = u := funext fun i => by rw [Fin.eq_zero i]
    rw [hconst, universalOneFormToActionForm_leftDifferentialForm_raw,
      universalOneFormToActionForm_leftDifferentialForm_raw]
    simp only [mul_sub, mul_assoc]
  have hval := congrArg (fun φ : OneForms A →+ ActionOperatorForm K 1 => φ ω v) hfg
  simpa [f, g, show (fun _ : Fin 1 => v 0) = v from funext fun i => by rw [Fin.eq_zero i]]
    using hval

theorem universalOneFormToActionForm_rightAction {K : LieActionLane R A}
    (hK : IsLeibnizAction K) (c : A) (ω : OneForms A) (v : Fin 1 → K.L) :
    universalOneFormToActionForm K (rightAction A c ω) v =
      universalOneFormToActionForm K ω v * c := by
  let f : OneForms A →+ ActionOperatorForm K 1 :=
    (universalOneFormToActionForm K).comp (rightAction A c)
  let g : OneForms A →+ ActionOperatorForm K 1 :=
    { toFun := fun η => actionOneFormEquiv K
        { toFun := fun x => universalOneFormToActionForm K η (fun _ => x) * c
          map_add' := fun x y => by
            have hx : (fun _ : Fin 1 => x + y) =
                Function.update (fun _ => x) 0 (x + y) :=
              funext fun i => by fin_cases i; rfl
            have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
              funext fun i => by fin_cases i; rfl
            have h1 : (fun _ : Fin 1 => y) = Function.update (fun _ => x) 0 y :=
              funext fun i => by fin_cases i; rfl
            rw [hx, (universalOneFormToActionForm K η).map_update_add, ← h0, ← h1, add_mul]
          map_smul' := fun r x => by
            have hx : (fun _ : Fin 1 => r • x) =
                Function.update (fun _ => x) 0 (r • x) :=
              funext fun i => by fin_cases i; rfl
            have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
              funext fun i => by fin_cases i; rfl
            change universalOneFormToActionForm K η (fun _ => r • x) * c =
              r • (universalOneFormToActionForm K η (fun _ => x) * c)
            rw [hx, (universalOneFormToActionForm K η).map_update_smul, ← h0,
              Algebra.smul_mul_assoc] }
      map_zero' := by ext u; simp
      map_add' := fun η₁ η₂ => by ext u; simp [add_mul] }
  have hfg : f = g := by
    apply oneForms_addHom_ext A f g
    intro a b
    ext u
    dsimp [f, g]
    have hconst : (fun _ : Fin 1 => u 0) = u := funext fun i => by rw [Fin.eq_zero i]
    rw [hconst, rightAction_leftDifferentialForm, map_sub, AlternatingMap.sub_apply,
      universalOneFormToActionForm_leftDifferentialForm hK,
      universalOneFormToActionForm_leftDifferentialForm hK,
      universalOneFormToActionForm_leftDifferentialForm hK,
      hK (u 0) b c, mul_add, mul_assoc]
    simp only [mul_assoc]
    abel
  have hval := congrArg (fun φ : OneForms A →+ ActionOperatorForm K 1 => φ ω v) hfg
  simpa [f, g, show (fun _ : Fin 1 => v 0) = v from funext fun i => by rw [Fin.eq_zero i]]
    using hval

/-- Uniqueness of `universalOneFormToActionForm` from its evaluation on `leftDifferentialForm`. -/
theorem universalOneFormToActionForm_unique_on_leftDifferentialForm {K : LieActionLane R A}
    (hK : IsLeibnizAction K) (f : OneForms A →+ ActionOperatorForm K 1)
    (hf : ∀ (a b : A) (v : Fin 1 → K.L),
      f (leftDifferentialForm A a b) v = a * K.operatorAction (v 0) b) :
    f = universalOneFormToActionForm K := by
  apply oneForms_addHom_ext A f (universalOneFormToActionForm K)
  intro a b
  ext v
  rw [hf a b v, universalOneFormToActionForm_leftDifferentialForm hK]

/-- Universal property of `OneForms A`: any additive map `OneForms A →+ ActionOperatorForm K 1`
that is left `A`-equivariant and agrees with `d₀` on `differential` equals
`universalOneFormToActionForm K`. -/
theorem universalOneFormToActionForm_unique_of_leftAction_differential {K : LieActionLane R A}
    (hK : IsLeibnizAction K) (f : OneForms A →+ ActionOperatorForm K 1)
    (hleft : ∀ (c : A) (ω : OneForms A) (v : Fin 1 → K.L),
      f (leftAction A c ω) v = c * f ω v)
    (hdiff : ∀ (a : A) (v : Fin 1 → K.L),
      f (differential A a) v = K.operatorAction (v 0) a) :
    f = universalOneFormToActionForm K := by
  apply universalOneFormToActionForm_unique_on_leftDifferentialForm hK f
  intro a b v
  rw [← leftAction_differential, hleft, hdiff]

/-- Exact universal differentials map to closed 1-forms. -/
theorem actionExteriorDerivative_universalOneForm_differential {K : LieActionLane R A}
    (hK : IsLeibnizAction K) (a : A) :
    actionExteriorDerivative K 1 (universalOneFormToActionForm K (differential A a)) = 0 := by
  rw [universalOneFormToActionForm_differential hK]
  exact actionExteriorDerivative_succ_comp K 0 (actionZeroFormEquiv K a)

/-- Degree-2 exterior calculus compatibility: `d(a · db) = da ∧ db`. -/
theorem actionExteriorDerivative_universalOneForm_leftDifferentialForm
    {K : LieActionLane R A} (hK : IsLeibnizAction K) (a b : A) :
    actionExteriorDerivative K 1 (universalOneFormToActionForm K (leftDifferentialForm A a b)) =
      actionWedge K
        (universalOneFormToActionForm K (differential A a))
        (universalOneFormToActionForm K (differential A b)) := by
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, actionWedge_one_one_apply]
  have h1 : ![v 0, v 1] = Matrix.vecCons (v 0) ![v 1] := by
    ext i; fin_cases i <;> rfl
  rw [h1, ← AlternatingMap.curryLeft_apply_apply, actionExteriorDerivative_succ_curryLeft]
  simp only [AlternatingMap.sub_apply, lieDeriv_apply, actionExteriorDerivative_zero_apply,
    AlternatingMap.curryLeft_apply_apply]
  rw [Fin.sum_univ_one]
  have hcons0 : Matrix.vecCons (v 0) (Fin.elim0 : Fin 0 → K.L) = ![v 0] := by
    ext i; fin_cases i; rfl
  have hupd : Function.update ![v 1] 0 ⁅v 0, ![v 1] 0⁆ = ![⁅v 0, v 1⁆] := by
    ext i; fin_cases i; rfl
  rw [hcons0, hupd]
  simp only [universalOneFormToActionForm_leftDifferentialForm hK,
    universalOneFormToActionForm_differential hK, actionExteriorDerivative_zero_apply,
    actionZeroFormEquiv_apply, Matrix.cons_val_zero]
  rw [hK (v 0) a (K.operatorAction (v 1) b), hK (v 1) a (K.operatorAction (v 0) b),
    K.operatorAction_commutator_apply (v 0) (v 1) b, mul_sub]
  abel

/-- Universal factorization of `OneForms A` into `DerivationOperatorForm K 1`. -/
def universalOneFormToDerivationForm (K : DerivationLieLane R A) :
    OneForms A →+ DerivationOperatorForm K 1 :=
  universalOneFormToActionForm K.toLieActionLane

@[simp] theorem universalOneFormToDerivationForm_leftDifferentialForm
    (K : DerivationLieLane R A) (a b : A) (v : Fin 1 → K.L) :
    universalOneFormToDerivationForm K (leftDifferentialForm A a b) v =
      a * K.operatorAction (v 0) b :=
  universalOneFormToActionForm_leftDifferentialForm K.isLeibnizAction a b v

theorem universalOneFormToDerivationForm_differential
    (K : DerivationLieLane R A) (a : A) :
    universalOneFormToDerivationForm K (differential A a) =
      ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) :=
  universalOneFormToActionForm_differential K.isLeibnizAction a

theorem universalOneFormToDerivationForm_unique_of_leftAction_differential
    (K : DerivationLieLane R A) (f : OneForms A →+ DerivationOperatorForm K 1)
    (hleft : ∀ (c : A) (ω : OneForms A) (v : Fin 1 → K.L),
      f (leftAction A c ω) v = c * f ω v)
    (hdiff : ∀ (a : A) (v : Fin 1 → K.L),
      f (differential A a) v = K.operatorAction (v 0) a) :
    f = universalOneFormToDerivationForm K :=
  universalOneFormToActionForm_unique_of_leftAction_differential K.isLeibnizAction f hleft hdiff

theorem ceExteriorDerivative_universalOneForm_leftDifferentialForm
    (K : DerivationLieLane R A) (a b : A) :
    ceExteriorDerivative K 1 (universalOneFormToDerivationForm K (leftDifferentialForm A a b)) =
      ceWedge K
        (universalOneFormToDerivationForm K (differential A a))
        (universalOneFormToDerivationForm K (differential A b)) :=
  actionExteriorDerivative_universalOneForm_leftDifferentialForm K.isLeibnizAction a b

/-- Universal factorization of `OneForms A` into `OneForm K`. -/
def universalOneFormToOneForm (K : DerivationLieLane R A) : OneForms A →+ OneForm K :=
  (oneFormAlternatingLinearEquiv K).symm.toAddMonoidHom.comp
    (universalOneFormToDerivationForm K)

@[simp] theorem universalOneFormToOneForm_differential
    (K : DerivationLieLane R A) (a : A) :
    universalOneFormToOneForm K (differential A a) = exteriorDerivativeZero K a := by
  ext x
  change universalOneFormToDerivationForm K (differential A a) (fun _ => x) =
    K.operatorAction x a
  rw [universalOneFormToDerivationForm_differential]
  exact actionExteriorDerivative_zero_apply K.toLieActionLane (zeroFormAlternatingEquiv K a)
    (fun _ => x)

theorem isClosed_universalOneForm_differential
    (K : DerivationLieLane R A) (a : A) :
    IsClosedOneForm K (universalOneFormToOneForm K (differential A a)) := by
  rw [universalOneFormToOneForm_differential]
  exact exteriorDerivativeOne_exteriorDerivativeZero K a

end UniversalFactorization

/-! ## Connes Cyclic 1-Cocycle & Hochschild Cohomology Bridges -/

section ConnesCyclicBridge

open InfoGeometry.NCG

section GeneralRing

variable {R A : Type*} [Ring R] [Ring A] [Module R A]

/-- Convert `NCG.AlgebraDerivation R A` into `NCG.CyclicAlgebraDerivation R A`. -/
def algebraDerivationToCyclic (D : AlgebraDerivation R A) : CyclicAlgebraDerivation R A where
  toLinearMap := D.toLinearMap
  leibniz' := D.leibniz'

private def cyclicEvalPair (D : CyclicAlgebraDerivation R A) : A →+ A →+ A where
  toFun a :=
    { toFun := fun b => a * D b
      map_zero' := by simp
      map_add' := fun b₁ b₂ => by simp [mul_add] }
  map_zero' := by ext b; simp
  map_add' a₁ a₂ := by ext b; simp [add_mul]

private theorem cyclicEvalPair_balanced (D : CyclicAlgebraDerivation R A) (n : ℤ) (a b : A) :
    cyclicEvalPair D (n • a) b = cyclicEvalPair D a (n • b) := by
  change (n • a) * D b = a * D (n • b)
  rw [smul_mul_assoc, ← mul_smul_comm]
  congr 1
  exact (map_zsmul D.toLinearMap.toAddMonoidHom n b).symm

/-- Universal evaluation `OneForms A →+ A` sending `a · dᵤ b ↦ a * D b`. -/
def cyclicDerivationUniversalEval (D : CyclicAlgebraDerivation R A) : OneForms A →+ A where
  toFun ω := tensorAddHom A (cyclicEvalPair D) (cyclicEvalPair_balanced D) ω.val
  map_zero' := map_zero _
  map_add' ω₁ ω₂ := map_add _ ω₁.val ω₂.val

@[simp] theorem cyclicDerivationUniversalEval_leftDifferentialForm
    (D : CyclicAlgebraDerivation R A) (a b : A) :
    cyclicDerivationUniversalEval D (leftDifferentialForm A a b) = a * D b := by
  change tensorAddHom A (cyclicEvalPair D) (cyclicEvalPair_balanced D)
      (leftDifferentialTensor A a b) = a * D b
  rw [tensorAddHom_leftDifferentialTensor]
  change a * D b - (a * b) * D 1 = a * D b
  simp

@[simp] theorem cyclicDerivationUniversalEval_differential
    (D : CyclicAlgebraDerivation R A) (a : A) :
    cyclicDerivationUniversalEval D (differential A a) = D a := by
  change tensorAddHom A (cyclicEvalPair D) (cyclicEvalPair_balanced D)
      (differential A a).val = D a
  rw [tensorAddHom_differential]
  change 1 * D a - a * D 1 = D a
  simp

@[simp] theorem cyclicDerivationUniversalEval_rightDifferentialForm
    (D : CyclicAlgebraDerivation R A) (a b : A) :
    cyclicDerivationUniversalEval D (rightDifferentialForm A a b) = D a * b := by
  have h := congrArg (cyclicDerivationUniversalEval D) (differential_mul_forms A a b)
  rw [map_add, cyclicDerivationUniversalEval_differential,
    cyclicDerivationUniversalEval_leftDifferentialForm, D.leibniz, add_comm (D a * b)] at h
  exact (add_left_cancel h).symm

/-- Connes universal 1-current `OneForms A →+ R` induced by `(τ, D)`. -/
def connesUniversalOneFormFunctional
    (τ : TracialFunctional R A) (D : CyclicAlgebraDerivation R A) : OneForms A →+ R :=
  τ.toLinearMap.toAddMonoidHom.comp (cyclicDerivationUniversalEval D)

@[simp] theorem connesUniversalOneFormFunctional_leftDifferentialForm
    (τ : TracialFunctional R A) (D : CyclicAlgebraDerivation R A) (x y : A) :
    connesUniversalOneFormFunctional τ D (leftDifferentialForm A x y) =
      connesCyclic1Cocycle τ D x y := by
  simp [connesUniversalOneFormFunctional, connesCyclic1Cocycle]

@[simp] theorem connesUniversalOneFormFunctional_rightDifferentialForm
    (τ : TracialFunctional R A) (D : CyclicAlgebraDerivation R A) (x y : A) :
    connesUniversalOneFormFunctional τ D (rightDifferentialForm A x y) =
      connesCyclic1Cocycle τ D y x := by
  simp [connesUniversalOneFormFunctional, connesCyclic1Cocycle, τ.cyclic]

theorem connesUniversalOneFormFunctional_differential_mul
    (τ : TracialFunctional R A) (D : CyclicAlgebraDerivation R A) (x y : A) :
    connesCyclic1Cocycle τ D x y + connesCyclic1Cocycle τ D y x =
      connesUniversalOneFormFunctional τ D (differential A (x * y)) := by
  simpa [connesUniversalOneFormFunctional] using cyclic_leibniz_identity τ D x y

theorem connesUniversalOneFormFunctional_differential_eq_zero_iff_skew
    (τ : TracialFunctional R A) (D : CyclicAlgebraDerivation R A) :
    (∀ a : A, connesUniversalOneFormFunctional τ D (differential A a) = 0) ↔
      (∀ x y : A, connesCyclic1Cocycle τ D x y = -connesCyclic1Cocycle τ D y x) := by
  constructor
  · intro hinv x y
    exact connes_cocycle_skew_symmetric τ D
      (fun z => by simpa [connesUniversalOneFormFunctional] using hinv z) x y
  · intro hskew a
    have h := hskew 1 a
    have hsum := connesUniversalOneFormFunctional_differential_mul τ D 1 a
    rw [one_mul] at hsum
    rw [← hsum, h, neg_add_cancel]

end GeneralRing

section ActionLaneConnes

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- View the action of `v : K.L` on a Leibniz `LieActionLane` as a `CyclicAlgebraDerivation`. -/
def lieActionToCyclicDerivation (K : LieActionLane R A) (hK : IsLeibnizAction K) (v : K.L) :
    CyclicAlgebraDerivation R A where
  toLinearMap := K.operatorAction v
  leibniz' := hK v

/-- View the action of `v : K.L` on a `DerivationLieLane` as a `CyclicAlgebraDerivation`. -/
def derivationLaneToCyclicDerivation (K : DerivationLieLane R A) (v : K.L) :
    CyclicAlgebraDerivation R A :=
  lieActionToCyclicDerivation K.toLieActionLane K.isLeibnizAction v

/-- Trace pairing of a 1-form `ω : ActionOperatorForm K 1` against `τ : TracialFunctional R A`. -/
def traceActionOneForm (τ : TracialFunctional R A) {K : LieActionLane R A}
    (ω : ActionOperatorForm K 1) : K.L →ₗ[R] R :=
  τ.toLinearMap.comp ((actionOneFormEquiv K).symm ω)

theorem traceActionOneForm_universal_leftDifferentialForm
    (τ : TracialFunctional R A) {K : LieActionLane R A} (hK : IsLeibnizAction K)
    (x y : A) (v : K.L) :
    traceActionOneForm τ (universalOneFormToActionForm K (leftDifferentialForm A x y)) v =
      connesCyclic1Cocycle τ (lieActionToCyclicDerivation K hK v) x y := by
  simp [traceActionOneForm, universalOneFormToActionForm_leftDifferentialForm hK,
    connesCyclic1Cocycle, lieActionToCyclicDerivation]

theorem traceActionOneForm_universal_differential
    (τ : TracialFunctional R A) {K : LieActionLane R A} (hK : IsLeibnizAction K)
    (a : A) (v : K.L) :
    traceActionOneForm τ (universalOneFormToActionForm K (differential A a)) v =
      τ (K.operatorAction v a) := by
  simp [traceActionOneForm, universalOneFormToActionForm_differential hK]

theorem traceActionOneForm_universal_cyclic_identity
    (τ : TracialFunctional R A) {K : LieActionLane R A} (hK : IsLeibnizAction K)
    (x y z : A) (v : K.L) :
    traceActionOneForm τ (universalOneFormToActionForm K (leftDifferentialForm A (x * y) z)) v -
      traceActionOneForm τ (universalOneFormToActionForm K (leftDifferentialForm A x (y * z))) v +
      traceActionOneForm τ (universalOneFormToActionForm K (leftDifferentialForm A (z * x) y)) v =
      0 := by
  simp only [traceActionOneForm_universal_leftDifferentialForm τ hK]
  exact connes_cyclic_1_cocycle_identity τ (lieActionToCyclicDerivation K hK v) x y z

end ActionLaneConnes

section RealHochschild

open InfoGeometry.Physics

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Convert `Physics.CyclicTraceData A` to `NCG.TracialFunctional ℝ A`. -/
def cyclicTraceDataToTracialFunctional (data : CyclicTraceData A) : TracialFunctional ℝ A where
  toLinearMap := data.Tr
  cyclic' := data.Tr_comm

/-- Convert `NCG.TracialFunctional ℝ A` to `Physics.CyclicTraceData A`. -/
def tracialFunctionalToCyclicTraceData (τ : TracialFunctional ℝ A) : CyclicTraceData A :=
  ⟨τ.toLinearMap, τ.cyclic⟩

/-- The Hochschild 1-cochain `a₀ ⊗ a₁ ↦ Tr(a₀ * D(a₁))`. -/
def connesCochain1 (data : CyclicTraceData A) (D : CyclicAlgebraDerivation ℝ A) : Cochain1 A :=
  connesCyclic1Cocycle (cyclicTraceDataToTracialFunctional data) D

theorem hochschild_b1_connesCochain1
    (data : CyclicTraceData A) (D : CyclicAlgebraDerivation ℝ A) (a0 a1 a2 : A) :
    hochschild_b1 (connesCochain1 data D) a0 a1 a2 = 0 := by
  dsimp [hochschild_b1, connesCochain1]
  exact connes_cyclic_1_cocycle_identity (cyclicTraceDataToTracialFunctional data) D a0 a1 a2

theorem hochschild_b1_universalActionOneForm
    (data : CyclicTraceData A) (K : LieActionLane ℝ A) (hK : IsLeibnizAction K)
    (v : K.L) (a0 a1 a2 : A) :
    hochschild_b1
      (fun x y => data.Tr (universalOneFormToActionForm K (leftDifferentialForm A x y) ![v]))
      a0 a1 a2 = 0 := by
  have hfun :
      (fun x y => data.Tr (universalOneFormToActionForm K (leftDifferentialForm A x y) ![v])) =
        connesCochain1 data (lieActionToCyclicDerivation K hK v) := by
    ext x y
    simp [universalOneFormToActionForm_leftDifferentialForm hK, connesCochain1,
      connesCyclic1Cocycle, cyclicTraceDataToTracialFunctional, lieActionToCyclicDerivation]
  rw [hfun]
  exact hochschild_b1_connesCochain1 data (lieActionToCyclicDerivation K hK v) a0 a1 a2

theorem connesCochain1_inner_eq_hochschild_b0
    (data : CyclicTraceData A) (k a0 a1 : A) :
    connesCochain1 data (innerAlgebraDerivation (R := ℝ) k) a0 a1 =
      hochschild_b0 (-(data.Tr.comp (LinearMap.mul ℝ A k))) a0 a1 := by
  dsimp [connesCochain1, hochschild_b0]
  rw [connesCyclic1Cocycle_inner]
  simp only [cyclicTraceDataToTracialFunctional, mul_assoc]
  abel

end RealHochschild

end ConnesCyclicBridge

end InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms

end noncomputable section
