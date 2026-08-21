import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Operator-Valued Exterior Algebra, Wedge Products, and Pullbacks

This module formalizes:
1. Operator-valued 1-forms (`Op1Form V A`) and alternating 2-forms (`Op2Form V A`).
2. The wedge product `α ∧ β` for operator-valued forms and the non-commutative
   curvature identity: `(α ∧ α)(u, v) = [α(u), α(v)]`.
3. Pullback of operator forms along linear maps `ϕ* (α ∧ β) = (ϕ* α) ∧ (ϕ* β)`.
4. The Leibniz product rule for ring derivations acting on the exterior algebra:
     `D(α ∧ β) = (D α) ∧ β + α ∧ (D β)`.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Exterior

variable {R V W U A : Type*}
variable [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable [Ring A] [Algebra R A]

/-!
=============================================================================
PART 1: Operator-Valued 1-Forms and Alternating 2-Forms
=============================================================================
-/

/-- An operator-valued 1-form is an R-linear map from the tangent module V to A. -/
structure Op1Form (V A : Type*) [AddCommGroup V] [Module R V] [Ring A] [Algebra R A] where
  toFun : V →ₗ[R] A

instance : CoeFun (Op1Form V A) (fun _ => V → A) where
  coe α := α.toFun

/-- An alternating operator-valued 2-form on V with values in A. -/
structure Op2Form (V A : Type*) [AddCommGroup V] [Module R V] [Ring A] [Algebra R A] where
  toFun : V → V → A
  map_add_left' : ∀ u v w, toFun (u + v) w = toFun u w + toFun v w
  map_add_right' : ∀ u v w, toFun u (v + w) = toFun u v + toFun u w
  map_smul_left' : ∀ (c : R) u v, toFun (c • u) v = c • toFun u v
  map_smul_right' : ∀ (c : R) u v, toFun u (c • v) = c • toFun u v
  alternating' : ∀ u, toFun u u = 0

instance : CoeFun (Op2Form V A) (fun _ => V → V → A) where
  coe ω := ω.toFun

namespace Op2Form

variable (ω : Op2Form V A)

@[simp] theorem map_add_left (u v w : V) : ω (u + v) w = ω u w + ω v w := ω.map_add_left' u v w
@[simp] theorem map_add_right (u v w : V) : ω u (v + w) = ω u v + ω u w := ω.map_add_right' u v w
@[simp] theorem map_smul_left (c : R) (u v : V) : ω (c • u) v = c • ω u v := ω.map_smul_left' c u v
@[simp] theorem map_smul_right (c : R) (u v : V) : ω u (c • v) = c • ω u v := ω.map_smul_right' c u v
@[simp] theorem alternating (u : V) : ω u u = 0 := ω.alternating' u

/-- THEOREM 1: Skew-symmetry of alternating operator 2-forms: ω(u, v) = - ω(v, u). -/
theorem skew (u v : V) : ω u v = - ω v u := by
  have h := ω.alternating (u + v)
  rw [ω.map_add_left, ω.map_add_right, ω.map_add_right] at h
  rw [ω.alternating u, ω.alternating v, zero_add, add_zero] at h
  have h_shift : ω u v + ω v u = 0 := h
  exact eq_neg_of_add_eq_zero_left h_shift

end Op2Form

/-!
=============================================================================
PART 2: The Non-Commutative Wedge Product
=============================================================================
-/

/-- 
  The Wedge Product of two operator-valued 1-forms:
  (α ∧ β)(u, v) = α(u) * β(v) - α(v) * β(u)
-/
def wedge (α β : Op1Form V A) : Op2Form V A where
  toFun u v := α u * β v - α v * β u
  map_add_left' u v w := by
    dsimp
    rw [α.toFun.map_add, β.toFun.map_add]
    simp only [add_mul, mul_add]
    abel
  map_add_right' u v w := by
    dsimp
    rw [α.toFun.map_add, β.toFun.map_add]
    simp only [mul_add, add_mul]
    abel
  map_smul_left' c u v := by
    dsimp
    rw [α.toFun.map_smul, β.toFun.map_smul]
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  map_smul_right' c u v := by
    dsimp
    rw [α.toFun.map_smul, β.toFun.map_smul]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
  alternating' u := by
    dsimp
    rw [sub_self]

local infixr:70 " ⋏ " => wedge

@[simp]
theorem wedge_apply (α β : Op1Form V A) (u v : V) :
    (α ⋏ β) u v = α u * β v - α v * β u := rfl

/-- 
  THEOREM 2 (Non-Commutative Curvature / Self-Wedge Identity):
  For any operator-valued 1-form α, the self-wedge (α ∧ α) is identically 
  the Lie commutator of its values:
    (α ∧ α)(u, v) = [α(u), α(v)]
-/
theorem wedge_self_eq_commutator (α : Op1Form V A) (u v : V) :
    (α ⋏ α) u v = α u * α v - α v * α u := rfl

/-!
=============================================================================
PART 3: Pullback of Operator Differential Forms
=============================================================================
-/

/-- Pullback of an operator 1-form along an R-linear map ϕ : W →ₗ[R] V. -/
def pullback1 (ϕ : W →ₗ[R] V) (α : Op1Form V A) : Op1Form W A where
  toFun := α.toFun.comp ϕ

@[simp]
theorem pullback1_apply (ϕ : W →ₗ[R] V) (α : Op1Form V A) (w : W) :
    pullback1 ϕ α w = α (ϕ w) := rfl

/-- Pullback of an alternating operator 2-form along an R-linear map ϕ : W →ₗ[R] V. -/
def pullback2 (ϕ : W →ₗ[R] V) (ω : Op2Form V A) : Op2Form W A where
  toFun w₁ w₂ := ω (ϕ w₁) (ϕ w₂)
  map_add_left' w₁ w₂ w₃ := by
    dsimp
    rw [ϕ.map_add, ω.map_add_left]
  map_add_right' w₁ w₂ w₃ := by
    dsimp
    rw [ϕ.map_add, ω.map_add_right]
  map_smul_left' c w₁ w₂ := by
    dsimp
    rw [ϕ.map_smul, ω.map_smul_left]
  map_smul_right' c w₁ w₂ := by
    dsimp
    rw [ϕ.map_smul, ω.map_smul_right]
  alternating' w := by
    dsimp
    rw [ω.alternating]

@[simp]
theorem pullback2_apply (ϕ : W →ₗ[R] V) (ω : Op2Form V A) (w₁ w₂ : W) :
    pullback2 ϕ ω w₁ w₂ = ω (ϕ w₁) (ϕ w₂) := rfl

/-- 
  THEOREM 3 (Pullback Preserves the Wedge Product):
  ϕ* (α ∧ β) = (ϕ* α) ∧ (ϕ* β)
-/
theorem pullback_wedge (ϕ : W →ₗ[R] V) (α β : Op1Form V A) :
    pullback2 ϕ (α ⋏ β) = (pullback1 ϕ α) ⋏ (pullback1 ϕ β) := by
  dsimp [pullback2, pullback1, wedge]
  rfl

/-- 
  THEOREM 4 (Functoriality of Pullbacks / Composition):
  (ψ ∘ ϕ)* ω = ϕ* (ψ* ω)
-/
theorem pullback_comp (ψ : U →ₗ[R] W) (ϕ : W →ₗ[R] V) (ω : Op2Form V A) :
    pullback2 (ϕ.comp ψ) ω = pullback2 ψ (pullback2 ϕ ω) := by
  dsimp [pullback2]
  rfl

/-!
=============================================================================
PART 4: Ring Derivations Acting on the Operator Exterior Algebra
=============================================================================
-/

/-- An R-linear derivation on the algebra A. -/
structure LinearDerivation (R A : Type*) [CommRing R] [Ring A] [Algebra R A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (c : R) x, toFun (c • x) = c • toFun x
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

instance : CoeFun (LinearDerivation R A) (fun _ => A → A) where
  coe D := D.toFun

namespace LinearDerivation

variable (D : LinearDerivation R A)

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem map_smul (c : R) (x : A) : D (c • x) = c • D x := D.map_smul' c x
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D (0 + 0) = D 0 + D 0 := D.map_add 0 0
  rw [add_zero] at h
  exact (self_eq_add_left.mp h.symm).symm

@[simp]
theorem map_sub (x y : A) : D (x - y) = D x - D y := by
  have h_neg (z : A) : D (-z) = - D z := by
    have hz : D (z + -z) = D z + D (-z) := D.map_add z (-z)
    rw [add_neg_cancel, D.map_zero] at hz
    exact eq_neg_of_add_eq_zero_right hz
  rw [sub_eq_add_neg, D.map_add, h_neg, ← sub_eq_add_neg]

end LinearDerivation

/-- Action of a derivation on an operator 1-form: (D α)(u) = D(α(u)). -/
def deriv1 (D : LinearDerivation R A) (α : Op1Form V A) : Op1Form V A where
  toFun := {
    toFun := fun u => D (α u)
    map_add' := fun u v => by simp [α.toFun.map_add, D.map_add]
    map_smul' := fun c u => by simp [α.toFun.map_smul, D.map_smul]
  }

@[simp]
theorem deriv1_apply (D : LinearDerivation R A) (α : Op1Form V A) (u : V) :
    deriv1 D α u = D (α u) := rfl

/-- Action of a derivation on an alternating operator 2-form: (D ω)(u, v) = D(ω(u, v)). -/
def deriv2 (D : LinearDerivation R A) (ω : Op2Form V A) : Op2Form V A where
  toFun u v := D (ω u v)
  map_add_left' u v w := by simp [ω.map_add_left, D.map_add]
  map_add_right' u v w := by simp [ω.map_add_right, D.map_add]
  map_smul_left' c u v := by simp [ω.map_smul_left, D.map_smul]
  map_smul_right' c u v := by simp [ω.map_smul_right, D.map_smul]
  alternating' u := by simp [ω.alternating, D.map_zero]

@[simp]
theorem deriv2_apply (D : LinearDerivation R A) (ω : Op2Form V A) (u v : V) :
    deriv2 D ω u v = D (ω u v) := rfl

/-- 
  THEOREM 5 (Leibniz Product Rule for the Operator Wedge Product):
  D(α ∧ β) = (D α) ∧ β + α ∧ (D β)
-/
theorem deriv_wedge_leibniz (D : LinearDerivation R A) (α β : Op1Form V A) (u v : V) :
    deriv2 D (α ⋏ β) u v = (deriv1 D α ⋏ β) u v + (α ⋏ deriv1 D β) u v := by
  dsimp [deriv2, deriv1, wedge]
  rw [D.map_sub, D.leibniz, D.leibniz]
  -- (D(α u) * β v + α u * D(β v)) - (D(α v) * β u + α v * D(β u))
  -- = (D(α u) * β v - D(α v) * β u) + (α u * D(β v) - α v * D(β u))
  abel

end InfoGeometry.OperatorAlgebra.Exterior

end noncomputable section
