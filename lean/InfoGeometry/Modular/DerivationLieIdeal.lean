import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Modular.LieIdeal

variable {A: Type*} [Ring A]

def adK (K X : A) : A :=
  K * X - X * K

@[simp] theorem adK_apply (K X : A) : adK K X = K * X - X * K := rfl

structure RingDerivation (A: Type*) [Ring A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

namespace RingDerivation

instance : CoeFun (RingDerivation A) (fun _ => A → A) where
  coe D := D.toFun

variable (D: RingDerivation A)

@[simp] theorem map_add (x y: A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x y: A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 = D 0 + D 0 := by
    calc D 0 = D (0 + 0) := by rw [add_zero]
    _ = D 0 + D 0 := D.map_add 0 0
  have h1 : D 0 - D 0 = (D 0 + D 0) - D 0 := congr_arg (fun x => x - D 0) h
  rw [sub_self, add_sub_cancel_right] at h1
  exact h1.symm

@[simp]
theorem map_neg (x: A) : D (-x) = - D x := by -- uses x
  have h : D (x + -x) = D x + D (-x) := D.map_add x (-x)
  rw [add_neg_cancel, D.map_zero] at h
  have h_neg : - D x = - D x + (D x + D (-x)) := by rw [← h, add_zero]
  rw [← add_assoc, neg_add_cancel, zero_add] at h_neg
  exact h_neg.symm

@[simp]
theorem map_sub (x: A) (y: A) : D (x - y) = D x - D y := by -- uses x y
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

theorem extensionality {D E : RingDerivation A} (h : ∀ x, D x = E x) : D = E := by
  cases D; cases E; congr; funext x; exact h x

def zero : RingDerivation A where
  toFun := fun _ => 0
  map_add' _ _ := by simp only [add_zero]
  leibniz' _ _ := by simp only [zero_mul, mul_zero, add_zero]

def add (D₁ D₂ : RingDerivation A) : RingDerivation A where
  toFun := fun x => D₁ x + D₂ x
  map_add' x y := by
    rw [D₁.map_add, D₂.map_add]
    abel
  leibniz' x y := by
    rw [D₁.leibniz, D₂.leibniz]
    simp only [add_mul, mul_add]
    abel

def neg (D : RingDerivation A) : RingDerivation A where
  toFun := fun x => - D x
  map_add' x y := by
    rw [D.map_add, neg_add]
  leibniz' x y := by
    rw [D.leibniz, neg_add, neg_mul_eq_neg_mul, neg_mul_eq_mul_neg]

def sub (D₁ D₂ : RingDerivation A) : RingDerivation A :=
  add D₁ (neg D₂)

def commutator (D₁ D₂ : RingDerivation A) : RingDerivation A where
  toFun := fun X => D₁ (D₂ X) - D₂ (D₁ X)
  map_add' x y := by
    rw [D₂.map_add, D₁.map_add, D₁.map_add, D₂.map_add]
    abel
  leibniz' x y := by
    rw [D₂.leibniz, D₁.leibniz, D₁.map_add, D₁.leibniz,
        D₁.leibniz, D₂.map_add, D₂.leibniz, D₂.leibniz]
    simp only [sub_mul, mul_sub]
    abel

end RingDerivation

def innerDerivation (K: A) : RingDerivation A where
  toFun := adK K
  map_add' x y := by
    dsimp [adK]
    simp only [mul_add, add_mul]
    abel
  leibniz' x y := by
    dsimp [adK]
    calc
      K * (x * y) - (x * y) * K = (K * x * y - x * K * y) + (x * K * y - x * y * K) := by
        simp only [mul_assoc]; abel
      _ = (K * x - x * K) * y + x * (K * y - y * K) := by
        simp only [sub_mul, mul_sub, mul_assoc]

@[simp] theorem innerDerivation_apply (K X : A) : innerDerivation K X = adK K X := rfl

theorem innerDerivation_zero : innerDerivation (0 : A) = RingDerivation.zero := by
  apply RingDerivation.extensionality
  intro X
  dsimp [innerDerivation, adK, RingDerivation.zero]
  simp only [mul_zero, zero_mul, sub_self]

theorem innerDerivation_add (K₁ K₂ : A) :
    innerDerivation (K₁ + K₂) = RingDerivation.add (innerDerivation K₁) (innerDerivation K₂) := by -- uses K₁ K₂
  apply RingDerivation.extensionality
  intro X
  dsimp [innerDerivation, adK, RingDerivation.add]
  simp only [add_mul, mul_add]
  abel

theorem innerDerivation_neg (K: A) :
    innerDerivation (-K) = RingDerivation.neg (innerDerivation K) := by -- uses K
  apply RingDerivation.extensionality
  intro X
  dsimp [innerDerivation, adK, RingDerivation.neg]
  simp only [neg_mul, mul_neg]
  abel

theorem innerDerivation_bracket (K₁ K₂ : A) :
    innerDerivation (adK K₁ K₂) = RingDerivation.commutator (innerDerivation K₁) (innerDerivation K₂) := by -- uses K₁ K₂
  apply RingDerivation.extensionality
  intro X
  dsimp [innerDerivation, adK, RingDerivation.commutator]
  calc
    (K₁ * K₂ - K₂ * K₁) * X - X * (K₁ * K₂ - K₂ * K₁)
      = K₁ * (K₂ * X - X * K₂) - (K₂ * X - X * K₂) * K₁ -
        (K₂ * (K₁ * X - X * K₁) - (K₁ * X - X * K₁) * K₂) := by
        simp only [sub_mul, mul_sub, mul_assoc]; abel

theorem derivation_adK_comm (D : RingDerivation A) (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X := by
  dsimp [adK]
  rw [D.map_sub, D.leibniz, D.leibniz]
  abel

theorem commutator_innerDerivation_eq (D : RingDerivation A) (K: A) :
    RingDerivation.commutator D (innerDerivation K) = innerDerivation (D K) := by -- uses D K
  apply RingDerivation.extensionality
  intro X
  exact derivation_adK_comm D K X

/-- Predicate characterizing inner derivations. -/
def isInner (D : RingDerivation A) : Prop :=
  ∃ K : A, D = innerDerivation K

/-- THEOREM 1: The zero derivation is inner. -/
theorem isInner_zero : isInner (RingDerivation.zero : RingDerivation A) := by
  exact ⟨0, innerDerivation_zero.symm⟩

/-- THEOREM 2: The sum of two inner derivations is inner. -/
theorem isInner_add {D₁ D₂ : RingDerivation A} (h₁ : isInner D₁) (h₂ : isInner D₂) :
    isInner (RingDerivation.add D₁ D₂) := by
  rcases h₁ with ⟨K₁, rfl⟩
  rcases h₂ with ⟨K₂, rfl⟩
  exact ⟨K₁ + K₂, (innerDerivation_add K₁ K₂).symm⟩

/-- THEOREM 3: The negative of an inner derivation is inner. -/
theorem isInner_neg {D : RingDerivation A} (h : isInner D) :
    isInner (RingDerivation.neg D) := by
  rcases h with ⟨K, rfl⟩
  exact ⟨-K, (innerDerivation_neg K).symm⟩

/-- THEOREM 4: The Lie bracket of two inner derivations is inner (Lie Subalgebra). -/
theorem isInner_bracket {D₁ D₂ : RingDerivation A} (h₁ : isInner D₁) (h₂ : isInner D₂) :
    isInner (RingDerivation.commutator D₁ D₂) := by
  rcases h₁ with ⟨K₁, rfl⟩
  rcases h₂ with ⟨K₂, rfl⟩
  exact ⟨adK K₁ K₂, (innerDerivation_bracket K₁ K₂).symm⟩

/-- 
  THEOREM 5 (Strict Lie Ideal):
  For EVERY derivation D (outer or inner) and EVERY inner derivation D_in,
  their Lie bracket [D, D_in] is strictly an inner derivation.
  [D, Inn(A)] ⊆ Inn(A)
-/
theorem isInner_lie_ideal (D : RingDerivation A) {D_in : RingDerivation A} (h_in : isInner D_in) :
    isInner (RingDerivation.commutator D D_in) := by
  rcases h_in with ⟨K, rfl⟩
  exact ⟨D K, commutator_innerDerivation_eq D K⟩

/-- 
  THEOREM 6 (Thermal Time Kernel):
  An inner derivation is identically zero if and only if its generator K lies in the center Z(A).
  ker(ad) = Z(A)
-/
theorem innerDerivation_eq_zero_iff_center (K: A) :
    innerDerivation K = RingDerivation.zero ↔ ∀ X : A, K * X = X * K := by -- uses K
  constructor
  · intro h X
    have h_apply := congr_fun (congr_arg RingDerivation.toFun h) X
    dsimp [innerDerivation, adK, RingDerivation.zero] at h_apply
    exact sub_eq_zero.mp h_apply
  · intro h_center
    apply RingDerivation.extensionality
    intro X
    dsimp [innerDerivation, adK, RingDerivation.zero]
    rw [h_center X, sub_self]

/-- Outer Equivalence Relation: D₁ ~ D₂ ↔ D₁ - D₂ ∈ Inn(A). -/
def outerEquiv (D₁ D₂ : RingDerivation A) : Prop :=
  isInner (RingDerivation.sub D₁ D₂)

theorem outerEquiv_refl (D: RingDerivation A) : outerEquiv D D := by -- uses D
  dsimp [outerEquiv]
  have h_zero : RingDerivation.sub D D = RingDerivation.zero := by
    apply RingDerivation.extensionality
    intro X
    dsimp [RingDerivation.sub, RingDerivation.add, RingDerivation.neg, RingDerivation.zero]
    abel
  rw [h_zero]
  exact isInner_zero

theorem outerEquiv_symm {D₁ D₂ : RingDerivation A} (h : outerEquiv D₁ D₂) : outerEquiv D₂ D₁ := by
  dsimp [outerEquiv] at *
  have h_neg : RingDerivation.sub D₂ D₁ = RingDerivation.neg (RingDerivation.sub D₁ D₂) := by
    apply RingDerivation.extensionality
    intro X
    dsimp [RingDerivation.sub, RingDerivation.add, RingDerivation.neg]
    abel
  rw [h_neg]
  exact isInner_neg h

theorem outerEquiv_trans {D₁ D₂ D₃ : RingDerivation A}
    (h₁₂ : outerEquiv D₁ D₂) (h₂₃ : outerEquiv D₂ D₃) : outerEquiv D₁ D₃ := by
  dsimp [outerEquiv] at *
  have h_sum : RingDerivation.sub D₁ D₃ =
      RingDerivation.add (RingDerivation.sub D₁ D₂) (RingDerivation.sub D₂ D₃) := by
    apply RingDerivation.extensionality
    intro X
    dsimp [RingDerivation.sub, RingDerivation.add, RingDerivation.neg]
    abel
  rw [h_sum]
  exact isInner_add h₁₂ h₂₃

end InfoGeometry.Modular.LieIdeal

end noncomputable section
