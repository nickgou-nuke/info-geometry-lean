import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Bundled Lie Ideal Structure of Inner Derivations and the Thermal Time Kernel

This module formalizes:
1. Derivation Lie algebra `Derivation A` with bracket `[D₁, D₂] = D₁ ∘ D₂ - D₂ ∘ D₁`.
2. The Inner Derivation constructor `ad K X = K * X - X * K`.
3. Lie Homomorphism: `[ad K₁, ad K₂] = ad [K₁, K₂]`.
4. Master Lie Ideal Property: `[D, ad K] = ad (D K)` for all D ∈ Der(A), K ∈ A.
5. Invariance of the Inner Derivation Subspace under arbitrary outer derivations:
   `T ∈ Inn(A) ⟹ [D, T] ∈ Inn(A)` and `[T, D] ∈ Inn(A)`.
6. The Thermal Time Kernel: `ad K = 0 ↔ K ∈ Z(A)`.
7. Stability of the Classical Center: `K ∈ Z(A) ⟹ D(K) ∈ Z(A)`.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Modular.LieIdeal

variable {A : Type*} [Ring A]

structure Derivation (A : Type*) [Ring A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

instance : CoeFun (Derivation A) (fun _ => A → A) where
  coe D := D.toFun

instance : Add (Derivation A) where
  add D₁ D₂ :=
    { toFun := fun x => D₁ x + D₂ x
      map_add' := by
        intro x y
        rw [D₁.map_add', D₂.map_add', add_add_add_comm]
      leibniz' := by
        intro x y
        simp only [D₁.leibniz', D₂.leibniz', add_mul, mul_add]
        abel }

instance : Zero (Derivation A) where
  zero :=
    { toFun := fun _ => 0
      map_add' := by simp
      leibniz' := by simp }

instance : Neg (Derivation A) where
  neg D :=
    { toFun := fun x => -D x
      map_add' := by
        intro x y
        rw [D.map_add', neg_add]
      leibniz' := by
        intro x y
        simp only [D.leibniz', neg_add, neg_mul, mul_neg]
        }

instance : Sub (Derivation A) where
  sub D₁ D₂ := D₁ + -D₂

namespace Derivation

variable (D : Derivation A)

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 = D 0 + D 0 := by
    calc D 0 = D (0 + 0) := by rw [add_zero]
    _ = D 0 + D 0 := D.map_add' 0 0
  have h1 : D 0 - D 0 = (D 0 + D 0) - D 0 := congr_arg (fun x => x - D 0) h
  rw [sub_self, add_sub_cancel_right] at h1
  exact h1.symm

@[simp]
theorem map_neg (x : A) : D (-x) = - D x := by
  have h : D (x + -x) = D x + D (-x) := D.map_add x (-x)
  rw [add_neg_cancel, D.map_zero] at h
  have h_neg : - D x = - D x + (D x + D (-x)) := by rw [← h, add_zero]
  rw [← add_assoc, neg_add_cancel, zero_add] at h_neg
  exact h_neg.symm

@[simp]
theorem map_sub (x y : A) : D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

/-- The Lie Bracket of derivations: [D₁, D₂] = D₁ ∘ D₂ - D₂ ∘ D₁. -/
def bracket (D₁ D₂ : Derivation A) (x : A) : A :=
  D₁ (D₂ x) - D₂ (D₁ x)

theorem bracket_leibniz (D₁ D₂ : Derivation A) (x y : A) :
    bracket D₁ D₂ (x * y) = (bracket D₁ D₂ x) * y + x * (bracket D₁ D₂ y) := by
  dsimp [bracket]
  simp only [Derivation.leibniz, Derivation.map_add]
  simp only [mul_sub, sub_mul]
  abel

def commutator (D₁ D₂ : Derivation A) : Derivation A where
  toFun := bracket D₁ D₂
  map_add' x y := by
    dsimp [bracket]
    rw [D₂.map_add, D₁.map_add, D₁.map_add, D₂.map_add]
    abel
  leibniz' := bracket_leibniz D₁ D₂

theorem ext (D₁ D₂ : Derivation A) (h : ∀ x, D₁ x = D₂ x) : D₁ = D₂ := by
  cases D₁
  cases D₂
  congr
  ext x
  exact h x

end Derivation

/-!
=============================================================================
PART 1: The Inner Derivation Constructor ad(K)
=============================================================================
-/

/-- Inner derivation: ad_K(X) = [K, X] = K * X - X * K. -/
def ad (K : A) : Derivation A where
  toFun X := K * X - X * K
  map_add' X Y := by
    simp only [mul_add, add_mul]
    abel
  leibniz' X Y := by
    simp only [sub_mul, mul_sub, mul_assoc]
    abel

@[simp] theorem ad_apply (K X : A) : ad K X = K * X - X * K := rfl

/-- Linearity of inner derivation assignment: ad(K₁ + K₂) = ad(K₁) + ad(K₂). -/
theorem ad_add (K₁ K₂ : A) :
    ∀ X, ad (K₁ + K₂) X = ad K₁ X + ad K₂ X := by
  intro X
  dsimp [ad]
  simp only [add_mul, mul_add]
  abel

/-- Bundled form of additivity of the inner-derivation constructor. -/
theorem ad_add_eq (K₁ K₂ : A) :
    ad (K₁ + K₂) = ad K₁ + ad K₂ := by
  apply Derivation.ext
  intro X
  exact ad_add K₁ K₂ X

/-- The zero generator induces the zero derivation. -/
theorem ad_zero (X : A) :
    ad (0 : A) X = 0 := by
  simp [ad]

/-- Bundled form of the zero-generator law. -/
theorem ad_zero_eq :
    ad (0 : A) = (0 : Derivation A) := by
  apply Derivation.ext
  intro X
  exact ad_zero X

/-- Bundled form of negation for the inner-derivation constructor. -/
theorem ad_neg_eq (K : A) :
    ad (-K) = -ad K := by
  apply Derivation.ext
  intro X
  change (-K) * X - X * (-K) = -(K * X - X * K)
  simp only [neg_mul, mul_neg, neg_sub]
  abel

/-- Bundled form of subtraction for the inner-derivation constructor. -/
theorem ad_sub_eq (K₁ K₂ : A) :
    ad (K₁ - K₂) = ad K₁ - ad K₂ := by
  apply Derivation.ext
  intro X
  change ad (K₁ - K₂) X = ad K₁ X + (-ad K₂ X)
  dsimp [ad]
  simp only [sub_mul, mul_sub, neg_sub]
  abel

/-!
=============================================================================
PART 2: Lie Homomorphism and Lie Ideal Theorems
=============================================================================
-/

/-- 
  THEOREM 1 (Lie Homomorphism of Inner Derivations):
  The commutator of two inner derivations is the inner derivation of their commutator:
    [ad(K₁), ad(K₂)] = ad([K₁, K₂])
-/
theorem ad_commutator_homomorphism (K₁ K₂ X : A) :
    Derivation.bracket (ad K₁) (ad K₂) X = ad (K₁ * K₂ - K₂ * K₁) X := by
  dsimp [Derivation.bracket, ad]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- Bundled Lie-homomorphism law for inner derivations. -/
theorem ad_commutator_homomorphism_eq (K₁ K₂ : A) :
    Derivation.commutator (ad K₁) (ad K₂) =
      ad (K₁ * K₂ - K₂ * K₁) := by
  apply Derivation.ext
  intro X
  exact ad_commutator_homomorphism K₁ K₂ X

/--
  THEOREM 2 (The Master Backreaction Lie Ideal Commutator):
  For any general derivation D ∈ Der(A) and any element K ∈ A:
    [D, ad(K)] = ad(D(K))
-/
theorem master_lie_ideal_commutator (D : Derivation A) (K X : A) :
    Derivation.bracket D (ad K) X = ad (D K) X := by
  dsimp [Derivation.bracket, ad]
  rw [D.map_sub, D.leibniz, D.leibniz]
  abel

/-- Bundled master backreaction identity for the inner-derivation ideal. -/
theorem master_lie_ideal_commutator_eq (D : Derivation A) (K : A) :
    Derivation.commutator D (ad K) = ad (D K) := by
  apply Derivation.ext
  intro X
  exact master_lie_ideal_commutator D K X

/-- Predicate for an inner derivation. -/
def isInnerDerivation (D : Derivation A) : Prop :=
  ∃ K : A, D = ad K

/-- 
  THEOREM 3 (Strict Lie Ideal Closure):
  If T is an inner derivation (T = ad(K)), then for any outer derivation D ∈ Der(A),
  their Lie bracket [D, T] is strictly an inner derivation:
    T ∈ Inn(A) ⟹ [D, T] ∈ Inn(A)
-/
theorem inner_derivations_is_lie_ideal (D : Derivation A) (T : Derivation A)
    (hT : isInnerDerivation T) :
    isInnerDerivation (Derivation.commutator D T) := by
  rcases hT with ⟨K, rfl⟩
  use D K
  apply Derivation.ext
  intro X
  exact master_lie_ideal_commutator D K X

/--
  THEOREM 4 (Skew Lie Ideal Closure):
  [T, D] is also strictly in Inn(A).
-/
theorem inner_derivations_is_lie_ideal_symm (D : Derivation A) (T : Derivation A)
    (hT : isInnerDerivation T) :
    isInnerDerivation (Derivation.commutator T D) := by
  rcases hT with ⟨K, rfl⟩
  use - (D K)
  apply Derivation.ext
  intro X
  dsimp [Derivation.commutator, Derivation.bracket, ad]
  rw [D.map_sub, D.leibniz, D.leibniz]
  simp only [neg_mul, mul_neg, sub_neg_eq_add]
  abel

/-!
=============================================================================
PART 3: Thermal Time Kernel and Center Invariance
=============================================================================
-/

/--
  THEOREM 5 (Thermal Time Kernel / Center Annihilation):
  An inner derivation is identically zero (ad(K) = 0) if and only if K is central:
    ad(K) = 0 ↔ ∀ X, K * X = X * K
-/
theorem thermal_time_kernel_iff_center (K : A) :
    (∀ X : A, ad K X = 0) ↔ (∀ X : A, K * X = X * K) := by
  constructor
  · intro h X
    have hX := h X
    dsimp [ad] at hX
    exact sub_eq_zero.mp hX
  · intro h X
    dsimp [ad]
    exact sub_eq_zero.mpr (h X)

/--
  THEOREM 6 (Center Invariance / Timelessness of Classical Volume):
  For any classical central observable B ∈ Z(A) and any spacetime flow D ∈ Der(A),
  the flow derivative D(B) remains strictly within the center Z(A).
-/
theorem center_preserved_under_flow (D : Derivation A) (B : A)
    (hB_center : ∀ X : A, B * X = X * B) (X : A) :
    D B * X = X * D B := by
  have h_prod : D (B * X) = D (X * B) := by rw [hB_center X]
  have h_left : D (B * X) = D B * X + B * D X := D.leibniz B X
  have h_right : D (X * B) = D X * B + X * D B := D.leibniz X B
  have h_comm_DX : D X * B = B * D X := (hB_center (D X)).symm
  have h_step : D B * X + B * D X = X * D B + B * D X := by
    calc
      D B * X + B * D X = D (B * X) := h_left.symm
      _ = D (X * B) := h_prod
      _ = D X * B + X * D B := h_right
      _ = B * D X + X * D B := by rw [h_comm_DX]
      _ = X * D B + B * D X := by rw [add_comm]
  exact add_right_cancel h_step

end InfoGeometry.Modular.LieIdeal

end noncomputable section
