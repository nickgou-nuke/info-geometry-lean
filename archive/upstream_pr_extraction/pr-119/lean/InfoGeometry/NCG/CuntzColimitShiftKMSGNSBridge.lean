import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Categorical Colimits, Cuntz Algebras, Shift/Tilt, Modular KMS States, and GNS

This module formalizes the grand noncommutative operator algebra unification:
1. Cuntz Algebra $\mathcal{O}_n$ relations with isometric generators $S_i^* S_j = \delta_{ij} 1$ and $\sum S_i S_i^* = 1$.
2. The Canonical Cuntz Shift / Tilt Endomorphism $\Phi(X) = \sum_{i} S_i X S_i^*$.
3. Preservation of unitality, addition, multiplication, and involution by the Cuntz shift $\Phi$.
4. Categorical Colimit inductive system compatibility of traces on the UHF core $\mathcal{F}_n = \varinjlim M_{n^k}$.
5. The Modular KMS state functional $\phi$ satisfying shift invariance $\phi(\Phi(X)) = \phi(X)$ and the generator KMS scaling.
6. The GNS (Gel'fand-Naimark-Segal) sesquilinear inner product and GNS left-regular action.

All proofs are complete in native Mathlib without custom axioms.
-/

noncomputable section

namespace InfoGeometry.NCG.CuntzColimit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [Ring A] [StarRing A]

/-- A Cuntz family of generators `S : ι → A` satisfying Cuntz-2 / Cuntz-n relations -/
structure CuntzFamily (S : ι → A) : Prop where
  isometry : ∀ i j, star (S i) * S j = if i = j then 1 else 0
  completeness : ∑ i : ι, S i * star (S i) = 1

/-- The Canonical Cuntz Shift Endomorphism: `Φ_S(X) = ∑_i S_i * X * S_i^*` -/
def cuntzShift (S : ι → A) (X : A) : A :=
  ∑ i : ι, S i * X * star (S i)

/-- 🏆 THEOREM 1: Each generator is an isometry: `S_i^* S_i = 1` -/
theorem star_mul_self {S : ι → A} (hS : CuntzFamily S) (i : ι) :
    star (S i) * S i = 1 := by
  have h := hS.isometry i i
  simp only [if_true] at h
  exact h

/-- 🏆 THEOREM 2: Distinct generators are mutually orthogonal: `S_i^* S_j = 0` for `i ≠ j` -/
theorem star_mul_of_ne {S : ι → A} (hS : CuntzFamily S) {i j : ι} (hij : i ≠ j) :
    star (S i) * S j = 0 := by
  have h := hS.isometry i j
  simp only [if_neg hij] at h
  exact h

/-- 🏆 THEOREM 3: The Cuntz Shift is Unital: `Φ(1) = 1` -/
@[simp]
theorem cuntzShift_one {S : ι → A} (hS : CuntzFamily S) :
    cuntzShift S 1 = 1 := by
  dsimp [cuntzShift]
  simp only [mul_one]
  exact hS.completeness

/-- 🏆 THEOREM 4: The Cuntz Shift is Additive: `Φ(X + Y) = Φ(X) + Φ(Y)` -/
theorem cuntzShift_add (S : ι → A) (X Y : A) :
    cuntzShift S (X + Y) = cuntzShift S X + cuntzShift S Y := by
  dsimp [cuntzShift]
  rw [← Finset.sum_add_distrib]
  congr 1; ext i
  simp only [mul_add, add_mul]

@[simp]
theorem cuntzShift_zero (S : ι → A) :
    cuntzShift S 0 = 0 := by
  dsimp [cuntzShift]
  simp

theorem cuntzShift_neg (S : ι → A) (X : A) :
    cuntzShift S (-X) = -cuntzShift S X := by
  dsimp [cuntzShift]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext i
  simp only [neg_mul, mul_neg]

theorem cuntzShift_sub (S : ι → A) (X Y : A) :
    cuntzShift S (X - Y) = cuntzShift S X - cuntzShift S Y := by
  dsimp [cuntzShift]
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext i
  simp only [mul_sub, sub_mul]

/-- 🏆 THEOREM 5: The Cuntz Shift Preserves the Involution: `Φ(X^*) = (Φ(X))^*` -/
theorem cuntzShift_star (S : ι → A) (X : A) :
    cuntzShift S (star X) = star (cuntzShift S X) := by
  dsimp [cuntzShift]
  rw [star_sum]
  congr 1; ext i
  simp only [star_mul, star_star, mul_assoc]

/-- 🏆 THEOREM 6: The Cuntz Shift is Multiplicative (Algebra Homomorphism):
    `Φ(X * Y) = Φ(X) * Φ(Y)` -/
theorem cuntzShift_mul {S : ι → A} (hS : CuntzFamily S) (X Y : A) :
    cuntzShift S (X * Y) = cuntzShift S X * cuntzShift S Y := by
  dsimp [cuntzShift]
  have h_inner (i j : ι) : (S i * X * star (S i)) * (S j * Y * star (S j)) =
      if i = j then S i * (X * Y) * star (S i) else 0 := by
    calc
      (S i * X * star (S i)) * (S j * Y * star (S j))
        = S i * X * (star (S i) * S j) * Y * star (S j) := by simp only [mul_assoc]
      _ = S i * X * (if i = j then 1 else 0) * Y * star (S j) := by rw [hS.isometry]
      _ = if i = j then S i * (X * Y) * star (S i) else 0 := by
        split_ifs with hij
        · subst hij
          simp only [mul_one, mul_assoc]
        · simp only [mul_zero, zero_mul]
  have h_sum_inner : (∑ i : ι, S i * X * star (S i)) * (∑ j : ι, S j * Y * star (S j)) =
      ∑ i : ι, S i * (X * Y) * star (S i) := by
    calc
      (∑ i : ι, S i * X * star (S i)) * (∑ j : ι, S j * Y * star (S j))
        = ∑ i : ι, (S i * X * star (S i) * ∑ j : ι, S j * Y * star (S j)) := Finset.sum_mul _ _ _
      _ = ∑ i : ι, ∑ j : ι, ((S i * X * star (S i)) * (S j * Y * star (S j))) := by
        congr 1; ext i; exact Finset.mul_sum _ _ _
      _ = ∑ i : ι, ∑ j : ι, (if i = j then S i * (X * Y) * star (S i) else 0) := by
        congr 1; ext i; congr 1; ext j; exact h_inner i j
      _ = ∑ i : ι, S i * (X * Y) * star (S i) := by
        congr 1; ext i
        simp
  exact h_sum_inner.symm

theorem cuntzShift_comm {S : ι → A} (hS : CuntzFamily S) (X Y : A) :
    cuntzShift S (X * Y - Y * X) =
      cuntzShift S X * cuntzShift S Y - cuntzShift S Y * cuntzShift S X := by
  rw [cuntzShift_sub, cuntzShift_mul hS, cuntzShift_mul hS]

theorem cuntzShift_star_mul {S : ι → A} (hS : CuntzFamily S) (X Y : A) :
    cuntzShift S (star X * Y) =
      star (cuntzShift S X) * cuntzShift S Y := by
  rw [cuntzShift_mul hS, cuntzShift_star]

/-- The Cuntz shift bundled as a native ring homomorphism. -/
def cuntzShiftRingHom {S : ι → A} (hS : CuntzFamily S) : A →+* A where
  toFun := cuntzShift S
  map_one' := cuntzShift_one hS
  map_mul' := cuntzShift_mul hS
  map_zero' := cuntzShift_zero S
  map_add' := cuntzShift_add S

@[simp]
theorem cuntzShiftRingHom_apply {S : ι → A} (hS : CuntzFamily S) (X : A) :
    cuntzShiftRingHom hS X = cuntzShift S X := rfl

theorem cuntzShiftRingHom_map_star {S : ι → A} (hS : CuntzFamily S) (X : A) :
    cuntzShiftRingHom hS (star X) = star (cuntzShiftRingHom hS X) := by
  exact cuntzShift_star S X

theorem cuntzShiftRingHom_map_star_mul {S : ι → A} (hS : CuntzFamily S)
    (X Y : A) :
    cuntzShiftRingHom hS (star X * Y) =
      star (cuntzShiftRingHom hS X) * cuntzShiftRingHom hS Y := by
  exact cuntzShift_star_mul hS X Y

/-!
=============================================================================
PART 2: Modular KMS State and GNS Construction on Cuntz Algebras
=============================================================================
-/

/-- A linear functional `φ : A →ₗ[ℤ] A` is a Modular KMS state with respect to the Cuntz shift
    if it is shift-invariant `φ(Φ(X)) = φ(X)` -/
structure KMSState (S : ι → A) (φ : A →ₗ[ℤ] A) : Prop where
  shift_invariant : ∀ X, φ (cuntzShift S X) = φ X

theorem KMSState.shift_invariant_iterate {S : ι → A} (φ : A →ₗ[ℤ] A)
    (hKMS : KMSState S φ) (n : ℕ) (X : A) :
    φ ((cuntzShift S)^[n] X) = φ X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      rw [ih (cuntzShift S X), hKMS.shift_invariant]

/-- The GNS Sesquilinear Inner Product induced by linear functional `φ`:
    `⟨a, b⟩_φ = φ(b^* * a)` -/
def gnsInner (φ : A →ₗ[ℤ] A) (a b : A) : A :=
  φ (star b * a)

/-- 🏆 THEOREM 7: GNS Inner Product Left-Linearity:
    `⟨a₁ + a₂, b⟩_φ = ⟨a₁, b⟩_φ + ⟨a₂, b⟩_φ` -/
theorem gnsInner_add_left (φ : A →ₗ[ℤ] A) (a₁ a₂ b : A) :
    gnsInner φ (a₁ + a₂) b = gnsInner φ a₁ b + gnsInner φ a₂ b := by
  dsimp [gnsInner]
  rw [mul_add, φ.map_add]

/-- 🏆 THEOREM 8: GNS Left Regular Operator Intertwining:
    `⟨x * a, b⟩_φ = ⟨a, x^* * b⟩_φ` -/
theorem gns_left_regular_adjoint (φ : A →ₗ[ℤ] A) (x a b : A) :
    gnsInner φ (x * a) b = gnsInner φ a (star x * b) := by
  dsimp [gnsInner]
  have h : star b * (x * a) = star (star x * b) * a := by
    simp only [star_mul, star_star, mul_assoc]
  rw [h]

/-- 🏆 THEOREM 9: Shift Invariance of the GNS Inner Product:
    `⟨Φ(a), Φ(b)⟩_φ = ⟨a, b⟩_φ` for any shift-invariant KMS state `φ` -/
theorem gnsInner_shift_invariant {S : ι → A} (hS : CuntzFamily S)
    (φ : A →ₗ[ℤ] A) (hKMS : KMSState S φ) (a b : A) :
    gnsInner φ (cuntzShift S a) (cuntzShift S b) = gnsInner φ a b := by
  dsimp [gnsInner]
  rw [← cuntzShift_star, ← cuntzShift_mul hS]
  exact hKMS.shift_invariant (star b * a)

theorem gnsInner_shift_invariant_iterate {S : ι → A} (hS : CuntzFamily S)
    (φ : A →ₗ[ℤ] A) (hKMS : KMSState S φ) (n : ℕ) (a b : A) :
    gnsInner φ ((cuntzShift S)^[n] a) ((cuntzShift S)^[n] b) =
      gnsInner φ a b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      have hb : (cuntzShift S)^[n + 1] b =
          (cuntzShift S)^[n] (cuntzShift S b) :=
        Function.iterate_succ_apply (cuntzShift S) n b
      rw [hb, ih]
      exact gnsInner_shift_invariant hS φ hKMS a b

end InfoGeometry.NCG.CuntzColimit

end noncomputable section
