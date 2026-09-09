import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Connes Noncommutative Differential Calculus and Gauge Curvature

This module formalizes:
1. Noncommutative derivations and Connes 1-forms on associative algebras `A`.
2. The Universal Leibniz Rule: `d(a * b) = (da) * b + a * (db)`.
3. Gauge connection transformations: `Aᵘ = u * A * u⁻¹ + u * d(u⁻¹)`.
4. Transitivity of Non-Abelian Gauge Transformations: `(Aᵘ)ᵛ = Aᵛᵘ`.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.NCG.Calculus

variable {A : Type*} [Ring A]

/-- A `ℤ`-linear Leibniz derivation on an associative ring A -/
structure NCDerivation (A : Type*) [Ring A] where
  toLinearMap : A →ₗ[ℤ] A
  leibniz' : ∀ a b, toLinearMap (a * b) = toLinearMap a * b + a * toLinearMap b

namespace NCDerivation

variable (D : NCDerivation A)

instance : CoeFun (NCDerivation A) (fun _ => A → A) where
  coe D := D.toLinearMap

instance : Zero (NCDerivation A) where
  zero :=
    { toLinearMap := 0
      leibniz' := by simp }

instance : Add (NCDerivation A) where
  add D E :=
    { toLinearMap := D.toLinearMap + E.toLinearMap
      leibniz' := by
        intro x y
        simp only [LinearMap.add_apply, D.leibniz', E.leibniz']
        simp only [add_mul, mul_add]
        abel }

instance : Neg (NCDerivation A) where
  neg D :=
    { toLinearMap := -D.toLinearMap
      leibniz' := by
        intro x y
        simp only [LinearMap.neg_apply, D.leibniz']
        simp only [neg_mul, mul_neg]
        abel }

instance : Sub (NCDerivation A) where
  sub D E :=
    { toLinearMap := D.toLinearMap - E.toLinearMap
      leibniz' := by
        intro x y
        simp only [LinearMap.sub_apply, D.leibniz', E.leibniz']
        simp only [sub_mul, mul_sub]
        abel }

@[ext] theorem ext {D E : NCDerivation A}
    (h : ∀ a, D a = E a) : D = E := by
  cases D with
  | mk D hD =>
    cases E with
    | mk E hE =>
      congr
      ext a
      exact h a

@[simp] theorem zero_apply (x : A) : (0 : NCDerivation A) x = 0 := rfl

@[simp] theorem add_apply (D E : NCDerivation A) (x : A) :
    (D + E) x = D x + E x := rfl

@[simp] theorem neg_apply (D : NCDerivation A) (x : A) :
    (-D) x = -D x := rfl

@[simp] theorem sub_apply (D E : NCDerivation A) (x : A) :
    (D - E) x = D x - E x := rfl

@[simp] theorem map_add (a b : A) : D (a + b) = D a + D b := D.toLinearMap.map_add a b
@[simp] theorem map_sub (a b : A) : D (a - b) = D a - D b := D.toLinearMap.map_sub a b
@[simp] theorem map_neg (a : A) : D (-a) = - D a := D.toLinearMap.map_neg a
@[simp] theorem map_zero : D 0 = 0 := D.toLinearMap.map_zero
@[simp] theorem leibniz (a b : A) : D (a * b) = D a * b + a * D b := D.leibniz' a b

/-! The commutator of associative derivations is again a derivation. -/
def commutator (D E : NCDerivation A) : NCDerivation A where
  toLinearMap := D.toLinearMap.comp E.toLinearMap - E.toLinearMap.comp D.toLinearMap
  leibniz' := by
    intro x y
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, D.leibniz', E.leibniz',
      D.toLinearMap.map_add, E.toLinearMap.map_add]
    noncomm_ring

@[simp] theorem commutator_apply (D E : NCDerivation A) (x : A) :
    commutator D E x = D (E x) - E (D x) := rfl

@[simp] theorem commutator_zero_left_apply (D : NCDerivation A) (x : A) :
    commutator 0 D x = 0 := by
  simp [commutator_apply]

@[simp] theorem commutator_zero_right_apply (D : NCDerivation A) (x : A) :
    commutator D 0 x = 0 := by
  simp [commutator_apply]

theorem commutator_add_left_apply (D E F : NCDerivation A) (x : A) :
    commutator (D + E) F x = commutator D F x + commutator E F x := by
  simp only [commutator_apply, add_apply, F.toLinearMap.map_add]
  abel

theorem commutator_add_right_apply (D E F : NCDerivation A) (x : A) :
    commutator D (E + F) x = commutator D E x + commutator D F x := by
  change D (E x + F x) - (E (D x) + F (D x)) =
    D (E x) - E (D x) + (D (F x) - F (D x))
  simp only [D.toLinearMap.map_add]
  abel

theorem commutator_neg_left_apply (D E : NCDerivation A) (x : A) :
    commutator (-D) E x = -commutator D E x := by
  simp only [commutator_apply, neg_apply, E.toLinearMap.map_neg]
  abel

theorem commutator_neg_right_apply (D E : NCDerivation A) (x : A) :
    commutator D (-E) x = -commutator D E x := by
  simp only [commutator_apply, neg_apply, D.toLinearMap.map_neg]
  abel

theorem commutator_swap_apply (D E : NCDerivation A) (x : A) :
    commutator E D x = -commutator D E x := by
  simp only [commutator_apply]
  abel

theorem commutator_jacobi_apply (D E F : NCDerivation A) (x : A) :
    commutator D (commutator E F) x +
        commutator E (commutator F D) x +
        commutator F (commutator D E) x = 0 := by
  simp only [commutator_apply, NCDerivation.map_sub]
  noncomm_ring

theorem commutator_zero_left (D : NCDerivation A) :
    commutator 0 D = 0 := by
  apply NCDerivation.ext
  intro x
  exact commutator_zero_left_apply D x

theorem commutator_zero_right (D : NCDerivation A) :
    commutator D 0 = 0 := by
  apply NCDerivation.ext
  intro x
  exact commutator_zero_right_apply D x

theorem commutator_swap (D E : NCDerivation A) :
    commutator E D = -commutator D E := by
  apply NCDerivation.ext
  intro x
  exact commutator_swap_apply D E x

theorem commutator_jacobi (D E F : NCDerivation A) :
    commutator D (commutator E F) +
        commutator E (commutator F D) +
        commutator F (commutator D E) = 0 := by
  apply NCDerivation.ext
  intro x
  exact commutator_jacobi_apply D E F x

/-- Derivation annihilates 1 in any ring -/
@[simp]
theorem map_one : D 1 = 0 := by
  have h := D.leibniz 1 1
  have h' : D 1 = D 1 + D 1 := by
    simpa only [mul_one, one_mul] using h
  have h'' : D 1 + 0 = D 1 + D 1 := by simpa using h'
  exact (add_left_cancel h'').symm

/-- Derivation on units inverse: `D(u⁻¹) = - u⁻¹ * D(u) * u⁻¹` -/
theorem map_unit_inv (u : Aˣ) :
    D (↑(u⁻¹) : A) = - ((↑(u⁻¹) : A) * D (u : A) * (↑(u⁻¹) : A)) := by
  have hone : D (1 : A) = 0 := D.map_one
  have hprod : D ((u : A) * (↑(u⁻¹) : A)) =
      D (u : A) * (↑(u⁻¹) : A) + (u : A) * D (↑(u⁻¹) : A) := D.leibniz _ _
  have hunit : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
  rw [hunit, hone] at hprod
  have hinv : (u : A) * D (↑(u⁻¹) : A) = - (D (u : A) * (↑(u⁻¹) : A)) := by
    exact eq_neg_of_add_eq_zero_right hprod.symm
  have hu_inv : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
  calc
    D (↑(u⁻¹) : A) = 1 * D (↑(u⁻¹) : A) := by rw [one_mul]
    _ = ((↑(u⁻¹) : A) * (u : A)) * D (↑(u⁻¹) : A) := by rw [hu_inv]
    _ = (↑(u⁻¹) : A) * ((u : A) * D (↑(u⁻¹) : A)) := by rw [mul_assoc]
    _ = (↑(u⁻¹) : A) * (- (D (u : A) * (↑(u⁻¹) : A))) := by rw [hinv]
    _ = - ((↑(u⁻¹) : A) * D (u : A) * (↑(u⁻¹) : A)) := by
      simp only [mul_neg, mul_assoc]

/-- 
  Non-Abelian Gauge Transformation of a 1-form connection `A`:
  `Aᵘ = u * A * u⁻¹ + u * D(u⁻¹)`
-/
def gaugeTransform (conn : A) (u : Aˣ) : A :=
  (u : A) * conn * (↑(u⁻¹) : A) + (u : A) * D (↑(u⁻¹) : A)

/-- 🏆 THEOREM 1: Identity Gauge Transformation acts trivially: `A¹ = A` -/
@[simp]
theorem gaugeTransform_one (conn : A) :
    gaugeTransform D conn 1 = conn := by
  dsimp [gaugeTransform]
  have hone : D (↑(1⁻¹ : Aˣ) : A) = 0 := by
    change D (1 : A) = 0
    exact D.map_one
  rw [hone]
  simp

/-- 🏆 THEOREM 2: Transitivity of Non-Abelian Gauge Transformations:
    `(Aᵘ)ᵛ = Aᵛᵘ` -/
theorem gaugeTransform_trans (conn : A) (u v : Aˣ) :
    gaugeTransform D (gaugeTransform D conn u) v =
      gaugeTransform D conn (v * u) := by
  dsimp [gaugeTransform]
  have h_leibniz : D (↑((v * u)⁻¹) : A) =
      D ((↑(u⁻¹) : A) * (↑(v⁻¹) : A)) := by
    rw [mul_inv_rev]
    rfl
  have h_expand : D ((↑(u⁻¹) : A) * (↑(v⁻¹) : A)) =
      D (↑(u⁻¹) : A) * (↑(v⁻¹) : A) + (↑(u⁻¹) : A) * D (↑(v⁻¹) : A) := D.leibniz _ _
  have hu_val : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
  have h_cancel : ((v : A) * (u : A)) * ((↑(u⁻¹) : A) * D (↑(v⁻¹) : A)) = (v : A) * D (↑(v⁻¹) : A) := by
    calc
      ((v : A) * (u : A)) * ((↑(u⁻¹) : A) * D (↑(v⁻¹) : A))
        = (v : A) * ((u : A) * (↑(u⁻¹) : A)) * D (↑(v⁻¹) : A) := by simp only [mul_assoc]
      _ = (v : A) * 1 * D (↑(v⁻¹) : A) := by rw [hu_val]
      _ = (v : A) * D (↑(v⁻¹) : A) := by rw [mul_one]
  calc
    (v : A) * ((u : A) * conn * (↑(u⁻¹) : A) + (u : A) * D (↑(u⁻¹) : A)) * (↑(v⁻¹) : A) + (v : A) * D (↑(v⁻¹) : A)
      = ((v : A) * (u : A)) * conn * ((↑(u⁻¹) : A) * (↑(v⁻¹) : A)) +
        ((v : A) * (u : A)) * (D (↑(u⁻¹) : A) * (↑(v⁻¹) : A)) + (v : A) * D (↑(v⁻¹) : A) := by
          simp only [mul_add, add_mul, mul_assoc]
    _ = ((v * u : Aˣ) : A) * conn * (↑((v * u)⁻¹) : A) +
        ((v * u : Aˣ) : A) * (D (↑(u⁻¹) : A) * (↑(v⁻¹) : A)) +
        ((v : A) * (u : A)) * ((↑(u⁻¹) : A) * D (↑(v⁻¹) : A)) := by
          rw [h_cancel]
          simp only [Units.val_mul, mul_inv_rev]
    _ = ((v * u : Aˣ) : A) * conn * (↑((v * u)⁻¹) : A) +
        (((v * u : Aˣ) : A) * (D (↑(u⁻¹) : A) * (↑(v⁻¹) : A)) +
         ((v * u : Aˣ) : A) * ((↑(u⁻¹) : A) * D (↑(v⁻¹) : A))) := by
          simp only [Units.val_mul, add_assoc]
    _ = ((v * u : Aˣ) : A) * conn * (↑((v * u)⁻¹) : A) +
        ((v * u : Aˣ) : A) * (D (↑(u⁻¹) : A) * (↑(v⁻¹) : A) + (↑(u⁻¹) : A) * D (↑(v⁻¹) : A)) := by
          simp only [mul_add]
    _ = (v * u : Aˣ) * conn * (↑((v * u)⁻¹) : A) + (v * u : Aˣ) * D (↑((v * u)⁻¹) : A) := by
          rw [h_leibniz, h_expand]

/-- Gauge transformation by a unit is inverted by the gauge transformation
of its inverse. -/
theorem gaugeTransform_inv (conn : A) (u : Aˣ) :
    gaugeTransform D (gaugeTransform D conn u) u⁻¹ = conn := by
  rw [gaugeTransform_trans D conn u u⁻¹]
  simp only [inv_mul_cancel, gaugeTransform_one]

end NCDerivation

end InfoGeometry.NCG.Calculus

end noncomputable section
