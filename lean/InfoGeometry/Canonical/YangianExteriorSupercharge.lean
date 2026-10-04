import Mathlib
import InfoGeometry.Canonical.KahlerAtiyahCartanForms

/-!
# Finite supertwistor fermions on the exterior algebra

This module realizes the fermionic coordinate derivatives as Mathlib's
contraction operators on an exterior algebra.  It proves the local operator
identity that a product of two odd contractions commutes with a single odd
contraction.  This is a concrete finite operator calculation; by itself it is
not the full `psu(2,2|4)` Yangian representation or an amplitude-invariance
theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.YangianExteriorSupercharge

open InfoGeometry.Canonical.KahlerAtiyahCartanForms

variable (n : ℕ)

/-- The odd coordinate directions for `n` particles and four fermionic labels. -/
abbrev FermionCoordinates := (Fin n × Fin 4) → ℝ

/-- The native exterior-algebra carrier of the finite fermionic state space. -/
abbrev SuperTwistorForms := ExteriorAlgebra ℝ (FermionCoordinates n)

/-- Endomorphisms of the finite fermionic state space. -/
abbrev SuperTwistorEnd := Module.End ℝ (SuperTwistorForms n)

/-- Evaluation at one fermionic coordinate, as a native linear functional. -/
def coordinateCovector (i : Fin n) (A : Fin 4) :
    Module.Dual ℝ (FermionCoordinates n) where
  toFun := fun x => x (i, A)
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

/-- The odd coordinate derivative is exterior-algebra contraction. -/
def fermionicDerivative (i : Fin n) (A : Fin 4) : SuperTwistorEnd n :=
  contractionOperator (coordinateCovector n i A)

/-- The level-zero fermionic supercharge contribution from particle `i`. -/
def levelZeroTerm (z : Fin n → Fin 4 → ℝ) (a A : Fin 4) (i : Fin n) :
    SuperTwistorEnd n :=
  (z i a) • fermionicDerivative n i A

/-- The antisymmetric bosonic twistor minor used as a bilocal coefficient. -/
def twistorMinor (z : Fin n → Fin 4 → ℝ) (a b : Fin 4)
    (i j : Fin n) : ℝ :=
  z i a * z j b - z j a * z i b

/-- A bilocal fermionic term: a bosonic minor times two odd contractions. -/
def bilocalTerm (z : Fin n → Fin 4 → ℝ) (a b A B : Fin 4)
    (i j : Fin n) : SuperTwistorEnd n :=
  (twistorMinor n z a b i j) •
    (fermionicDerivative n i A * fermionicDerivative n j B)

/-- Coordinate contractions anticommute, by Mathlib's exterior contraction law. -/
theorem fermionicDerivative_swap (i j : Fin n) (A B : Fin 4) :
    fermionicDerivative n i A * fermionicDerivative n j B =
      -(fermionicDerivative n j B * fermionicDerivative n i A) := by
  have h := contractionOperator_anticommutator_zero
    (coordinateCovector n i A) (coordinateCovector n j B)
  exact eq_neg_of_add_eq_zero_left h

private theorem product_comm_of_pairwise_anticommute
    {A : Type*} [Ring A] (x y z : A)
    (hyz : y * z = -(z * y)) (hxz : x * z = -(z * x)) :
    (x * y) * z = z * (x * y) := by
  calc
    (x * y) * z = x * (y * z) := mul_assoc x y z
    _ = x * (-(z * y)) := by rw [hyz]
    _ = -(x * (z * y)) := by rw [mul_neg]
    _ = -((x * z) * y) := by rw [mul_assoc]
    _ = -((-(z * x)) * y) := by rw [hxz]
    _ = (z * x) * y := by simp
    _ = z * (x * y) := mul_assoc z x y

/-- A product of two fermionic derivatives commutes with every fermionic
derivative. This remains valid when coordinate indices coincide, since the
native contraction anticommutator law covers that case as well. -/
theorem contractionPair_commutes (i j k : Fin n) (A B C : Fin 4) :
    (fermionicDerivative n i A * fermionicDerivative n j B) *
        fermionicDerivative n k C =
      fermionicDerivative n k C *
        (fermionicDerivative n i A * fermionicDerivative n j B) := by
  exact product_comm_of_pairwise_anticommute
    (fermionicDerivative n i A) (fermionicDerivative n j B)
    (fermionicDerivative n k C)
    (fermionicDerivative_swap n j k B C)
    (fermionicDerivative_swap n i k A C)

private theorem smul_mul_smul
    {A : Type*} [Ring A] [Algebra ℝ A]
    (r s : ℝ) (x y : A) :
    (r • x) * (s • y) = (r * s) • (x * y) := by
  calc
    (r • x) * (s • y) = r • (x * (s • y)) := Algebra.smul_mul_assoc r x _
    _ = r • (s • (x * y)) := by rw [Algebra.mul_smul_comm]
    _ = (r * s) • (x * y) := smul_smul r s (x * y)

/-- One bilocal fermionic term commutes with one level-zero fermionic term. -/
theorem bilocalTerm_commutes_levelZeroTerm
    (z : Fin n → Fin 4 → ℝ) (a b A B C : Fin 4) (i j k : Fin n) :
    bilocalTerm n z a b A B i j * levelZeroTerm n z a C k =
      levelZeroTerm n z a C k * bilocalTerm n z a b A B i j := by
  change (twistorMinor n z a b i j •
      (fermionicDerivative n i A * fermionicDerivative n j B)) *
    ((z k a) • fermionicDerivative n k C) = _
  calc
    _ = (twistorMinor n z a b i j * z k a) •
        ((fermionicDerivative n i A * fermionicDerivative n j B) *
          fermionicDerivative n k C) := smul_mul_smul _ _ _ _
    _ = (z k a * twistorMinor n z a b i j) •
        (fermionicDerivative n k C *
          (fermionicDerivative n i A * fermionicDerivative n j B)) := by
      rw [mul_comm (twistorMinor n z a b i j) (z k a), contractionPair_commutes]
    _ = ((z k a) • fermionicDerivative n k C) *
        (twistorMinor n z a b i j •
          (fermionicDerivative n i A * fermionicDerivative n j B)) :=
      (smul_mul_smul _ _ _ _).symm

end InfoGeometry.Canonical.YangianExteriorSupercharge

end noncomputable section
