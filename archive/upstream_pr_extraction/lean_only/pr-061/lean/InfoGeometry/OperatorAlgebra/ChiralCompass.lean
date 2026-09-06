/-
Copyright (c) 2024 InfoGeometry Contributors.
All rights reserved.

Chiral Compasses: Cl(1,1) ⊗ Cl(1,1) ≅ Cl(2,2)
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

open TensorProduct

namespace InfoGeometry.ChiralCompass

variable (R : Type*) [CommRing R] [Invertible (2 : R)]

abbrev Vec11 := Fin 2 → R

abbrev Vec22 := Fin 4 → R

/--
The quadratic form for Cl(1,1), representing a single chiral compass.
Signature (+, -).
-/
def Q11 : QuadraticForm R (Vec11 R) :=
  QuadraticMap.proj 0 0 - QuadraticMap.proj 1 1

/--
The quadratic form for Cl(2,2), representing the combined 4D spacetime.
Signature (+, -, +, -).
-/
def Q22 : QuadraticForm R (Vec22 R) :=
  QuadraticMap.proj 0 0 - QuadraticMap.proj 1 1 +
    QuadraticMap.proj 2 2 - QuadraticMap.proj 3 3

/-- The Clifford algebra for the single chiral compass Cl(1,1). -/
abbrev Cl11 := CliffordAlgebra (Q11 R)

/-- The Clifford algebra for the full (2,2) spacetime. -/
abbrev Cl22 := CliffordAlgebra (Q22 R)

/-- Inclusion of the first split plane into the four-coordinate split space. -/
def leftPlane : Vec11 R →ₗ[R] Vec22 R where
  toFun p := fun i =>
    match i with
    | 0 => p 0
    | 1 => p 1
    | 2 => 0
    | 3 => 0
  map_add' := by
    intro p q
    ext i
    fin_cases i <;> simp
  map_smul' := by
    intro a p
    ext i
    fin_cases i <;> simp

/-- Inclusion of the second split plane into the four-coordinate split space. -/
def rightPlane : Vec11 R →ₗ[R] Vec22 R where
  toFun p := fun i =>
    match i with
    | 0 => 0
    | 1 => 0
    | 2 => p 0
    | 3 => p 1
  map_add' := by
    intro p q
    ext i
    fin_cases i <;> simp
  map_smul' := by
    intro a p
    ext i
    fin_cases i <;> simp

@[simp] theorem Q22_leftPlane (p : Vec11 R) :
    Q22 R (leftPlane R p) = Q11 R p := by
  simp [Q11, Q22, leftPlane]

@[simp] theorem Q22_rightPlane (p : Vec11 R) :
    Q22 R (rightPlane R p) = Q11 R p := by
  simp [Q11, Q22, rightPlane]

/--
The left chiral compass injection.
Maps the first Cl(1,1) generators directly into Cl(2,2).
-/
def leftCompass : Cl11 R →ₐ[R] Cl22 R :=
  CliffordAlgebra.lift (Q11 R)
    ⟨(CliffordAlgebra.ι (Q22 R)).comp (leftPlane R),
     by
       intro p
       change CliffordAlgebra.ι (Q22 R) (leftPlane R p) *
           CliffordAlgebra.ι (Q22 R) (leftPlane R p) =
         algebraMap R (Cl22 R) (Q11 R p)
       rw [CliffordAlgebra.ι_sq_scalar (Q22 R)]
       simp⟩

/--
The right chiral compass injection requires grading by the volume element
of the left compass to ensure anti-commutation across the tensor factors.
This encodes the graded tensor product:
  γ_3 = (γ_1 γ_2) ⊗ γ'_1
  γ_4 = (γ_1 γ_2) ⊗ γ'_2

We model this directly on the generators of the second Cl(1,1).
-/
def rightCompass
    (vol_L : Cl22 R)
    (h_vol_sq : vol_L ^ 2 = 1)
    (h_comm :
      ∀ p : Vec11 R,
        Commute vol_L (CliffordAlgebra.ι (Q22 R) (rightPlane R p))) :
    Cl11 R →ₐ[R] Cl22 R :=
  CliffordAlgebra.lift (Q11 R)
    ⟨{ toFun := fun p => vol_L * CliffordAlgebra.ι (Q22 R) (rightPlane R p)
       map_add' := by
        intro p q
        simp [map_add, mul_add]
       map_smul' := by
        intro a p
        change vol_L * CliffordAlgebra.ι (Q22 R) (rightPlane R (a • p)) =
          a • (vol_L * CliffordAlgebra.ι (Q22 R) (rightPlane R p))
        rw [LinearMap.map_smul, LinearMap.map_smul]
        simp only [Algebra.smul_def]
        rw [← mul_assoc, ← Algebra.commutes a vol_L, mul_assoc] },
     by
       intro p
       calc
         (vol_L * CliffordAlgebra.ι (Q22 R) (rightPlane R p)) *
             (vol_L * CliffordAlgebra.ι (Q22 R) (rightPlane R p))
             = (vol_L ^ 2) *
                 (CliffordAlgebra.ι (Q22 R) (rightPlane R p) *
                  CliffordAlgebra.ι (Q22 R) (rightPlane R p)) := by
                 rw [pow_two]
                 exact (h_comm p).symm.mul_mul_mul_comm vol_L
                   (CliffordAlgebra.ι (Q22 R) (rightPlane R p))
         _ = algebraMap R _ (Q11 R p) := by
               rw [h_vol_sq, one_mul, CliffordAlgebra.ι_sq_scalar]
               simp⟩

/-- The canonical left `Cl(1,1)` compass embedding into `Cl(2,2)`. -/
def chiral_compasses_equivalence :
    Cl11 R →ₐ[R] Cl22 R :=
  leftCompass R

theorem chiral_compasses_equivalence_eq_leftCompass :
    chiral_compasses_equivalence R = leftCompass R :=
  rfl

end InfoGeometry.ChiralCompass
