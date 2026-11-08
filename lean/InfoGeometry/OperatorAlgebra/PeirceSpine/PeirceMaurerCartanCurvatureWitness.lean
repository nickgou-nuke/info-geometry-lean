/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Curvature of the Peirce unipotent Maurer–Cartan form

For the inner derivation `d = [P, ·]` and the unipotent `U = 1 + N₊`, the
Maurer–Cartan form is `N₊`. Its curvature is therefore `N₊`, not zero in
general. This records the exact scope of the flatness condition `d²(U) = 0`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Left Maurer–Cartan form of an operator with a specified inverse. -/
def peirceMaurerCartanForm (d : B → B) (U Uinv : B) : B := Uinv * d U

/-- For the Peirce unipotent `1 + N₊`, the curvature `dω + ω²` of its left
Maurer–Cartan form for `d = [P, ·]` is exactly `N₊`. -/
theorem peirce_unipotent_maurer_cartan_curvature_eq_conePlus
    {P : B} (hP : P * P = P) (A : B) :
    comm P (peirceMaurerCartanForm (comm P) (1 + conePlus P A)
      (1 - conePlus P A)) +
      peirceMaurerCartanForm (comm P) (1 + conePlus P A)
        (1 - conePlus P A) *
      peirceMaurerCartanForm (comm P) (1 + conePlus P A)
        (1 - conePlus P A) =
      conePlus P A := by
  unfold peirceMaurerCartanForm comm conePlus
  peirce_nf hP

/-- Consequently, this Peirce Maurer–Cartan form is nonflat whenever its
off-diagonal corner generator is nonzero. -/
theorem peirce_unipotent_nonflat_of_conePlus_ne_zero
    {P : B} (hP : P * P = P) (A : B)
    (hN : conePlus P A ≠ 0) :
    comm P (peirceMaurerCartanForm (comm P) (1 + conePlus P A)
      (1 - conePlus P A)) +
      peirceMaurerCartanForm (comm P) (1 + conePlus P A)
        (1 - conePlus P A) *
      peirceMaurerCartanForm (comm P) (1 + conePlus P A)
        (1 - conePlus P A) ≠ 0 := by
  rw [peirce_unipotent_maurer_cartan_curvature_eq_conePlus hP A]
  exact hN

/-! ### Concrete matrix counterexample -/

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℤ

/-- A nontrivial Peirce idempotent in the integral two-by-two matrix ring. -/
def curvatureWitnessP : Mat2 :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

def curvatureWitnessE10 : Mat2 :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- The integral matrix carrier used for the curvature example is genuinely
noncommutative. -/
theorem curvatureWitness_noncommutative_witness :
    curvatureWitnessP * curvatureWitnessE10 ≠
      curvatureWitnessE10 * curvatureWitnessP := by
  decide

/-- An upper-corner matrix unit for `curvatureWitnessP`. -/
def curvatureWitnessA : Mat2 :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

theorem curvatureWitnessP_idempotent :
    curvatureWitnessP * curvatureWitnessP = curvatureWitnessP := by
  decide

theorem curvatureWitness_conePlus :
    conePlus curvatureWitnessP curvatureWitnessA = curvatureWitnessA := by
  decide

/-- In this genuinely noncommutative matrix carrier, the Peirce unipotent
Maurer–Cartan form is not flat: its curvature is the nonzero matrix unit. -/
theorem peirce_matrix_unipotent_maurer_cartan_nonflat :
    comm curvatureWitnessP
        (peirceMaurerCartanForm (comm curvatureWitnessP)
          (1 + conePlus curvatureWitnessP curvatureWitnessA)
          (1 - conePlus curvatureWitnessP curvatureWitnessA)) +
      peirceMaurerCartanForm (comm curvatureWitnessP)
        (1 + conePlus curvatureWitnessP curvatureWitnessA)
        (1 - conePlus curvatureWitnessP curvatureWitnessA) *
      peirceMaurerCartanForm (comm curvatureWitnessP)
        (1 + conePlus curvatureWitnessP curvatureWitnessA)
        (1 - conePlus curvatureWitnessP curvatureWitnessA) ≠ 0 := by
  rw [peirce_unipotent_maurer_cartan_curvature_eq_conePlus
    curvatureWitnessP_idempotent curvatureWitnessA, curvatureWitness_conePlus]
  decide

end InfoGeometry.OperatorAlgebra.PeirceSpine
