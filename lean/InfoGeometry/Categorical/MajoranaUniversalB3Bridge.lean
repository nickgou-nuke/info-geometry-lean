import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Integer

import InfoGeometry.Categorical.UniversalArtinBraidRepresentation
import InfoGeometry.Topology.MajoranaBraidGroup

/-!
# Majorana B₃ representation through the universal Artin engine

The existing finite Majorana owner provides two 8×8 integer braid matrices
`braid12`, `braid23` satisfying the Artin relation, together with inverse
numerators whose products are `2 I`.

Over `ℚ`, dividing those inverse numerators by two gives genuine inverses.
This module packages the resulting units into
`UniversalArtinBraidRepresentation.ArtinBraidSystem` for `m = 2`, hence
obtains a canonical representation

  B₃ →* (Matrix (Fin 8) (Fin 8) ℚ)ˣ.

This is the first concrete operator-valued canary for the universal braid
representation API.  It does not assert a general n-strand Clifford formula.
-/

noncomputable section

namespace InfoGeometry.Categorical.MajoranaUniversalB3Bridge

open Braid
open InfoGeometry.Categorical.UniversalArtinBraidRepresentation
open InfoGeometry.GrandUnification.MajoranaBraidGroup

abbrev M8Q := Matrix (Fin 8) (Fin 8) ℚ

/-- Entrywise rational lift of an integer 8×8 matrix. -/
def ratLift (A : M8Z) : M8Q :=
  A.map (Int.cast : ℤ → ℚ)

@[simp] theorem ratLift_add (A B : M8Z) :
    ratLift (A + B) = ratLift A + ratLift B := by
  ext i j
  simp [ratLift]

@[simp] theorem ratLift_mul (A B : M8Z) :
    ratLift (A * B) = ratLift A * ratLift B := by
  exact Matrix.map_mul_intCast A B

@[simp] theorem ratLift_one :
    ratLift (1 : M8Z) = (1 : M8Q) := by
  exact Matrix.map_one (Int.cast : ℤ → ℚ) Int.cast_zero Int.cast_one

@[simp] theorem ratLift_zsmul (n : ℤ) (A : M8Z) :
    ratLift (n • A) = (n : ℚ) • ratLift A := by
  ext i j
  simp [ratLift]

def braid12Q : M8Q := ratLift braid12
def braid23Q : M8Q := ratLift braid23

def braid12InvQ : M8Q := (1 / 2 : ℚ) • ratLift braid12InvNumerator
def braid23InvQ : M8Q := (1 / 2 : ℚ) • ratLift braid23InvNumerator

theorem braid12Q_mul_inv :
    braid12Q * braid12InvQ = 1 := by
  rw [braid12Q, braid12InvQ, ← Matrix.mul_smul]
  rw [← ratLift_mul, majorana_projective_inverses.1, ratLift_zsmul, ratLift_one]
  norm_num

theorem braid23Q_mul_inv :
    braid23Q * braid23InvQ = 1 := by
  rw [braid23Q, braid23InvQ, ← Matrix.mul_smul]
  rw [← ratLift_mul, majorana_projective_inverses.2, ratLift_zsmul, ratLift_one]
  norm_num

theorem braid12InvQ_mul :
    braid12InvQ * braid12Q = 1 := by
  native_decide

theorem braid23InvQ_mul :
    braid23InvQ * braid23Q = 1 := by
  native_decide

/-- Genuine rational unit lifting the first finite Majorana braid generator. -/
def braid12Unit : Units M8Q where
  val := braid12Q
  inv := braid12InvQ
  val_inv := braid12Q_mul_inv
  inv_val := braid12InvQ_mul

/-- Genuine rational unit lifting the second finite Majorana braid generator. -/
def braid23Unit : Units M8Q where
  val := braid23Q
  inv := braid23InvQ
  val_inv := braid23Q_mul_inv
  inv_val := braid23InvQ_mul

/-- The integer Majorana Artin identity lifts exactly to rational matrices. -/
theorem majoranaQ_adjacent_artin :
    braid12Q * braid23Q * braid12Q =
      braid23Q * braid12Q * braid23Q := by
  have h := congrArg ratLift majorana_adjacent_artin
  simpa [braid12Q, braid23Q, ratLift_mul] using h

/-- The two rational Majorana units satisfy the B₃ Artin relation. -/
theorem majoranaUnit_adjacent_artin :
    braid12Unit * braid23Unit * braid12Unit =
      braid23Unit * braid12Unit * braid23Unit := by
  apply Units.ext
  exact majoranaQ_adjacent_artin

/-- The existing concrete two-generator Majorana lane packaged as a universal
Artin braid system. -/
def majoranaArtinSystem :
    ArtinBraidSystem (Units M8Q) 2 where
  gen i := if i = 0 then braid12Unit else braid23Unit
  adjacent i j hij := by
    fin_cases i <;> fin_cases j
    · omega
    · simpa using majoranaUnit_adjacent_artin
    · omega
    · omega
  farCommute i j hij := by
    fin_cases i <;> fin_cases j <;> omega

/-- Canonical universal Majorana representation of B₃. -/
def majoranaB3Hom :
    braid_group 3 →* Units M8Q :=
  majoranaArtinSystem.toGroupHom

@[simp] theorem majoranaB3Hom_sigma0 :
    majoranaB3Hom (σ' 2 (0 : Fin 2)) = braid12Unit := by
  simpa [majoranaB3Hom, majoranaArtinSystem] using
    ArtinBraidSystem.toGroupHom_generator majoranaArtinSystem (0 : Fin 2)

@[simp] theorem majoranaB3Hom_sigma1 :
    majoranaB3Hom (σ' 2 (1 : Fin 2)) = braid23Unit := by
  simpa [majoranaB3Hom, majoranaArtinSystem] using
    ArtinBraidSystem.toGroupHom_generator majoranaArtinSystem (1 : Fin 2)

/-- Deduplication principle: any legacy B₃ homomorphism with the same two
Majorana generator images is definitionally forced to equal the universal one. -/
theorem majoranaB3Hom_unique
    (legacy : braid_group 3 →* Units M8Q)
    (h0 : legacy (σ' 2 (0 : Fin 2)) = braid12Unit)
    (h1 : legacy (σ' 2 (1 : Fin 2)) = braid23Unit) :
    legacy = majoranaB3Hom := by
  apply ArtinBraidSystem.toGroupHom_unique majoranaArtinSystem legacy
  intro i
  fin_cases i
  · exact h0
  · exact h1

end InfoGeometry.Categorical.MajoranaUniversalB3Bridge
