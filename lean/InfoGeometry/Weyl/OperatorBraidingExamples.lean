/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Weyl.OperatorBraiding
import InfoGeometry.Core.ParabolicShearRelations
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A noncentral operator-valued braiding witness

Two integer transvection units label the edges and vertices of a two-vertex
swap. The coefficient ring is `M₂(ℤ)` and the clock/shift carrier is
`M₂(M₂(ℤ))`. The resulting holonomy coefficient is neither scalar nor central.
-/

namespace InfoGeometry.Weyl.OperatorBraidingExamples

open Matrix OperatorBraiding

abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ

def upperUnit : Coeffˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

def lowerUnit : Coeffˣ where
  val := !![1, 0; 1, 1]
  inv := !![1, 0; -1, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

def swapVertices : Equiv.Perm (Fin 2) := Equiv.swap 0 1
def edgeLabels : Fin 2 → Coeffˣ := fun _ => upperUnit
def vertexLabels : Fin 2 → Coeffˣ := fun _ => lowerUnit

/-- The coefficient labels themselves do not commute. -/
theorem coefficient_units_noncommute : ¬ Commute upperUnit lowerUnit := by
  intro h
  have hh := congrArg (fun u : Coeffˣ => (u : Coeff) 0 0) h.eq
  norm_num [upperUnit, lowerUnit, Matrix.mul_apply, Fin.sum_univ_two] at hh

/-- Explicit ordered plaquette readout at the first vertex. -/
theorem holonomy_value :
    ((braidingHolonomy swapVertices edgeLabels vertexLabels 0 : Coeffˣ) : Coeff) =
      !![0, 1; -1, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [braidingHolonomy_apply, edgeLabels, vertexLabels,
      upperUnit, lowerUnit, Matrix.mul_apply, Fin.sum_univ_two]

/-- The off-diagonal entry excludes every scalar multiple of the identity. -/
theorem holonomy_not_scalar (z : ℤ) :
    ((braidingHolonomy swapVertices edgeLabels vertexLabels 0 : Coeffˣ) : Coeff) ≠
      Matrix.scalar (Fin 2) z := by
  intro h
  have hh := congrArg (fun M : Coeff => M 0 1) h
  rw [holonomy_value] at hh
  change (1 : ℤ) = 0 at hh
  norm_num at hh

/-- The holonomy fails to commute with an explicit coefficient-ring element. -/
theorem holonomy_noncentral :
    ¬ Commute ((braidingHolonomy swapVertices edgeLabels vertexLabels 0 : Coeffˣ) : Coeff)
      (upperUnit : Coeff) := by
  intro h
  have hh := congrArg (fun M : Coeff => M 0 0) h.eq
  rw [holonomy_value] at hh
  norm_num [upperUnit, Matrix.mul_apply, Fin.sum_univ_two] at hh

theorem holonomy_ne_one :
    braidingHolonomy swapVertices edgeLabels vertexLabels 0 ≠ 1 := by
  intro h
  have hh := congrArg (fun u : Coeffˣ => (u : Coeff) 0 1) h
  rw [holonomy_value] at hh
  norm_num at hh

/-- Nonflat holonomy forces noncommutation in the unit group of the nested matrix ring. -/
theorem clock_shift_units_noncommute :
    ¬ Commute (clockUnit vertexLabels) (shiftUnit swapVertices edgeLabels) := by
  intro h
  exact holonomy_ne_one ((clockUnit_shiftUnit_commute_iff
    swapVertices edgeLabels vertexLabels).mp h 0)

/-- The same noncommutation in the native ring `M₂(M₂(ℤ))`. -/
theorem clock_shift_matrices_noncommute :
    ¬ Commute (clock vertexLabels) (shift swapVertices edgeLabels) := by
  intro h
  apply clock_shift_units_noncommute
  change clockUnit vertexLabels * shiftUnit swapVertices edgeLabels =
    shiftUnit swapVertices edgeLabels * clockUnit vertexLabels
  apply Units.ext
  exact h.eq

/-! ### Concrete check of the square-zero block holonomy

The nested operator-matrix example checks the proposed block holonomy with
the noncommutative coefficient ring `M₂(ℤ)`. Its two diagonal blocks are
`1 + N₊` and `1 - F₋`, so it realizes the claimed square-zero decomposition.
-/

abbrev NestedCoeff := Matrix (Fin 2) (Fin 2) Coeff

def wittFPlus : Coeff := !![0, 1; 0, 0]
def wittFMinus : Coeff := !![0, 0; 1, 0]
def wittSigma : Coeff := !![0, 1; 1, 0]
def wittGamma : Coeff := !![1, 0; 0, -1]
def proposedNPlus : Coeff := !![-1, -1; 1, 1]

def proposedBlockShift : NestedCoeff :=
  ![![0, 1 - wittFPlus], ![1 + wittFPlus, 0]]

def proposedBlockClock : NestedCoeff :=
  ![![wittSigma, 0], ![0, wittGamma]]

def proposedBlockNilpotent : NestedCoeff :=
  ![![proposedNPlus, 0], ![0, -wittFMinus]]

def proposedBlockHolonomy : NestedCoeff :=
  (proposedBlockClock * proposedBlockShift) *
    (proposedBlockClock * proposedBlockShift)

/-- The lower-right block of the plaquette holonomy is `1 - F₋`. -/
theorem proposedBlockHolonomy_lowerRight :
    proposedBlockHolonomy 1 1 = !![1, 0; -1, 1] := by
  decide

/-- The proposed nilpotent decomposition holds for this nested operator
matrix model over `M₂(ℤ)`. -/
theorem proposedBlockHolonomy_eq_one_add_nilpotent :
    proposedBlockHolonomy = 1 + proposedBlockNilpotent := by
  decide

/-! ### Coefficient extension of the nested block model

The operators above have integer matrix entries.  Applying the canonical
integer-scalar ring hom entrywise, twice, extends this fixed nested operator
model to `M₂(M₂(B))` for every ring `B`.  The proofs below use the actual
matrix-ring homomorphisms, so the coefficient ring remains arbitrary and
noncommutative.
-/

section CoefficientExtension

variable (B : Type*) [Ring B]

abbrev UniversalCoeff := Matrix (Fin 2) (Fin 2) B
abbrev UniversalNested := Matrix (Fin 2) (Fin 2) (UniversalCoeff B)

/-- Entrywise integer scalar extension from `M₂(ℤ)` to `M₂(B)`. -/
def coeffExtension : Coeff →+* UniversalCoeff B :=
  (Int.castRingHom B).mapMatrix

/-- Entrywise extension of the outer matrix ring. -/
def nestedExtension : NestedCoeff →+* UniversalNested B :=
  (coeffExtension B).mapMatrix

def universalBlockShift : UniversalNested B :=
  nestedExtension B proposedBlockShift

def universalBlockClock : UniversalNested B :=
  nestedExtension B proposedBlockClock

def universalBlockNilpotent : UniversalNested B :=
  nestedExtension B proposedBlockNilpotent

def universalBlockHolonomy : UniversalNested B :=
  nestedExtension B proposedBlockHolonomy

theorem universalBlockHolonomy_eq_clockShift_square :
    universalBlockHolonomy B =
      (universalBlockClock B * universalBlockShift B) *
        (universalBlockClock B * universalBlockShift B) := by
  change nestedExtension B
      ((proposedBlockClock * proposedBlockShift) *
        (proposedBlockClock * proposedBlockShift)) =
      (nestedExtension B proposedBlockClock * nestedExtension B proposedBlockShift) *
        (nestedExtension B proposedBlockClock * nestedExtension B proposedBlockShift)
  simp only [RingHom.map_mul]

theorem proposedBlockShift_sq : proposedBlockShift * proposedBlockShift = 1 := by
  decide

theorem proposedBlockClock_sq : proposedBlockClock * proposedBlockClock = 1 := by
  decide

theorem proposedBlockNilpotent_sq :
    proposedBlockNilpotent * proposedBlockNilpotent = 0 := by
  decide

theorem universalBlockShift_sq :
    universalBlockShift B * universalBlockShift B = 1 := by
  change (nestedExtension B proposedBlockShift) *
    (nestedExtension B proposedBlockShift) = 1
  rw [← (nestedExtension B).map_mul, ← (nestedExtension B).map_one]
  exact congrArg (nestedExtension B) proposedBlockShift_sq

theorem universalBlockClock_sq :
    universalBlockClock B * universalBlockClock B = 1 := by
  change (nestedExtension B proposedBlockClock) *
    (nestedExtension B proposedBlockClock) = 1
  rw [← (nestedExtension B).map_mul, ← (nestedExtension B).map_one]
  exact congrArg (nestedExtension B) proposedBlockClock_sq

theorem universalBlockNilpotent_sq :
    universalBlockNilpotent B * universalBlockNilpotent B = 0 := by
  change (nestedExtension B proposedBlockNilpotent) *
    (nestedExtension B proposedBlockNilpotent) = 0
  rw [← (nestedExtension B).map_mul, ← (nestedExtension B).map_zero]
  exact congrArg (nestedExtension B) proposedBlockNilpotent_sq

theorem universalBlockHolonomy_eq_one_add_nilpotent :
    universalBlockHolonomy B = 1 + universalBlockNilpotent B := by
  change nestedExtension B proposedBlockHolonomy =
    1 + nestedExtension B proposedBlockNilpotent
  rw [← (nestedExtension B).map_one, ← (nestedExtension B).map_add,
    proposedBlockHolonomy_eq_one_add_nilpotent]

/-- The nested block holonomy obeys the square-zero Jordan power law over any
noncommutative coefficient ring. -/
theorem universalBlockHolonomy_pow (n : ℕ) :
    universalBlockHolonomy B ^ n = 1 + n • universalBlockNilpotent B := by
  rw [universalBlockHolonomy_eq_one_add_nilpotent]
  exact InfoGeometry.Core.ParabolicShearRelations.shear_pow
    (universalBlockNilpotent B) (universalBlockNilpotent_sq B) n

/-- In characteristic zero, the nested operator holonomy has infinite
multiplicative order: its powers retain the nonzero `(1,0)` coefficient of
the upper-left square-zero block. -/
theorem universalBlockHolonomy_infinite_order [CharZero B]
    (n : ℕ) (hn : 0 < n) : universalBlockHolonomy B ^ n ≠ 1 := by
  intro h
  have hentry : (n : B) = 0 := by
    have he := congrArg (fun M : UniversalNested B => M 0 0 1 0) h
    rw [universalBlockHolonomy_pow] at he
    have hcoeff : (universalBlockNilpotent B) 0 0 1 0 = (1 : B) := by
      change (Int.castRingHom B) (proposedNPlus 1 0) = 1
      simp [proposedNPlus]
    have hcast : (n : B) = 0 := by
      simpa [Matrix.add_apply, Matrix.one_apply, Matrix.natCast_apply,
        Matrix.mul_apply, Fin.sum_univ_two, hcoeff, nsmul_eq_mul] using he
    exact hcast
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) hentry

/-- The product-square phase gives the noncentral braid relation for the
extended clock and shift operators. -/
theorem universalBlock_braiding :
    universalBlockClock B * universalBlockShift B =
      universalBlockHolonomy B * universalBlockShift B * universalBlockClock B := by
  rw [universalBlockHolonomy_eq_clockShift_square]
  noncomm_ring [universalBlockShift_sq B, universalBlockClock_sq B]

end CoefficientExtension

end InfoGeometry.Weyl.OperatorBraidingExamples
