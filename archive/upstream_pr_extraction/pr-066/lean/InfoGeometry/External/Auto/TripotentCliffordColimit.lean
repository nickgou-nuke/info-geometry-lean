import Mathlib.Tactic

/-!
# Tripotent trifactor geometry and a finite diagonal scale model

This module formalizes the stable algebraic skeleton of the prompt:

* split-octonion imaginary directions have a Cartan-like sign split:
  quaternionic compact units square to `-1`, split units square to `+1`;
* the split `(4,4)` quadratic form has a concrete nonzero null vector;
* the tripotent scale operator `T=diag(1,-1,0)` satisfies `T³=T`;
* a finite diagonal matrix model of the scale/tripotent invariant, modeled
  concretely as duplicating each sector (`T ↦ T⊗I₂`, represented as
  `diag(1,1,-1,-1,0,0)`), preserves tripotency;
* the stated results are the finite algebraic identities themselves.

This is not a full Clifford/CAR embedding or a CAR representation.
-/

noncomputable section

namespace TripotentCliffordColimit

open Matrix

/-! ## Split-octonion Cartan sign skeleton -/

inductive ImagUnit where
  | e1 | e2 | e3 | e4 | e5 | e6 | e7
  deriving DecidableEq, Repr

open ImagUnit

/-- Square sign of imaginary split-octonion basis units. -/
def squareSign : ImagUnit → ℤ
  | e1 | e2 | e3 => -1
  | e4 | e5 | e6 | e7 => 1

/-- Compact/quaternionic sector has square sign `-1`. -/
theorem compact_square_sign : squareSign e1 = -1 ∧ squareSign e2 = -1 ∧ squareSign e3 = -1 := by
  simp [squareSign]

/-- Split/noncompact sector has square sign `+1`. -/
theorem split_square_sign :
    squareSign e4 = 1 ∧ squareSign e5 = 1 ∧ squareSign e6 = 1 ∧ squareSign e7 = 1 := by
  simp [squareSign]

/-- Coordinates for the split `(4,4)` quadratic form. -/
structure Split8 where
  x0 : ℂ
  x1 : ℂ
  x2 : ℂ
  x3 : ℂ
  x4 : ℂ
  x5 : ℂ
  x6 : ℂ
  x7 : ℂ

/-- Split `(4,4)` quadratic norm. -/
def splitNorm (x : Split8) : ℂ :=
  x.x0^2 + x.x1^2 + x.x2^2 + x.x3^2 - x.x4^2 - x.x5^2 - x.x6^2 - x.x7^2

/-- Concrete nonzero null vector. -/
def nullVector : Split8 where
  x0 := 1; x1 := 0; x2 := 0; x3 := 0; x4 := 1; x5 := 0; x6 := 0; x7 := 0

/-- The null vector lies on the split null cone. -/
theorem nullVector_norm_zero : splitNorm nullVector = 0 := by
  simp [splitNorm, nullVector]

/-- The null vector is nonzero. -/
theorem nullVector_nonzero : nullVector.x0 ≠ 0 := by
  norm_num [nullVector]

/-! ## Tripotent trifactor operator -/

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev M6C := Matrix (Fin 6) (Fin 6) ℂ

/-- The basic tripotent scale operator with sectors `+1,-1,0`. -/
def Trip : M3C := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- Tripotency of the scale operator. -/
theorem Trip_tripotent : Trip * Trip * Trip = Trip := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Trip, Matrix.mul_apply, Finset.sum]

/-- Scale determinant. -/
theorem Trip_det_scale (s : ℂ) :
    (s • (1 : M3C) - Trip).det = (s - 1) * (s + 1) * s := by
  have hpoly : (s - 1) * (s + 1) * s = s ^ 3 - s := by
    ring
  simp [Trip, Matrix.det_fin_three, Matrix.smul_apply, Matrix.sub_apply, hpoly]

/-- The zero-mode pole of the tripotent. -/
theorem Trip_zero_pole : (0 • (1 : M3C) - Trip).det = 0 := by
  norm_num [Trip, Matrix.det_fin_three, Matrix.smul_apply, Matrix.sub_apply]
  simp

/-- Finite diagonal doubled-sector scale model `T ↦ T⊗I₂`, represented after basis ordering. -/
def TripLift : M6C :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

/-- The finite diagonal doubled-sector model preserves tripotency. -/
theorem TripLift_tripotent : TripLift * TripLift * TripLift = TripLift := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [TripLift, Matrix.mul_apply, Finset.sum]

/-- Explicit lifted sector labels. -/
inductive LiftSector where
  | bosonA | bosonB | fermionA | fermionB | zeroA | zeroB
  deriving DecidableEq, Repr

/-- Eigenvalue attached to each lifted sector. -/
def LiftSector.value : LiftSector → ℂ
  | .bosonA | .bosonB => 1
  | .fermionA | .fermionB => -1
  | .zeroA | .zeroB => 0

/-- All three original sectors are present after one doubled-sector lift. -/
theorem lifted_has_all_trifactors :
    (∃ p : LiftSector, p.value = 1) ∧
    (∃ p : LiftSector, p.value = -1) ∧
    (∃ p : LiftSector, p.value = 0) := by
  constructor
  · use LiftSector.bosonA
    rfl
  · constructor
    · use LiftSector.fermionA
      rfl
    · use LiftSector.zeroA
      rfl

end TripotentCliffordColimit
