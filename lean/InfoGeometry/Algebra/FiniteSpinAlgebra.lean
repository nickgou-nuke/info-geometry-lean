import Mathlib.Tactic

/-!
# Finite spin algebra

Reusable finite spin-`1/2` matrix layer.

This module isolates the two-dimensional `su(2)` ladder relations from the
paper-specific arithmetic owners.  It is a finite matrix algebra surface only:
no global topology, representation classification, or experimental carrier
claim is asserted.
-/

noncomputable section

namespace InfoGeometry.Algebra.FiniteSpin

open Matrix

/-- Complex `2 × 2` matrices. -/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

abbrev Mat3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev Mat3R := Matrix (Fin 3) (Fin 3) ℝ

abbrev QutritMatrix := Mat3C

abbrev Mat4R := Matrix (Fin 4) (Fin 4) ℝ

abbrev Mat4C := Matrix (Fin 4) (Fin 4) ℂ

/-- Canonical larger finite matrix carriers shared by concrete modules. -/
abbrev Mat10R := Matrix (Fin 10) (Fin 10) ℝ
abbrev Mat32Z := Matrix (Fin 32) (Fin 32) ℤ
abbrev Mat10Z := Matrix (Fin 10) (Fin 10) ℤ
abbrev Mat3Z := Matrix (Fin 3) (Fin 3) ℤ
abbrev Mat2Q := Matrix (Fin 2) (Fin 2) ℚ
abbrev Mat8Z := Matrix (Fin 8) (Fin 8) ℤ
abbrev Mat5R := Matrix (Fin 5) (Fin 5) ℝ
abbrev Mat8R := Matrix (Fin 8) (Fin 8) ℝ
abbrev Mat32R := Matrix (Fin 32) (Fin 32) ℝ
abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ
abbrev Mat6C := Matrix (Fin 6) (Fin 6) ℂ
abbrev Mat2x1C := Matrix (Fin 2) (Fin 1) ℂ
abbrev Mat2x1R := Matrix (Fin 2) (Fin 1) ℝ
abbrev Mat16R := Matrix (Fin 16) (Fin 16) ℝ
abbrev Mat32SplitR := Matrix (Fin 2) (Fin 2) Mat16R
abbrev Vec8R := Fin 8 → ℝ
abbrev Vec3R := Fin 3 → ℝ
abbrev Vec4R := Fin 4 → ℝ
abbrev Vec2C := Fin 2 → ℂ
abbrev Vec2R := Fin 2 → ℝ
abbrev Vec2Q := Fin 2 → ℚ
abbrev Vec2Z := Fin 2 → ℤ
abbrev Vec3C := Fin 3 → ℂ
abbrev Vec3Z := Fin 3 → ℤ
abbrev Vec3Q := Fin 3 → ℚ
abbrev Vec4Q := Fin 4 → ℚ
abbrev Vec5Q := Fin 5 → ℚ
abbrev Vec5Z := Fin 5 → ℤ
abbrev Vec4C := Fin 4 → ℂ
abbrev Vec5R := Fin 5 → ℝ
abbrev Vec6C := Fin 6 → ℂ
abbrev Vec6R := Fin 6 → ℝ
abbrev Vec7R := Fin 7 → ℝ
abbrev Vec8C := Fin 8 → ℂ
abbrev Vec10R := Fin 10 → ℝ
abbrev Vec10Q := Fin 10 → ℚ
abbrev Vec10Z := Fin 10 → ℤ
abbrev Vec32R := Fin 32 → ℝ

/-- Matrix commutator. -/
def comm (A B : Mat2C) : Mat2C :=
  A * B - B * A

/-- Spin-half raising matrix. -/
def J_plus : Mat2C :=
  !![0, 1;
     0, 0]

/-- Spin-half lowering matrix. -/
def J_minus : Mat2C :=
  !![0, 0;
     1, 0]

/-- Spin-half diagonal generator. -/
def J_zero : Mat2C :=
  !![(1 / 2 : ℂ), 0;
     0, -(1 / 2 : ℂ)]

/-- Structure exposing a finite spin-`1/2` algebra carrier. -/
structure SpinHalfBasis (n : ℕ) where
  J_zero : Matrix (Fin n) (Fin n) ℂ
  J_plus : Matrix (Fin n) (Fin n) ℂ
  J_minus : Matrix (Fin n) (Fin n) ℂ
  h_commutator_z_plus : J_zero * J_plus - J_plus * J_zero = J_plus
  h_commutator_z_minus : J_zero * J_minus - J_minus * J_zero = -J_minus
  h_commutator_plus_minus : J_plus * J_minus - J_minus * J_plus = (2 : ℂ) • J_zero

namespace SpinHalfBasis

variable {n : ℕ} (basis : SpinHalfBasis n)

/-- The `J₀,J₊` commutation relation read from a finite spin-half basis. -/
theorem spin_z_plus_commutation :
    basis.J_zero * basis.J_plus - basis.J_plus * basis.J_zero = basis.J_plus :=
  basis.h_commutator_z_plus

/-- The `J₀,J₋` commutation relation read from a finite spin-half basis. -/
theorem spin_z_minus_commutation :
    basis.J_zero * basis.J_minus - basis.J_minus * basis.J_zero = -basis.J_minus :=
  basis.h_commutator_z_minus

/-- The `J₊,J₋` commutation relation read from a finite spin-half basis. -/
theorem spin_plus_minus_commutation :
    basis.J_plus * basis.J_minus - basis.J_minus * basis.J_plus = (2 : ℂ) • basis.J_zero :=
  basis.h_commutator_plus_minus

end SpinHalfBasis

/-- Concrete finite relation `[J₀,J₊]=J₊`. -/
theorem comm_J_zero_J_plus :
    comm J_zero J_plus = J_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, J_zero, J_plus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete finite relation `[J₀,J₋]=-J₋`. -/
theorem comm_J_zero_J_minus :
    comm J_zero J_minus = -J_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, J_zero, J_minus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete finite relation `[J₊,J₋]=2J₀`. -/
theorem comm_J_plus_J_minus :
    comm J_plus J_minus = (2 : ℂ) • J_zero := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, J_plus, J_minus, J_zero, Matrix.mul_apply, Fin.sum_univ_two]

/-- The canonical concrete spin-half basis. -/
def canonicalSpinHalfBasis : SpinHalfBasis 2 where
  J_zero := J_zero
  J_plus := J_plus
  J_minus := J_minus
  h_commutator_z_plus := comm_J_zero_J_plus
  h_commutator_z_minus := comm_J_zero_J_minus
  h_commutator_plus_minus := comm_J_plus_J_minus

/-- Consolidated finite spin algebra packet. -/
theorem finite_spin_half_packet :
    comm J_zero J_plus = J_plus ∧
      comm J_zero J_minus = -J_minus ∧
        comm J_plus J_minus = (2 : ℂ) • J_zero :=
  ⟨comm_J_zero_J_plus, comm_J_zero_J_minus, comm_J_plus_J_minus⟩

end InfoGeometry.Algebra.FiniteSpin

end noncomputable section
