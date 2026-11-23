/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Class-two BCH multiplication in the noncommutative `3 × 3` operator ring

The carrier is `Matrix (Fin 3) (Fin 3) A` for an arbitrary, possibly
noncommutative ring `A`. The half element is explicit: it is exactly the
coefficient required by the quadratic exponential and BCH law.
-/

namespace InfoGeometry.OperatorAlgebra.StrictUpperTriangularBCH

open Matrix

variable {A : Type*} [Ring A]

abbrev Op₃ (A : Type*) := Matrix (Fin 3) (Fin 3) A

/-- A strictly upper-triangular operator, with its three independent entries. -/
def strictUpper (a b c : A) : Op₃ A := !![0, a, b; 0, 0, c; 0, 0, 0]

/-- The corresponding unitriangular operator. -/
def unipotent (a b c : A) : Op₃ A := !![1, a, b; 0, 1, c; 0, 0, 1]

/-- Multiplication in the strict upper-triangular `3 × 3` operator algebra. -/
theorem strictUpper_mul (a b c d e f : A) :
    strictUpper a b c * strictUpper d e f = strictUpper 0 (a * f) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [strictUpper]

/-- The associative commutator on the operator carrier. -/
def opComm (X Y : Op₃ A) : Op₃ A := X * Y - Y * X

/-- The Lie bracket of two strict upper operators is supported only in the
top-right matrix entry. The order `a*f - d*c` is retained. -/
theorem strictUpper_comm (a b c d e f : A) :
    opComm (strictUpper a b c) (strictUpper d e f) =
      strictUpper 0 (a * f - d * c) 0 := by
  rw [opComm, strictUpper_mul, strictUpper_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [strictUpper]

/-- The operator matrix algebra is genuinely noncommutative whenever its
coefficient ring is nontrivial: the adjacent upper-root operators have
different two-step products. This witness does not require `A` itself to be
noncommutative. -/
theorem strictUpper_adjacent_roots_do_not_commute [Nontrivial A] :
    strictUpper (1 : A) 0 0 * strictUpper 0 0 (1 : A) ≠
      strictUpper 0 0 (1 : A) * strictUpper (1 : A) 0 0 := by
  intro h
  have h02 := congrArg (fun M : Op₃ A => M 0 2) h
  rw [strictUpper_mul, strictUpper_mul] at h02
  simp [strictUpper] at h02

/-- Matrix units in the coefficient operator algebra `M₂(ℝ)`. -/
abbrev RealOp₂ := Matrix (Fin 2) (Fin 2) ℝ

private def coeffE01 : RealOp₂ := !![(0 : ℝ), 1; 0, 0]
private def coeffE10 : RealOp₂ := !![(0 : ℝ), 0; 1, 0]

/-- The coefficient ring `M₂(ℝ)` retains its noncommutative ordered product:
the two opposite matrix-unit products are different. -/
theorem operatorCoefficient_matrix_units_do_not_commute :
    coeffE01 * coeffE10 ≠ coeffE10 * coeffE01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [coeffE01, coeffE10, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The class-two Lie bracket in `M₃(M₂(ℝ))` contains a nonzero product of
noncommuting operator coefficients. This witnesses both the outer BCH
commutator and the internal operator order in one matrix carrier. -/
theorem strictUpper_operator_coefficient_commutator_nonzero :
    opComm (A := RealOp₂)
      (strictUpper coeffE01 (0 : RealOp₂) (0 : RealOp₂))
      (strictUpper (0 : RealOp₂) (0 : RealOp₂) coeffE10) ≠
        (0 : Op₃ RealOp₂) := by
  intro h
  have h02 := congrArg (fun M : Op₃ (Matrix (Fin 2) (Fin 2) ℝ) => M 0 2) h
  have h00 := congrArg (fun M : RealOp₂ => M 0 0) h02
  norm_num [opComm, strictUpper, coeffE01, coeffE10, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_succ] at h00

/-- Every strict upper operator commutes with every bracket: this matrix
algebra is two-step nilpotent as a Lie algebra. -/
theorem strictUpper_bracket_central (a b c d e f g k l : A) :
    opComm (opComm (strictUpper a b c) (strictUpper d e f))
        (strictUpper g k l) = 0 ∧
    opComm (strictUpper g k l)
        (opComm (strictUpper a b c) (strictUpper d e f)) = 0 := by
  rw [strictUpper_comm]
  constructor <;> rw [opComm, strictUpper_mul, strictUpper_mul]
    <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [strictUpper]

/-- Multiplication of unitriangular operators; the cross term records the
noncommutative order along the two-step path. -/
theorem unipotent_mul (a b c d e f : A) :
    unipotent a b c * unipotent d e f =
      unipotent (a + d) (b + e + a * f) (c + f) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotent] <;> abel

/-- Explicit inverse in the unitriangular operator group. -/
theorem unipotent_mul_inverse (a b c : A) :
    unipotent a b c * unipotent (-a) (a * c - b) (-c) = 1 := by
  rw [unipotent_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent]

/-- The inverse is two-sided, including over noncommutative coefficient rings. -/
theorem inverse_mul_unipotent (a b c : A) :
    unipotent (-a) (a * c - b) (-c) * unipotent a b c = 1 := by
  rw [unipotent_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent]

/-- The coordinate unipotent operator, equipped with its explicit inverse,
as an element of the general linear group of the operator module. -/
def unipotentUnit (a b c : A) : Units (Op₃ A) where
  val := unipotent a b c
  inv := unipotent (-a) (a * c - b) (-c)
  val_inv := unipotent_mul_inverse a b c
  inv_val := inverse_mul_unipotent a b c

/-- Intrinsic entry conditions for a unitriangular operator on three stages:
unit diagonal and zero strictly below it. Unlike a coordinate-range
definition, this predicate describes matrices by their operator entries. -/
def IsUnitriangular (M : Op₃ A) : Prop :=
  M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1 ∧
    M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

/-- The six intrinsic entry conditions determine the three free upper-root
operators uniquely, retaining their order as matrix entries. -/
theorem eq_unipotent_of_isUnitriangular {M : Op₃ A}
    (hM : IsUnitriangular M) :
    M = unipotent (M 0 1) (M 0 2) (M 1 2) := by
  rcases hM with ⟨h00, h11, h22, h10, h20, h21⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotent, h00, h11, h22, h10, h20, h21]

/-- Multiplication in the concrete subgroup is exactly the class-two
unitriangular coordinate law, with the ordered cross-term `a*f`. -/
theorem unipotentUnit_mul (a b c d e f : A) :
    unipotentUnit a b c * unipotentUnit d e f =
      unipotentUnit (a + d) (b + e + a * f) (c + f) := by
  apply Units.ext
  exact unipotent_mul a b c d e f

/-- The inverse in the concrete operator group is given by the noncommutative
coordinate correction `a*c - b`. -/
theorem unipotentUnit_inv (a b c : A) :
    (unipotentUnit a b c)⁻¹ = unipotentUnit (-a) (a * c - b) (-c) := by
  apply Units.ext
  rfl

/-- The unitriangular operators form the intrinsic subgroup of `GL₃(A)`
whose matrices have unit diagonal and vanish below the diagonal. This group
is defined by matrix geometry, not as the range of its coordinate chart. -/
def unitriangularOperatorGroup : Subgroup (Units (Op₃ A)) where
  carrier := {U | IsUnitriangular (U : Op₃ A)}
  one_mem' := by simp [IsUnitriangular]
  mul_mem' := by
    intro U V hU hV
    change IsUnitriangular ((U * V : Units (Op₃ A)) : Op₃ A)
    rw [Units.val_mul, eq_unipotent_of_isUnitriangular hU,
      eq_unipotent_of_isUnitriangular hV, unipotent_mul]
    simp [IsUnitriangular, unipotent]
  inv_mem' := by
    intro U hU
    have hshape := eq_unipotent_of_isUnitriangular hU
    have hcoord : U = unipotentUnit (U.1 0 1) (U.1 0 2) (U.1 1 2) := by
      apply Units.ext
      exact hshape
    rw [hcoord, unipotentUnit_inv]
    simp [IsUnitriangular, unipotentUnit, unipotent]


/-- The matrix group commutator of two unitriangular operators lies in the
central top-right root subgroup, with coordinate `a*f - d*c`. -/
theorem unipotent_group_commutator (a b c d e f : A) :
    unipotent a b c * unipotent d e f *
        unipotent (-a) (a * c - b) (-c) *
        unipotent (-d) (d * f - e) (-f) =
      unipotent 0 (a * f - d * c) 0 := by
  rw [unipotent_mul, unipotent_mul, unipotent_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> all_goals simp [unipotent] <;> noncomm_ring

/- The following identity is the operator-level version of the class-two
   group commutator formula. The half element affects the exponential chart,
   while the commutator itself is independent of that chart. -/

/-- A half element supplies the coefficient needed for the quadratic
truncation without assuming that the coefficient ring is commutative. -/
def hasHalf (h : A) : Prop := h + h = 1

/-- The exact quadratic exponential on strict upper-triangular `3 × 3`
operators, written as a unitriangular matrix. -/
def exp₂ (h a b c : A) : Op₃ A :=
  unipotent a (b + h * (a * c)) c

/-- The quadratic-exponential chart reaches every unitriangular operator.
The inverse coordinate change is the noncommutative shear
`(a,b,c) ↦ (a, b - h*(a*c), c)`. -/
theorem exp₂_reconstructs_unipotent (h a b c : A) :
    exp₂ h a (b - h * (a * c)) c = unipotent a b c := by
  dsimp [exp₂]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent]

/-- Every invertible unitriangular operator has coordinates in the quadratic
exponential chart, for every coefficient `h`. Thus the chart is surjective
onto the concrete operator subgroup, not merely an injective parametrization. -/
theorem unitriangular_exp₂_chart_surjective (h : A)
    (U : unitriangularOperatorGroup) :
    ∃ a b c : A, ((U.1 : Units (Op₃ A)) : Op₃ A) = exp₂ h a b c := by
  let a := (U.1 : Op₃ A) 0 1
  let b := (U.1 : Op₃ A) 0 2
  let c := (U.1 : Op₃ A) 1 2
  refine ⟨a, b - h * (a * c), c, ?_⟩
  rw [eq_unipotent_of_isUnitriangular U.2]
  exact (exp₂_reconstructs_unipotent h a b c).symm

/-- The quadratic-exponential chart has unique coordinates over an arbitrary
noncommutative ring. -/
theorem exp₂_injective (h a b c d e f : A)
    (heq : exp₂ h a b c = exp₂ h d e f) :
    a = d ∧ b = e ∧ c = f := by
  have hab := congrArg (fun M : Op₃ A => M 0 1) heq
  have hbc := congrArg (fun M : Op₃ A => M 0 2) heq
  have hcf := congrArg (fun M : Op₃ A => M 1 2) heq
  have ha : a = d := by simpa [exp₂, unipotent] using hab
  have hc : c = f := by simpa [exp₂, unipotent] using hcf
  have hb' : b + h * (a * c) = e + h * (a * c) := by
    simpa [exp₂, unipotent, ha, hc] using hbc
  exact ⟨ha, add_right_cancel hb', hc⟩

/-- The coordinate chart is exactly the quadratic matrix polynomial
`1 + N + h • N²` for the strict upper operator `N`; the coefficient acts on
the left, so no centrality of `h` or commutativity of `A` is assumed. -/
theorem exp₂_eq_quadratic_polynomial (h a b c : A) :
    exp₂ h a b c =
      1 + strictUpper a b c + h • (strictUpper a b c * strictUpper a b c) := by
  rw [strictUpper_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exp₂, unipotent, strictUpper, Matrix.add_apply]

/-- The class-two BCH coordinates `X + Y + h[X,Y]`. -/
def bch₂ (h a b c d e f : A) : A × A × A :=
  (a + d, b + e + h * (a * f - d * c), c + f)

/-- The class-two BCH product on the three operator entries. -/
def bch₂Mul (h : A) (x y : A × A × A) : A × A × A :=
  bch₂ h x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2

/-- For a quadratic-exponential chart, the group commutator is the
exponential of the Lie commutator. This is an exact identity in `M₃(A)`, not
an asymptotic BCH statement. -/
theorem exp₂_group_commutator (h a b c d e f : A)
    (hh : hasHalf h) :
    exp₂ h a b c * exp₂ h d e f *
        exp₂ h (-a) (-b) (-c) * exp₂ h (-d) (-e) (-f) =
      unipotent 0 (a * f - d * c) 0 := by
  change h + h = 1 at hh
  have hA : a * c - (b + h * (a * c)) = -b + h * (a * c) := by
    calc
      a * c - (b + h * (a * c)) = (h + h) * (a * c) - (b + h * (a * c)) := by
        rw [hh, one_mul]
      _ = -b + h * (a * c) := by noncomm_ring
  have hD : d * f - (e + h * (d * f)) = -e + h * (d * f) := by
    calc
      d * f - (e + h * (d * f)) = (h + h) * (d * f) - (e + h * (d * f)) := by
        rw [hh, one_mul]
      _ = -e + h * (d * f) := by noncomm_ring
  dsimp [exp₂]
  have hnegA : h * (-a * -c) = h * (a * c) := by noncomm_ring
  have hnegD : h * (-d * -f) = h * (d * f) := by noncomm_ring
  rw [hnegA, hnegD]
  rw [← hA, ← hD, unipotent_group_commutator]

/-- Exact quadratic-exponential BCH multiplication in the noncommutative
operator matrix ring `M₃(A)`. The hypothesis supplies a half element, which
is necessary for the coefficient `1/2`; no commutativity of `A` is assumed. -/
theorem exp₂_mul_exp₂_eq_exp₂_bch
    (h a b c d e f : A)
    (hh : hasHalf h) :
    exp₂ h a b c * exp₂ h d e f =
      exp₂ h (bch₂ h a b c d e f).1
        (bch₂ h a b c d e f).2.1
        (bch₂ h a b c d e f).2.2 := by
  change h + h = 1 at hh
  have hmul (x : A) : 2 • (h * x) = x := by
    calc
      2 • (h * x) = h * x + h * x := by rw [two_smul]
      _ = (h + h) * x := by rw [← add_mul]
      _ = x := by rw [hh, one_mul]
  dsimp [exp₂, bch₂]
  rw [unipotent_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotent]
  all_goals
    calc
      _ = b + (h * (a * c) + (e + (h * (d * f) + a * f))) := by abel
      _ = b + (h * (a * c) + (e + (h * (d * f) + 2 • (h * (a * f))))) := by
        rw [hmul]
      _ = _ := by noncomm_ring [hh]

/-- Associativity of the coordinate BCH law, derived from associativity of
operator-matrix multiplication and injectivity of the quadratic chart. The
statement retains the noncommutative coefficient order used by `bch₂`. -/
theorem bch₂Mul_assoc (h : A) (hh : hasHalf h)
    (x y z : A × A × A) :
    bch₂Mul h (bch₂Mul h x y) z = bch₂Mul h x (bch₂Mul h y z) := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  obtain ⟨g, k, l⟩ := z
  have hleft := exp₂_mul_exp₂_eq_exp₂_bch h a b c d e f hh
  have hright := exp₂_mul_exp₂_eq_exp₂_bch h d e f g k l hh
  have hleft' := exp₂_mul_exp₂_eq_exp₂_bch h
    (bch₂ h a b c d e f).1 (bch₂ h a b c d e f).2.1
    (bch₂ h a b c d e f).2.2 g k l hh
  have hright' := exp₂_mul_exp₂_eq_exp₂_bch h a b c
    (bch₂ h d e f g k l).1 (bch₂ h d e f g k l).2.1
    (bch₂ h d e f g k l).2.2 hh
  have hmat :
      exp₂ h (bch₂ h (bch₂ h a b c d e f).1 (bch₂ h a b c d e f).2.1
        (bch₂ h a b c d e f).2.2 g k l).1
        (bch₂ h (bch₂ h a b c d e f).1 (bch₂ h a b c d e f).2.1
          (bch₂ h a b c d e f).2.2 g k l).2.1
        (bch₂ h (bch₂ h a b c d e f).1 (bch₂ h a b c d e f).2.1
          (bch₂ h a b c d e f).2.2 g k l).2.2 =
      exp₂ h (bch₂ h a b c (bch₂ h d e f g k l).1
        (bch₂ h d e f g k l).2.1 (bch₂ h d e f g k l).2.2).1
        (bch₂ h a b c (bch₂ h d e f g k l).1
          (bch₂ h d e f g k l).2.1 (bch₂ h d e f g k l).2.2).2.1
        (bch₂ h a b c (bch₂ h d e f g k l).1
          (bch₂ h d e f g k l).2.1 (bch₂ h d e f g k l).2.2).2.2 := by
    calc
      _ = exp₂ h (bch₂ h a b c d e f).1 (bch₂ h a b c d e f).2.1
          (bch₂ h a b c d e f).2.2 * exp₂ h g k l := hleft'.symm
      _ = (exp₂ h a b c * exp₂ h d e f) * exp₂ h g k l := by rw [hleft]
      _ = exp₂ h a b c * (exp₂ h d e f * exp₂ h g k l) := mul_assoc _ _ _
      _ = exp₂ h a b c * exp₂ h (bch₂ h d e f g k l).1
          (bch₂ h d e f g k l).2.1 (bch₂ h d e f g k l).2.2 := by rw [hright]
      _ = _ := hright'
  obtain ⟨h₁, h₂, h₃⟩ := exp₂_injective h _ _ _ _ _ _ hmat
  apply Prod.ext h₁
  apply Prod.ext h₂
  exact h₃

/-- The quadratic exponential of a strict upper operator multiplies by the
quadratic exponential of its negative to the identity. -/
theorem exp₂_mul_exp₂_neg_eq_one (h a b c : A) (hh : hasHalf h) :
    exp₂ h a b c * exp₂ h (-a) (-b) (-c) = 1 := by
  change h + h = 1 at hh
  dsimp [exp₂]
  rw [unipotent_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotent]
  all_goals
    calc
      _ = h * (a * c) + h * (a * c) - (a * c) := by abel
      _ = 0 := by rw [← add_mul, hh, one_mul, sub_self]

/-- The reverse product gives the same inverse identity, without commuting
any coefficients of the noncommutative ring. -/
theorem exp₂_neg_mul_exp₂_eq_one (h a b c : A) (hh : hasHalf h) :
    exp₂ h (-a) (-b) (-c) * exp₂ h a b c = 1 := by
  change h + h = 1 at hh
  dsimp [exp₂]
  rw [unipotent_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotent]
  all_goals
    calc
      _ = h * (a * c) + h * (a * c) - (a * c) := by abel
      _ = 0 := by rw [← add_mul, hh, one_mul, sub_self]

/-- The strict upper corner is two-step nilpotent: every product of three
strictly upper-triangular `3 × 3` operators vanishes. -/
theorem strictUpper_cube_eq_zero (a b c : A) :
    strictUpper a b c * strictUpper a b c * strictUpper a b c = 0 := by
  rw [strictUpper_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [strictUpper]

/-- Matrix multiplication in `Op₃ A` is genuinely noncommutative over any
nontrivial coefficient ring. -/
theorem op3_noncommute [Nontrivial A] :
    ∃ matI matJ : Matrix (Fin 3) (Fin 3) A,
      matI * matJ ≠ matJ * matI := by
  refine ⟨strictUpper 1 0 0, strictUpper 0 0 1, ?_⟩
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 0 2) h
  simp [strictUpper, Matrix.mul_apply, Fin.sum_univ_three] at h02

end InfoGeometry.OperatorAlgebra.StrictUpperTriangularBCH
