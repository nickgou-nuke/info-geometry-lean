/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Projective.Clifford22MatrixCore
import Mathlib.Data.Matrix.Basic

open Matrix
def _witness_a_22_ℤ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 0 1 1
def _witness_b_22_ℤ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 1 0 1

theorem _witness_noncommute_22_ℤ : _witness_a_22_ℤ * _witness_b_22_ℤ ≠ _witness_b_22_ℤ * _witness_a_22_ℤ := by
  intro h
  have h₁ : _witness_a_22_ℤ * _witness_b_22_ℤ = Matrix.single 0 0 (1 : ℤ) := by
    simp [_witness_a_22_ℤ, _witness_b_22_ℤ, Matrix.single_mul_single_same]
  have h₂ : _witness_b_22_ℤ * _witness_a_22_ℤ = Matrix.single 1 1 (1 : ℤ) := by
    simp [_witness_a_22_ℤ, _witness_b_22_ℤ, Matrix.single_mul_single_same]
  rw [h₁, h₂] at h
  have h₃ := congrFun (congrFun h 0) 0
  norm_num at h₃

def _witness_a : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single 0 1 1
def _witness_b : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single 1 0 1

theorem _witness_noncommute : _witness_a * _witness_b ≠ _witness_b * _witness_a := by
  intro h
  have h₁ : _witness_a * _witness_b = Matrix.single 0 0 (1 : ℝ) := by
    simp [_witness_a, _witness_b, Matrix.single_mul_single_same]
  have h₂ : _witness_b * _witness_a = Matrix.single 1 1 (1 : ℝ) := by
    simp [_witness_a, _witness_b, Matrix.single_mul_single_same]
  rw [h₁, h₂] at h
  have h₃ := congrFun (congrFun h 0) 0
  norm_num at h₃

/-!
# Chiral spinor brackets and the positive `Gr(2,4)` chart in the `Cl(2,2)` matrix frame

Additions on top of `Clifford22MatrixCore` (same displayed `4 × 4` frame,
`ω = diag(1,1,-1,-1)`), each SymPy-checked before translation:

* `clReconstruct4_eq`: the sixteen signed trace coordinates reconstruct `4 • M`.
* Doubled chiral projectors: `(1 ± ω)² = 2 (1 ± ω)`, `(1 + ω)(1 - ω) = 0`.
* `chiral_bivector_sq`: `((1 ± ω) B)² = 2 (I₁ ± 2 Q_Pl) (1 ± ω)`.  (A candidate
  statement `((1+ω)B)² = 2 I₊ ((1+ω)B)` is false; the right-hand projector is
  `1 + ω`, not `(1+ω)B`.)
* `ymSlashMomentum_anticomm`: `P_a P_b + P_b P_a = -4 ⟨ab⟩[ab] · 1`.
* Chiral commutator vanishing: if `λ̃_b = c λ̃_a` then `(1 + ω)[P_a,P_b] = 0`; if
  `λ_b = c λ_a` then `(1 - ω)[P_a,P_b] = 0`.
* Affine chart around a projector: for idempotents `P, Q` with `PQ = QP = 0` and
  `N = P X Q`, `N² = 0`, `(1 - N) P (1 + N) = P + N`, `(1 + N) P (1 - N) = P - N`.
* Positive `Gr(2,4)` chart `C(α) = [I₂ | G(α)]`: the six minors are
  `1, α₃+α₄, α₂α₄, α₁, α₁α₂, α₁α₂α₃`, they satisfy the Plücker relation, are
  positive for positive `α`, the explicit Jacobian of
  `g = (-α₁, -α₁α₂, α₃+α₄, α₂α₄)` has determinant `α₁α₂`, and
  `(12)(23)(34)(14) = α₁α₂ · α₁α₂α₃α₄`.

## Scope

The Jacobian matrix is written explicitly (its entries are the partial derivatives
of the displayed polynomial map); no differential-form library statement is made.
Matrix-rank stratification (ranks `4,3,2,1`) and the MHV / anti-MHV vertex readings
are not proved here.
-/

namespace Clifford22

namespace Mat4

open Matrix

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 8000000 in
/-- The sixteen signed trace coordinates reconstruct `4 • M`. -/
theorem clReconstruct4_eq (M : Mat4 R) : clReconstruct4 M = smul 4 M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clReconstruct4, tr4, smul, E1, E2, E3, E4, E12, E13, E14, E23, E24, E34,
      E234, E134, E124, E123, omega, Matrix.mul_apply, Fin.sum_univ_four] <;> noncomm_ring

/-- The displayed volume element is diagonal in the chosen chiral frame. -/
theorem omega_eq : (omega : Mat4 R) = Matrix.diagonal ![1, 1, -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega, E1, E2, E3, E4, Matrix.mul_apply, Fin.sum_univ_four]

/-- The doubled positive chiral projector squares to twice itself. -/
theorem Pi_plus_2_sq : (Pi_plus_2 : Mat4 R) * Pi_plus_2 = smul 2 Pi_plus_2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_plus_2, omega_eq, smul, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal] <;>
    norm_num

/-- The doubled negative chiral projector squares to twice itself. -/
theorem Pi_minus_2_sq : (Pi_minus_2 : Mat4 R) * Pi_minus_2 = smul 2 Pi_minus_2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_minus_2, omega_eq, smul, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal] <;>
    norm_num

/-- The two doubled chiral projectors are orthogonal. -/
theorem Pi_plus_2_mul_Pi_minus_2 : (Pi_plus_2 : Mat4 R) * Pi_minus_2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_plus_2, Pi_minus_2, omega_eq, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal]

set_option maxHeartbeats 8000000 in
/-- Chiral squares of a bivector: `((1 ± ω) B)² = 2 (I₁ ± 2 Q_Pl) (1 ± ω)`. -/
theorem chiral_bivector_sq (p12 p13 p14 p23 p24 p34 : R) :
    (Pi_plus_2 * clBivec p12 p13 p14 p23 p24 p34) * (Pi_plus_2 * clBivec p12 p13 p14 p23 p24 p34) =
        smul (2 * (bivecNormI1 p12 p13 p14 p23 p24 p34 + 2 * plueckerRel p12 p13 p14 p23 p24 p34))
          Pi_plus_2 ∧
      (Pi_minus_2 * clBivec p12 p13 p14 p23 p24 p34) *
          (Pi_minus_2 * clBivec p12 p13 p14 p23 p24 p34) =
        smul (2 * (bivecNormI1 p12 p13 p14 p23 p24 p34 - 2 * plueckerRel p12 p13 p14 p23 p24 p34))
          Pi_minus_2 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Pi_plus_2, Pi_minus_2, omega_eq, clBivec, smul, E12, E13, E14, E23, E24, E34,
      E1, E2, E3, E4, bivecNormI1, plueckerRel, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.diagonal] <;> ring

set_option maxHeartbeats 8000000 in
/-- `P_a P_b + P_b P_a = -4 ⟨ab⟩[ab] · 1`. -/
theorem ymSlashMomentum_anticomm (la ta lb tb : Spinor2 R) :
    ymSlashMomentum la ta * ymSlashMomentum lb tb + ymSlashMomentum lb tb * ymSlashMomentum la ta =
      smul (-4 * spinBrk la lb * spinBrk ta tb) 1 := by
  have hla := (ymSlashMomentum_null_and_chiral_minor_zero la ta).1
  have hlb := (ymSlashMomentum_null_and_chiral_minor_zero lb tb).1
  calc
    ymSlashMomentum la ta * ymSlashMomentum lb tb +
        ymSlashMomentum lb tb * ymSlashMomentum la ta =
        (ymSlashMomentum la ta + ymSlashMomentum lb tb) *
          (ymSlashMomentum la ta + ymSlashMomentum lb tb) := by
      simp only [add_mul, mul_add]
      rw [hla, hlb]
      abel
    _ = smul (-4 * spinBrk la lb * spinBrk ta tb) 1 :=
      ymSlashMomentum_pair_square la ta lb tb

set_option maxHeartbeats 8000000 in
/-- Collinear square spinors kill the self-dual part of the commutator; collinear angle
spinors kill the anti-self-dual part. -/
theorem ymSlashMomentum_chiral_commutator (la ta lb tb : Spinor2 R) (c : R) :
    Pi_plus_2 * (ymSlashMomentum la ta * ymSlashMomentum lb ⟨c * ta.s1, c * ta.s2⟩ -
        ymSlashMomentum lb ⟨c * ta.s1, c * ta.s2⟩ * ymSlashMomentum la ta) = 0 ∧
      Pi_minus_2 * (ymSlashMomentum la ta * ymSlashMomentum ⟨c * la.s1, c * la.s2⟩ tb -
        ymSlashMomentum ⟨c * la.s1, c * la.s2⟩ tb * ymSlashMomentum la ta) = 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Pi_plus_2, Pi_minus_2, omega_eq, ymSlashMomentum, clVec, smul, E1, E2, E3, E4,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal] <;> ring

end Mat4

/-! ### Affine chart around an idempotent -/

section Chart

variable {A : Type*} [Ring A] {P Q : A}

/-- For idempotents with `PQ = QP = 0` and `N = P X Q`: `N² = 0` and the two
conjugation orders give `P ± N`. -/
theorem projector_chart (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (X : A) :
    (P * X * Q) * (P * X * Q) = 0 ∧
      (1 - P * X * Q) * P * (1 + P * X * Q) = P + P * X * Q ∧
      (1 + P * X * Q) * P * (1 - P * X * Q) = P - P * X * Q := by
  have hP' : ∀ z : A, P * (P * z) = P * z := fun z => by rw [← mul_assoc, hP]
  have hQP' : ∀ z : A, Q * (P * z) = 0 := fun z => by rw [← mul_assoc, hQP, zero_mul]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP, hQP,
      hP', hQP', mul_zero, zero_mul, sub_zero, add_zero] <;>
    abel

end Chart

/-! ### Positive `Gr(2,4)` chart -/

section PositiveGr24

variable {R : Type*} [Ring R]

/-- `C(α) = [[1, 0, -α₁, -α₁α₂], [0, 1, α₃+α₄, α₂α₄]]`. -/
def postnikovC (a₁ a₂ a₃ a₄ : R) : Matrix (Fin 2) (Fin 4) R :=
  !![1, 0, -a₁, -(a₁ * a₂); 0, 1, a₃ + a₄, a₂ * a₄]

/-- The Plücker minor on columns `i, j`. -/
def minor24 (C : Matrix (Fin 2) (Fin 4) R) (i j : Fin 4) : R :=
  C 0 i * C 1 j - C 0 j * C 1 i

/-- Compute all six ordered Plücker coordinates of the Postnikov chart. -/
theorem postnikov_minors (a₁ a₂ a₃ a₄ : R) :
    let C := postnikovC a₁ a₂ a₃ a₄
    minor24 C 0 1 = 1 ∧ minor24 C 0 2 = a₃ + a₄ ∧ minor24 C 0 3 = a₂ * a₄ ∧
      minor24 C 1 2 = a₁ ∧ minor24 C 1 3 = a₁ * a₂ ∧ minor24 C 2 3 = a₁ * a₂ * a₃ := by
  intro C
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [C, minor24, postnikovC, Matrix.det_fin_two] <;> noncomm_ring

/-- Ordered operator-valued minors of the Postnikov chart have this exact
Plücker defect over an arbitrary, possibly noncommutative ring. -/
def postnikovPluckerDefect (a₁ a₂ a₃ a₄ : R) : R :=
  a₁ * a₂ * a₃ - (a₃ + a₄) * (a₁ * a₂) + (a₂ * a₄) * a₁

theorem postnikov_plucker_defect (a₁ a₂ a₃ a₄ : R) :
    let C := postnikovC a₁ a₂ a₃ a₄
    minor24 C 0 1 * minor24 C 2 3 - minor24 C 0 2 * minor24 C 1 3 +
      minor24 C 0 3 * minor24 C 1 2 = postnikovPluckerDefect a₁ a₂ a₃ a₄ := by
  intro C
  simp [C, minor24, postnikovC, postnikovPluckerDefect]
  noncomm_ring

/-- Concrete operator-valued counterexample: for the matrix units `E₀₁` and
`E₁₀`, the ordered Plücker defect is `diag(1,-1)`, not zero. -/
theorem postnikov_plucker_operator_counterexample :
    postnikovPluckerDefect
      (R := Matrix (Fin 2) (Fin 2) ℤ)
      (Matrix.of ![![0, 1], ![0, 0]]) 1
      (Matrix.of ![![0, 0], ![1, 0]]) 0 = Matrix.of ![![1, 0], ![0, -1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [postnikovPluckerDefect, Matrix.mul_apply, Fin.sum_univ_two]

theorem postnikov_plucker_operator_counterexample_ne_zero :
    postnikovPluckerDefect
      (R := Matrix (Fin 2) (Fin 2) ℤ)
      (Matrix.of ![![0, 1], ![0, 0]]) 1
      (Matrix.of ![![0, 0], ![1, 0]]) 0 ≠ 0 := by
  rw [postnikov_plucker_operator_counterexample]
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  norm_num at h00

end PositiveGr24

/-! Positivity and Jacobian claims below concern scalar coordinates.  Their
ordered-field hypotheses supply the commutativity needed for the usual
Grassmannian determinant identities. -/

section PositiveGr24Scalar

variable {R : Type*} [CommRing R]

/-- Positive bridge parameters give strict positivity of every ordered scalar minor. -/
theorem postnikov_minors_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a₁ a₂ a₃ a₄ : K} (h₁ : 0 < a₁) (h₂ : 0 < a₂) (h₃ : 0 < a₃) (h₄ : 0 < a₄) :
    let C := postnikovC a₁ a₂ a₃ a₄
    0 < minor24 C 0 1 ∧ 0 < minor24 C 0 2 ∧ 0 < minor24 C 0 3 ∧
      0 < minor24 C 1 2 ∧ 0 < minor24 C 1 3 ∧ 0 < minor24 C 2 3 := by
  intro C
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := postnikov_minors a₁ a₂ a₃ a₄
  simp only [C, e1, e2, e3, e4, e5, e6]
  exact ⟨one_pos, add_pos h₃ h₄, mul_pos h₂ h₄, h₁, mul_pos h₁ h₂,
    mul_pos (mul_pos h₁ h₂) h₃⟩

/-- Jacobian of `g = (-α₁, -α₁α₂, α₃+α₄, α₂α₄)` with respect to `(α₁, α₂, α₃, α₄)`. -/
def postnikovJac (a₁ a₂ a₄ : R) : Matrix (Fin 4) (Fin 4) R :=
  !![-1, 0, 0, 0;
     -a₂, -a₁, 0, 0;
     0, 0, 1, 1;
     0, a₄, 0, a₂]

/-- The Jacobian determinant of the Postnikov coordinate map is `α₁ α₂`. -/
theorem postnikovJac_det (a₁ a₂ a₄ : R) : (postnikovJac a₁ a₂ a₄).det = a₁ * a₂ := by
  simp [postnikovJac, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

/-- `d log` cancellation: the cyclic Parke–Taylor denominator equals the Jacobian
determinant times `α₁α₂α₃α₄`. -/
theorem postnikov_dlog_denominator (a₁ a₂ a₃ a₄ : R) :
    let C := postnikovC a₁ a₂ a₃ a₄
    minor24 C 0 1 * minor24 C 1 2 * minor24 C 2 3 * minor24 C 0 3 =
      (postnikovJac a₁ a₂ a₄).det * (a₁ * a₂ * a₃ * a₄) := by
  intro C
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := postnikov_minors a₁ a₂ a₃ a₄
  simp only [C, e1, e4, e6, e3, postnikovJac_det]
  ring

/-- On the positive chart, the Jacobian divided by the cyclic Parke--Taylor
denominator is exactly the coefficient `1/(α₁α₂α₃α₄)` of the logarithmic
volume element. This is a scalar density identity; it does not claim to build
an exterior differential form or a global canonical form on the Grassmannian. -/
theorem postnikov_dlog_density_coefficient
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a₁ a₂ a₃ a₄ : K}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) (h₃ : 0 < a₃) (h₄ : 0 < a₄) :
    let C := postnikovC a₁ a₂ a₃ a₄
    (postnikovJac a₁ a₂ a₄).det /
        (minor24 C 0 1 * minor24 C 1 2 * minor24 C 2 3 * minor24 C 0 3) =
      1 / (a₁ * a₂ * a₃ * a₄) := by
  intro C
  have hJ : (postnikovJac a₁ a₂ a₄).det ≠ 0 := by
    rw [postnikovJac_det]
    exact ne_of_gt (mul_pos h₁ h₂)
  have hA : a₁ * a₂ * a₃ * a₄ ≠ 0 := by
    exact ne_of_gt (mul_pos (mul_pos (mul_pos h₁ h₂) h₃) h₄)
  rw [postnikov_dlog_denominator a₁ a₂ a₃ a₄]
  field_simp [hJ, hA]

end PositiveGr24Scalar

end Clifford22
