/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

/-!
# Hodge star on the exterior square of a four-slot basis: Lorentz vs Euclidean

Coordinate certification layer for the Hodge star on `⋀²` of the four-slot basis
`e0, e1, e2` (spatial) / `e3` (time), `eta = diag(1, 1, 1, -1)`
(Pauli §4 Eq. (2), time slot last).  The star is presented on the pair carrier
whose index set is `Set.powersetCard (Fin 4) 2` (cf.
`CliffordFourExteriorGradeBridge`), enumerated
`b0 = e01, b1 = e02, b2 = e03, b3 = e12, b4 = e13, b5 = e23`
(this order fixes both column and row conventions below).

* `hodgeLorentz` (⋆ = ⋆_eta): `⋆e01 = e23`, `⋆e02 = -e13`, `⋆e03 = -e12`,
  `⋆e12 = e03`, `⋆e13 = e02`, `⋆e23 = -e01`.  It is anti-self-transposed,
  squares to `-1` (`⋆⋆ = sgn det eta = -1`), is an *anti*-isometry of the
  2-form Gram `gramLorentz = diag(1, 1, -1, 1, -1, -1)`
  (`hodgeLorentzᵀ * gramLorentz * hodgeLorentz = -gramLorentz`), has zero
  diagonal and zero trace, and `det = +1`.
* `hodgeEuclidean` (⋆ = ⋆_delta): symmetric, squares to `+1`, and is an honest
  isometry of `gramEuclidean = diag(1, 1, 1, 1, 1, 1)`
  (`hodgeEuclideanᵀ * gramEuclidean * hodgeEuclidean = gramEuclidean`).
* The self-dual / anti-self-dual Peirce pair `P± = (1 ± ⋆)/2`
  (`projSelfDual`, `projAntiSelfDual`) is idempotent **only on the Euclidean
  side**: `(1 ± ⋆_eta)/2` is *not* idempotent since `⋆_eta² = -1`.  Over
  `R`-algebras carrying `Invertible (2 : R)` the packet satisfies
  `P±² = P±`, `P+ P- = P- P+ = 0`, `P+ + P- = 1`, exactly in the idiom of
  `GrandUnification.CoquaternionicDiracDecomposition`'s split Peirce projectors.

Every statement was first arbitrated by the strict word model
`proofs/hodge_star_signature.py` (17/17 checks, including the per-column
defining wedge property `alpha ^ (⋆ alpha) = ⟨alpha, alpha⟩ vol`) before
transcription.  That census refuted the planned claim
`Sᵀ Gr S = Gr` for the Lorentz star: with `GR` diagonal the star of
`sgn det eta = -1` signature is anti-isometric, and the Lean statement below
carries the corrected sign.  No tangent, covariant-derivative, or
differential-operator layer is asserted here.
-/

namespace InfoGeometry.Algebra.HodgeStarSignatureFour

open scoped Matrix

variable {R : Type*} [Ring R]

/-- A `Fin 6` sum splits into six summands (helper for the 6×6 entry work). -/
theorem sum_fin6 {M : Type*} [AddCommMonoid M] (f : Fin 6 → M) :
    (∑ k : Fin 6, f k) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ, Fin.sum_univ_one]
  abel

/-! ### The two stars on `⋀²` -/

/-- The Lorentz `⋆` on `⋀²` of `eta = diag(1,1,1,-1)`: column `j` holds the
coefficients of `⋆ b_j` (`⋆e01 = e23`, `⋆e02 = -e13`, `⋆e03 = -e12`,
`⋆e12 = e03`, `⋆e13 = e02`, `⋆e23 = -e01`). -/
def hodgeLorentz : Matrix (Fin 6) (Fin 6) R :=
  !![0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0]

/-- The 2-form Gram of `eta`: `⟨b_i, b_j⟩ = g_ii g_jj` diagonals
`(1, 1, -1, 1, -1, -1)`. -/
def gramLorentz : Matrix (Fin 6) (Fin 6) R :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, -1]

/-- The Euclidean `⋆` on `⋀²`: `⋆e01 = e23`, `⋆e02 = -e13`, `⋆e03 = e12`,
`⋆e12 = e03`, `⋆e13 = -e02`, `⋆e23 = e01`. -/
def hodgeEuclidean : Matrix (Fin 6) (Fin 6) R :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, -1, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0]

/-- The 2-form Gram of the flat metric: the identity on the pair carrier. -/
def gramEuclidean : Matrix (Fin 6) (Fin 6) R :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Matrix units in the six-dimensional operator carrier. -/
def matrixCarrierForward : Matrix (Fin 6) (Fin 6) R :=
  Matrix.single 0 1 (1 : R)

def matrixCarrierBackward : Matrix (Fin 6) (Fin 6) R :=
  Matrix.single 1 0 (1 : R)

/-- The full matrix carrier used for the Hodge operator is noncommutative
whenever its coefficient ring is nontrivial. -/
theorem matrixCarrier_noncommutative [Nontrivial R] :
    matrixCarrierForward (R := R) * matrixCarrierBackward (R := R) ≠
      matrixCarrierBackward (R := R) * matrixCarrierForward (R := R) := by
  intro h
  simp only [matrixCarrierForward, matrixCarrierBackward] at h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have h00 := congrArg (fun M : Matrix (Fin 6) (Fin 6) R => M 0 0) h
  have hOne : (1 : R) = 0 := by simpa [Matrix.single] using h00
  exact one_ne_zero hOne

/-- The Lorentz star is anti-self-transposed. -/
theorem hodgeLorentz_antisym :
    hodgeLorentz + hodgeLorentzᵀ = (0 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hodgeLorentz, Matrix.transpose_apply]

/-- `⋆⋆ = sgn det eta = -1` on the Lorentz exterior square. -/
theorem hodgeLorentz_sq :
    hodgeLorentz * hodgeLorentz = -(1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, sum_fin6, hodgeLorentz, Matrix.one_apply] <;>
    norm_num

/-- The Lorentz star is an **anti**-isometry of the 2-form Gram
(the census-corrected sign: `sgn det eta = -1`). -/
theorem hodgeLorentz_anti_isometry :
    (hodgeLorentz : Matrix (Fin 6) (Fin 6) R)ᵀ *
      (gramLorentz : Matrix (Fin 6) (Fin 6) R) *
      (hodgeLorentz : Matrix (Fin 6) (Fin 6) R) =
      -(gramLorentz : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, sum_fin6, hodgeLorentz, gramLorentz,
      Matrix.transpose_apply] <;>
    norm_num

/-- The Lorentz star has zero trace (no fixed basis pair). -/
theorem hodgeLorentz_trace_zero :
    Matrix.trace (hodgeLorentz : Matrix (Fin 6) (Fin 6) R) = (0 : R) := by
  unfold Matrix.trace
  rw [sum_fin6]
  simp [Matrix.diag, hodgeLorentz]

/-- The Euclidean star is symmetric. -/
theorem hodgeEuclidean_symmetric :
    hodgeEuclideanᵀ = (hodgeEuclidean : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hodgeEuclidean, Matrix.transpose_apply]

/-- `⋆⋆ = sgn det delta = +1` on the Euclidean exterior square. -/
theorem hodgeEuclidean_sq :
    hodgeEuclidean * hodgeEuclidean = (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, sum_fin6, hodgeEuclidean, Matrix.one_apply] <;>
    norm_num

/-- The Euclidean star is an honest isometry of the 2-form Gram. -/
theorem hodgeEuclidean_isometry :
    (hodgeEuclidean : Matrix (Fin 6) (Fin 6) R)ᵀ *
      (gramEuclidean : Matrix (Fin 6) (Fin 6) R) *
      (hodgeEuclidean : Matrix (Fin 6) (Fin 6) R) =
      (gramEuclidean : Matrix (Fin 6) (Fin 6) R) := by
  have hgram : gramEuclidean = (1 : Matrix (Fin 6) (Fin 6) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gramEuclidean, Matrix.one_apply]
  rw [hgram, hodgeEuclidean_symmetric, Matrix.mul_one, hodgeEuclidean_sq]

/-! ### The Euclidean self-dual / anti-self-dual Peirce pair -/

section SelfDualPacket

variable [Invertible (2 : R)]

/-- Self-dual projector `P₊ = (1 + ⋆_delta)/2` on the Euclidean `⋀²`. -/
def projSelfDual : Matrix (Fin 6) (Fin 6) R :=
  (⅟(2 : R) : R) • (1 + (hodgeEuclidean : Matrix (Fin 6) (Fin 6) R))

/-- Anti-self-dual projector `P₋ = (1 - ⋆_delta)/2`. -/
def projAntiSelfDual : Matrix (Fin 6) (Fin 6) R :=
  (⅟(2 : R) : R) • (1 - (hodgeEuclidean : Matrix (Fin 6) (Fin 6) R))

theorem projSelfDual_add_projAntiSelfDual :
    projSelfDual + projAntiSelfDual = (1 : Matrix (Fin 6) (Fin 6) R) := by
  dsimp [projSelfDual, projAntiSelfDual]
  rw [← smul_add]
  have h_add : (1 + hodgeEuclidean) + (1 - hodgeEuclidean) =
      (2 : R) • (1 : Matrix (Fin 6) (Fin 6) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hodgeEuclidean, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] <;>
      norm_num
  rw [h_add, smul_smul]
  rw [invOf_mul_self (2 : R), one_smul]

lemma invOf_two_smul_mul_smul {n : Type*} [Fintype n] (M N : Matrix n n R) :
    ((⅟(2 : R) : R) • M) * ((⅟(2 : R) : R) • N) =
      ((⅟(2 : R) * ⅟(2 : R) : R)) • (M * N) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : ⅟(2 : R) * M i k = M i k * ⅟(2 : R) :=
    (Commute.ofNat_left 2 (M i k)).invOf_left.eq
  calc
    (⅟(2 : R) * M i k) * (⅟(2 : R) * N k j)
      = ⅟(2 : R) * (M i k * ⅟(2 : R)) * N k j := by noncomm_ring
    _ = ⅟(2 : R) * (⅟(2 : R) * M i k) * N k j := by rw [← hc]
    _ = ⅟(2 : R) * ⅟(2 : R) * (M i k * N k j) := by noncomm_ring

theorem projSelfDual_sq :
    (projSelfDual : Matrix (Fin 6) (Fin 6) R) * projSelfDual = projSelfDual := by
  dsimp [projSelfDual]
  rw [invOf_two_smul_mul_smul]
  have h_mul : ((1 : Matrix (Fin 6) (Fin 6) R) + hodgeEuclidean) *
      ((1 : Matrix (Fin 6) (Fin 6) R) + hodgeEuclidean) =
      (2 : R) • ((1 : Matrix (Fin 6) (Fin 6) R) + hodgeEuclidean) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, sum_fin6, hodgeEuclidean, Matrix.smul_apply,
        smul_eq_mul, Matrix.one_apply] <;>
      norm_num
  rw [h_mul, smul_smul]
  have h_coeff : ⅟(2 : R) * (⅟(2 : R) * 2) = ⅟(2 : R) := by
    rw [invOf_mul_self (2 : R), mul_one]
  have h_assoc : ⅟(2 : R) * ⅟(2 : R) * 2 = ⅟(2 : R) * (⅟(2 : R) * 2) := mul_assoc _ _ _
  rw [h_assoc, h_coeff]

theorem projAntiSelfDual_sq :
    (projAntiSelfDual : Matrix (Fin 6) (Fin 6) R) * projAntiSelfDual =
      projAntiSelfDual := by
  dsimp [projAntiSelfDual]
  rw [invOf_two_smul_mul_smul]
  have h_mul : ((1 : Matrix (Fin 6) (Fin 6) R) - hodgeEuclidean) *
      ((1 : Matrix (Fin 6) (Fin 6) R) - hodgeEuclidean) =
      (2 : R) • ((1 : Matrix (Fin 6) (Fin 6) R) - hodgeEuclidean) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, sum_fin6, hodgeEuclidean, Matrix.smul_apply,
        smul_eq_mul, Matrix.one_apply] <;>
      norm_num
  rw [h_mul, smul_smul]
  have h_coeff : ⅟(2 : R) * (⅟(2 : R) * 2) = ⅟(2 : R) := by
    rw [invOf_mul_self (2 : R), mul_one]
  have h_assoc : ⅟(2 : R) * ⅟(2 : R) * 2 = ⅟(2 : R) * (⅟(2 : R) * 2) := mul_assoc _ _ _
  rw [h_assoc, h_coeff]

theorem proj_self_dual_mul_proj_anti_self_dual :
    projSelfDual * projAntiSelfDual = (0 : Matrix (Fin 6) (Fin 6) R) := by
  dsimp [projSelfDual, projAntiSelfDual]
  rw [invOf_two_smul_mul_smul]
  have h_mul : (1 + hodgeEuclidean) * (1 - hodgeEuclidean) =
      (0 : Matrix (Fin 6) (Fin 6) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, sum_fin6, hodgeEuclidean, Matrix.one_apply] <;>
      norm_num
  rw [h_mul, smul_zero]

theorem proj_anti_self_dual_mul_proj_self_dual :
    projAntiSelfDual * projSelfDual = (0 : Matrix (Fin 6) (Fin 6) R) := by
  dsimp [projSelfDual, projAntiSelfDual]
  rw [invOf_two_smul_mul_smul]
  have h_mul : (1 - hodgeEuclidean) * (1 + hodgeEuclidean) =
      (0 : Matrix (Fin 6) (Fin 6) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, sum_fin6, hodgeEuclidean, Matrix.one_apply] <;>
      norm_num
  rw [h_mul, smul_zero]

end SelfDualPacket

end InfoGeometry.Algebra.HodgeStarSignatureFour
