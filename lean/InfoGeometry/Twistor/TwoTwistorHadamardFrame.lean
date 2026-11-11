/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Twistor.ConstituentMomentumTransport
import InfoGeometry.Algebra.MatrixNoncommutativity

/-!
# Hadamard changes of the actual two-twistor constituent frame

The raw sum/difference matrix has square `2 • 1` and determinant `-2`.
It multiplies the infinity pairing by `-2`, and the pair mass squared and
overlap-Gram determinant by `4`. The existing real scalar `paperScale`
normalizes it to a unitary involution with determinant `-1`.

The overlap convention is conjugate-linear in the first twistor. Consequently
its constituent-frame covariance is `conjugateEntries U * G * Uᵀ`.
Unitary frame changes preserve its trace and trace-free determinant. An
explicit actual-twistor counterexample excludes replacing unitarity by
`det U = 1` in the trace-free assertion.

These are finite algebraic readouts of native twistors. The statements do not
identify the trace-free determinant with a Pauli--Lubanski invariant or its
ratio with a spatial screw pitch, nor construct an equivalence of null-ray
geometries.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwoTwistorHadamardFrame

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.PerjesConventions
open InfoGeometry.Twistor.InfinityTwistor
open InfoGeometry.Twistor.TwistorKinematicTensor
open InfoGeometry.Twistor.TwistorConstituentKinematics
open InfoGeometry.Twistor.TwistorInternalSymmetry
open InfoGeometry.Twistor.ConstituentMomentumTransport
open scoped BigOperators Matrix

/-- Any alternating bilinear form acquires the determinant of a two-vector
frame change. The alternating hypothesis concerns the form itself. -/
theorem alternating_pair_mix
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (B : M →ₗ[R] M →ₗ[R] R) (hB : ∀ v, B v v = 0)
    (U : Matrix (Fin 2) (Fin 2) R) (Z : Fin 2 → M) :
    B (∑ j, U 0 j • Z j) (∑ j, U 1 j • Z j) =
      U.det * B (Z 0) (Z 1) := by
  have hswap : B (Z 1) (Z 0) = -B (Z 0) (Z 1) := by
    have h := hB (Z 0 + Z 1)
    simp only [map_add, LinearMap.add_apply, hB, zero_add, add_zero] at h
    linear_combination h
  simp only [Fin.sum_univ_two, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hB, hswap, Matrix.det_fin_two]
  ring

/-- This changes constituent labels, as opposed to the spinor-frame action
already owned by `InfinityTwistor.infinityTwistor_frameAction`. -/
theorem infinityTwistor_mix_pair
    (U : Matrix (Fin 2) (Fin 2) ℂ) (Z : Packet (Fin 2)) :
    infinityTwistor (mix U Z 0) (mix U Z 1) =
      U.det * infinityTwistor (Z 0) (Z 1) := by
  exact alternating_pair_mix infinityTwistor infinityTwistor_self U Z

/-- The native pair-mass convention is `normSq μ`; the paper's additional
factor two is already recorded in `paper_pair_mass`. -/
theorem pairMassSq_mix_pair
    (U : Matrix (Fin 2) (Fin 2) ℂ) (Z : Packet (Fin 2)) :
    pairMassSq (mix U Z 0) (mix U Z 1) =
      Complex.normSq U.det * pairMassSq (Z 0) (Z 1) := by
  change Complex.normSq (infinityTwistor (mix U Z 0) (mix U Z 1)) =
    Complex.normSq U.det * Complex.normSq (infinityTwistor (Z 0) (Z 1))
  rw [infinityTwistor_mix_pair, Complex.normSq_mul]

/-- Hermitian overlap matrix of the actual two twistor constituents. -/
def pairWittGram (Z : Packet (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => wittPair (Z i) (Z j)

theorem pairWittGram_hermitian (Z : Packet (Fin 2)) :
    (pairWittGram Z)ᴴ = pairWittGram Z := by
  ext i j
  exact wittPair_conj (Z j) (Z i)

/-- The conjugation order follows the owner's left-conjugate Witt pairing. -/
theorem pairWittGram_mix
    (U : Matrix (Fin 2) (Fin 2) ℂ) (Z : Packet (Fin 2)) :
    pairWittGram (mix U Z) =
      conjugateEntries U * pairWittGram Z * Uᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairWittGram, mix, wittPair, conjugateEntries, Matrix.mul_apply,
      Fin.sum_univ_two, smul_eq_mul] <;> ring

theorem det_conjugateEntries (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (conjugateEntries U).det = star U.det := by
  change ((Uᴴ)ᵀ).det = star U.det
  rw [Matrix.det_transpose, Matrix.det_conjTranspose]

theorem pairWittGram_det_mix
    (U : Matrix (Fin 2) (Fin 2) ℂ) (Z : Packet (Fin 2)) :
    (pairWittGram (mix U Z)).det =
      (Complex.normSq U.det : ℂ) * (pairWittGram Z).det := by
  rw [pairWittGram_mix, Matrix.det_mul, Matrix.det_mul,
    det_conjugateEntries, Matrix.det_transpose, Complex.normSq_eq_conj_mul_self]
  ring

/-- Unitarity supplies the trace invariant that determinant one alone lacks. -/
theorem pairWittGram_trace_of_unitary
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (Z : Packet (Fin 2)) :
    Matrix.trace (pairWittGram (mix U Z)) = Matrix.trace (pairWittGram Z) := by
  have ht : Uᵀ * conjugateEntries U = 1 := by
    have h := congrArg Matrix.transpose hU
    rw [Matrix.transpose_mul, Matrix.conjTranspose_transpose] at h
    have hc : U.map star = conjugateEntries U := by
      ext i j
      rfl
    rw [← hc]
    simpa using h
  rw [pairWittGram_mix, Matrix.trace_mul_cycle, ht, Matrix.one_mul]

theorem pairWittGram_det_of_unitary
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (Z : Packet (Fin 2)) :
    (pairWittGram (mix U Z)).det = (pairWittGram Z).det := by
  have hd : star U.det * U.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one]
      using congrArg Matrix.det hU
  rw [pairWittGram_det_mix, Complex.normSq_eq_conj_mul_self, hd, one_mul]

/-- Trace-free part of the actual overlap matrix; no spin interpretation is
included in the definition. -/
def pairWittTraceFree (Z : Packet (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  pairWittGram Z - (Matrix.trace (pairWittGram Z) / 2) • 1

theorem pairWittTraceFree_det (Z : Packet (Fin 2)) :
    (pairWittTraceFree Z).det =
      (pairWittGram Z).det - (Matrix.trace (pairWittGram Z)) ^ 2 / 4 := by
  simp [pairWittTraceFree, Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two]
  ring

theorem pairWittTraceFree_det_of_unitary
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (Z : Packet (Fin 2)) :
    (pairWittTraceFree (mix U Z)).det = (pairWittTraceFree Z).det := by
  rw [pairWittTraceFree_det, pairWittTraceFree_det,
    pairWittGram_det_of_unitary U hU, pairWittGram_trace_of_unitary U hU]

/-- The raw Sylvester matrix acts on the constituent label, not on spacetime
spinor components. Its entries are real even though the twistors are complex. -/
def rawHadamard : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

@[simp] theorem rawHadamard_transpose : rawHadamardᵀ = rawHadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rawHadamard]

@[simp] theorem rawHadamard_conjTranspose : rawHadamardᴴ = rawHadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rawHadamard]

@[simp] theorem conjugateEntries_rawHadamard :
    conjugateEntries rawHadamard = rawHadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [conjugateEntries, rawHadamard]

theorem rawHadamard_square : rawHadamard * rawHadamard = (2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rawHadamard, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem rawHadamard_det : rawHadamard.det = -2 := by
  norm_num [rawHadamard, Matrix.det_fin_two]

theorem rawHadamard_not_unitary : rawHadamardᴴ * rawHadamard ≠ 1 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num [rawHadamard, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Mixing the constituents and reversing one constituent's sign do not commute. -/
theorem rawHadamard_mul_sign_ne :
    rawHadamard * Matrix.diagonal ![1, -1] ≠
      Matrix.diagonal ![1, -1] * rawHadamard := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [rawHadamard, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] at h01

@[simp] theorem mix_rawHadamard_zero (Z : Packet (Fin 2)) :
    mix rawHadamard Z 0 = Z 0 + Z 1 := by
  simp [mix, rawHadamard, Fin.sum_univ_two]

@[simp] theorem mix_rawHadamard_one (Z : Packet (Fin 2)) :
    mix rawHadamard Z 1 = Z 0 - Z 1 := by
  simp [mix, rawHadamard, Fin.sum_univ_two, sub_eq_add_neg]

theorem infinityTwistor_rawHadamard (Z : Packet (Fin 2)) :
    infinityTwistor (mix rawHadamard Z 0) (mix rawHadamard Z 1) =
      -2 * infinityTwistor (Z 0) (Z 1) := by
  rw [infinityTwistor_mix_pair, rawHadamard_det]

theorem pairMassSq_rawHadamard (Z : Packet (Fin 2)) :
    pairMassSq (mix rawHadamard Z 0) (mix rawHadamard Z 1) =
      4 * pairMassSq (Z 0) (Z 1) := by
  rw [pairMassSq_mix_pair, rawHadamard_det]
  norm_num [Complex.normSq_apply]

theorem totalMomentum_rawHadamard (Z : Packet (Fin 2)) :
    totalMomentum (mix rawHadamard Z) = (2 : ℂ) • totalMomentum Z := by
  ext a b
  simp [totalMomentum, mix, rawHadamard, momentum, Matrix.vecMulVec,
    Fin.sum_univ_two, smul_eq_mul]
  ring

theorem pairWittGram_det_rawHadamard (Z : Packet (Fin 2)) :
    (pairWittGram (mix rawHadamard Z)).det = 4 * (pairWittGram Z).det := by
  rw [pairWittGram_det_mix, rawHadamard_det]
  norm_num [Complex.normSq_apply]

theorem pairWittGram_trace_rawHadamard (Z : Packet (Fin 2)) :
    Matrix.trace (pairWittGram (mix rawHadamard Z)) =
      2 * Matrix.trace (pairWittGram Z) := by
  rw [pairWittGram_mix]
  simp [conjugateEntries, rawHadamard, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

theorem pairWittTraceFree_det_rawHadamard (Z : Packet (Fin 2)) :
    (pairWittTraceFree (mix rawHadamard Z)).det =
      4 * (pairWittTraceFree Z).det := by
  rw [pairWittTraceFree_det, pairWittTraceFree_det,
    pairWittGram_det_rawHadamard, pairWittGram_trace_rawHadamard]
  ring

/-- Diagonal-to-off-diagonal conversion is conditional on the actual overlap
matrix, and retains the raw factor four. -/
theorem pairWittGram_rawHadamard_of_diagonal
    (Z : Packet (Fin 2)) (s : ℝ)
    (hZ : pairWittGram Z = !![2 * (s : ℂ), 0; 0, -2 * (s : ℂ)]) :
    pairWittGram (mix rawHadamard Z) = !![0, 4 * (s : ℂ); 4 * (s : ℂ), 0] := by
  rw [pairWittGram_mix, hZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawHadamard, conjugateEntries, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The quotient of these two finite algebraic readouts survives the common
scale. A nonzero mass premise makes this a genuine ratio. -/
theorem traceFreeDet_mass_ratio_rawHadamard
    (Z : Packet (Fin 2)) (hZ : pairMassSq (Z 0) (Z 1) ≠ 0) :
    (pairWittTraceFree (mix rawHadamard Z)).det /
        (pairMassSq (mix rawHadamard Z 0) (mix rawHadamard Z 1) : ℂ) =
      (pairWittTraceFree Z).det / (pairMassSq (Z 0) (Z 1) : ℂ) := by
  have hZ' : (pairMassSq (Z 0) (Z 1) : ℂ) ≠ 0 := by exact_mod_cast hZ
  rw [pairWittTraceFree_det_rawHadamard, pairMassSq_rawHadamard]
  push_cast
  field_simp [hZ'] <;> ring

/-- Reuse the real `1/√2` normalization already fixed by the Perjes owner. -/
def normalizedHadamard : Matrix (Fin 2) (Fin 2) ℂ := paperScale • rawHadamard

@[simp] theorem star_paperScale : star paperScale = paperScale := by
  simp [paperScale]

@[simp] theorem normalizedHadamard_conjTranspose :
    normalizedHadamardᴴ = normalizedHadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedHadamard, rawHadamard, smul_eq_mul]

theorem normalizedHadamard_square :
    normalizedHadamard * normalizedHadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedHadamard, rawHadamard, Matrix.mul_apply,
      Fin.sum_univ_two, smul_eq_mul] <;>
    first
    | ring
    | linear_combination paperScale_sq

theorem normalizedHadamard_unitary :
    normalizedHadamardᴴ * normalizedHadamard = 1 := by
  rw [normalizedHadamard_conjTranspose, normalizedHadamard_square]

@[simp] theorem normalizedHadamard_det : normalizedHadamard.det = -1 := by
  calc
    normalizedHadamard.det = -(2 * paperScale ^ 2) := by
      simp [normalizedHadamard, rawHadamard, Matrix.det_fin_two, smul_eq_mul]
      ring
    _ = -1 := by rw [paperScale_sq]

/-- The normalized frame is its own inverse on the actual twistor packet. -/
theorem mix_normalizedHadamard_involutive (Z : Packet (Fin 2)) :
    mix normalizedHadamard (mix normalizedHadamard Z) = Z := by
  rw [mix_mul, normalizedHadamard_square, mix_one]

theorem totalKinematic_normalizedHadamard (Z : Packet (Fin 2)) :
    totalKinematic (mix normalizedHadamard Z) = totalKinematic Z :=
  totalKinematic_mix normalizedHadamard normalizedHadamard_unitary Z

theorem totalMomentum_normalizedHadamard (Z : Packet (Fin 2)) :
    totalMomentum (mix normalizedHadamard Z) = totalMomentum Z := by
  rw [← totalMomentum_readout, totalKinematic_normalizedHadamard,
    totalMomentum_readout]

theorem infinityTwistor_normalizedHadamard (Z : Packet (Fin 2)) :
    infinityTwistor (mix normalizedHadamard Z 0) (mix normalizedHadamard Z 1) =
      -infinityTwistor (Z 0) (Z 1) := by
  rw [infinityTwistor_mix_pair, normalizedHadamard_det, neg_one_mul]

theorem pairMassSq_normalizedHadamard (Z : Packet (Fin 2)) :
    pairMassSq (mix normalizedHadamard Z 0) (mix normalizedHadamard Z 1) =
      pairMassSq (Z 0) (Z 1) := by
  rw [pairMassSq_mix_pair, normalizedHadamard_det]
  norm_num [Complex.normSq_apply]

theorem pairWittTraceFree_det_normalizedHadamard (Z : Packet (Fin 2)) :
    (pairWittTraceFree (mix normalizedHadamard Z)).det =
      (pairWittTraceFree Z).det :=
  pairWittTraceFree_det_of_unitary normalizedHadamard normalizedHadamard_unitary Z

/-- The normalized gate gives the off-diagonal value `2s`, while the raw
sum/difference gate gives `4s`. -/
theorem pairWittGram_normalizedHadamard_of_diagonal
    (Z : Packet (Fin 2)) (s : ℝ)
    (hZ : pairWittGram Z = !![2 * (s : ℂ), 0; 0, -2 * (s : ℂ)]) :
    pairWittGram (mix normalizedHadamard Z) =
      !![0, 2 * (s : ℂ); 2 * (s : ℂ), 0] := by
  rw [pairWittGram_mix, hZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedHadamard, rawHadamard, conjugateEntries,
      Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;>
    first
    | ring
    | linear_combination (2 * (s : ℂ)) * paperScale_sq

/-- Determinant one does not preserve the trace-free overlap determinant.
The witness packet has Gram matrix `1`, while its image under
`diag(2, 1/2)` has Gram matrix `diag(4, 1/4)`. -/
theorem det_one_not_enough_for_traceFreeDet :
    ∃ (U : Matrix (Fin 2) (Fin 2) ℂ) (Z : Packet (Fin 2)),
      U.det = 1 ∧
        (pairWittTraceFree (mix U Z)).det ≠ (pairWittTraceFree Z).det := by
  refine ⟨!![2, 0; 0, 1 / 2],
    ![((![1, 0] : Spinor2), (![1 / 2, 0] : Spinor2)),
      ((![0, 1] : Spinor2), (![0, 1 / 2] : Spinor2))], ?_, ?_⟩
  · norm_num [Matrix.det_fin_two]
  · norm_num [pairWittTraceFree, pairWittGram, mix, wittPair,
      Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two, smul_eq_mul]

end InfoGeometry.Twistor.TwoTwistorHadamardFrame
