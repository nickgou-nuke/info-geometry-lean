/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauHilbertSchmidtOnsager
import InfoGeometry.Physics.MatrixTraceBimodulePairingNative
import InfoGeometry.Thermodynamics.FiniteEntropyLeaves
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Module

/-! # Real matrix radial mixing and orthogonal orbit motion

The carrier is the full real matrix algebra in every finite dimension.  The
radial operation mixes a trace-one matrix with the isotropic density.  Its
positivity, composition, purity law, and covariance are proved, without a
commutation hypothesis on the state and the orbit generator.

A common nonzero scalar amplitude disappears under trace normalization.
Consequently that amplitude is distinct from this radial change of a
normalized state.  The orthogonality statement uses the existing positive
Hilbert--Schmidt pairing and a symmetric state; a skew generator gives a
symmetric trace-zero orbit direction.  This file asserts no entropy formula,
spacetime interpretation, or construction of a three-dimensional Bloch ball.
-/

noncomputable section

namespace InfoGeometry.Thermo.RealDensityRadialFlow

open Matrix
open InfoGeometry.Physics
open SouriauHilbertSchmidtOnsager

variable {n : ℕ}

/-- The central trace-one density, when the dimension is nonzero. -/
def uniformDensity (n : ℕ) : MatrixSpace n :=
  (n : ℝ)⁻¹ • 1

/-- Radial mixing about the central density on the full matrix carrier. -/
def radialMix (r : ℝ) (ρ : MatrixSpace n) : MatrixSpace n :=
  r • ρ + (1 - r) • uniformDensity n

/-- The displacement from the central density. -/
def radialDirection (ρ : MatrixSpace n) : MatrixSpace n :=
  ρ - uniformDensity n

/-- Normalization by the ordinary real matrix trace. -/
def traceNormalize (A : MatrixSpace n) : MatrixSpace n :=
  (Matrix.trace A)⁻¹ • A

@[simp] theorem uniformDensity_transpose :
    (uniformDensity n).transpose = uniformDensity n := by
  simp [uniformDensity]

theorem uniformDensity_trace (hn : n ≠ 0) :
    Matrix.trace (uniformDensity n) = 1 := by
  simp [uniformDensity, Matrix.trace_smul, hn]

theorem uniformDensity_posSemidef : (uniformDensity n).PosSemidef :=
  Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg n))

theorem uniformDensity_mul (A : MatrixSpace n) :
    uniformDensity n * A = (n : ℝ)⁻¹ • A := by
  simp [uniformDensity]

theorem mul_uniformDensity (A : MatrixSpace n) :
    A * uniformDensity n = (n : ℝ)⁻¹ • A := by
  simp [uniformDensity]

theorem uniformDensity_commute (A : MatrixSpace n) :
    Commute (uniformDensity n) A := by
  exact (uniformDensity_mul A).trans (mul_uniformDensity A).symm

@[simp] theorem radialMix_zero (ρ : MatrixSpace n) :
    radialMix 0 ρ = uniformDensity n := by
  simp [radialMix]

@[simp] theorem radialMix_one (ρ : MatrixSpace n) : radialMix 1 ρ = ρ := by
  simp [radialMix]

@[simp] theorem radialMix_uniformDensity (r : ℝ) :
    radialMix r (uniformDensity n) = uniformDensity n := by
  unfold radialMix
  module

theorem radialMix_eq_center_add (r : ℝ) (ρ : MatrixSpace n) :
    radialMix r ρ = uniformDensity n + r • radialDirection ρ := by
  unfold radialMix radialDirection
  module

theorem radialDirection_radialMix (r : ℝ) (ρ : MatrixSpace n) :
    radialDirection (radialMix r ρ) = r • radialDirection ρ := by
  rw [radialDirection, radialMix_eq_center_add]
  abel

/-- Contraction parameters compose multiplicatively. -/
theorem radialMix_comp (r s : ℝ) (ρ : MatrixSpace n) :
    radialMix r (radialMix s ρ) = radialMix (r * s) ρ := by
  unfold radialMix
  module

theorem radialMix_trace (hn : n ≠ 0) (r : ℝ) (ρ : MatrixSpace n)
    (hρ : Matrix.trace ρ = 1) : Matrix.trace (radialMix r ρ) = 1 := by
  simp [radialMix, Matrix.trace_add, Matrix.trace_smul,
    uniformDensity_trace hn, hρ]

theorem radialDirection_trace (hn : n ≠ 0) (ρ : MatrixSpace n)
    (hρ : Matrix.trace ρ = 1) : Matrix.trace (radialDirection ρ) = 0 := by
  simp [radialDirection, Matrix.trace_sub, uniformDensity_trace hn, hρ]

/-- The entire segment from the central density to a positive state is positive. -/
theorem radialMix_posSemidef (r : ℝ) (ρ : MatrixSpace n)
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hρ : ρ.PosSemidef) :
    (radialMix r ρ).PosSemidef :=
  (hρ.smul hr₀).add (uniformDensity_posSemidef.smul (sub_nonneg.mpr hr₁))

theorem traceNormalize_trace (A : MatrixSpace n) (hA : Matrix.trace A ≠ 0) :
    Matrix.trace (traceNormalize A) = 1 := by
  simp [traceNormalize, Matrix.trace_smul, hA]

theorem traceNormalize_posSemidef (A : MatrixSpace n)
    (hA : A.PosSemidef) (htr : 0 < Matrix.trace A) :
    (traceNormalize A).PosSemidef :=
  hA.smul (le_of_lt (inv_pos.mpr htr))

/-- Common amplitude is a normalization gauge, even for noncommuting matrices. -/
theorem traceNormalize_smul (c : ℝ) (hc : c ≠ 0) (A : MatrixSpace n) :
    traceNormalize (c • A) = traceNormalize A := by
  unfold traceNormalize
  rw [Matrix.trace_smul]
  change (c * Matrix.trace A)⁻¹ • (c • A) = (Matrix.trace A)⁻¹ • A
  rw [_root_.mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

theorem traceNormalize_exp_smul (s : ℝ) (A : MatrixSpace n) :
    traceNormalize (Real.exp s • A) = traceNormalize A :=
  traceNormalize_smul (Real.exp s) (Real.exp_ne_zero s) A

/-! ## Covariance under native real unitary conjugation -/

theorem trace_unitary_conjugate (U : unitary (MatrixSpace n)) (A : MatrixSpace n) :
    Matrix.trace ((U : MatrixSpace n) * A * star (U : MatrixSpace n)) =
      Matrix.trace A := by
  exact InfoGeometry.Thermodynamics.FiniteEntropyLeaves.trace_conjugate
    (U : MatrixSpace n) (star (U : MatrixSpace n)) A (by simp)

theorem radialMix_unitary_conjugate (U : unitary (MatrixSpace n))
    (r : ℝ) (ρ : MatrixSpace n) :
    radialMix r ((U : MatrixSpace n) * ρ * star (U : MatrixSpace n)) =
      (U : MatrixSpace n) * radialMix r ρ * star (U : MatrixSpace n) := by
  let φ := Unitary.conjStarAlgAut ℝ (MatrixSpace n) U
  change radialMix r (φ ρ) = φ (radialMix r ρ)
  simp [radialMix, uniformDensity]

theorem traceNormalize_unitary_conjugate (U : unitary (MatrixSpace n))
    (A : MatrixSpace n) :
    traceNormalize ((U : MatrixSpace n) * A * star (U : MatrixSpace n)) =
      (U : MatrixSpace n) * traceNormalize A * star (U : MatrixSpace n) := by
  simp [traceNormalize, trace_unitary_conjugate]

/-- Full matrix trace-square purity is invariant on each orthogonal orbit. -/
theorem purity_unitary_conjugate (U : unitary (MatrixSpace n)) (ρ : MatrixSpace n) :
    Matrix.trace
        (((U : MatrixSpace n) * ρ * star (U : MatrixSpace n)) *
          ((U : MatrixSpace n) * ρ * star (U : MatrixSpace n))) =
      Matrix.trace (ρ * ρ) := by
  have hmul :
      ((U : MatrixSpace n) * ρ * star (U : MatrixSpace n)) *
          ((U : MatrixSpace n) * ρ * star (U : MatrixSpace n)) =
        (U : MatrixSpace n) * (ρ * ρ) * star (U : MatrixSpace n) := by
    simpa only [Unitary.conjStarAlgAut_apply] using
      (map_mul (Unitary.conjStarAlgAut ℝ (MatrixSpace n) U) ρ ρ).symm
  rw [hmul, trace_unitary_conjugate]

/-! ## Exact radial purity and its positive metric interpretation -/

theorem trace_uniformDensity_mul (ρ : MatrixSpace n) (hρ : Matrix.trace ρ = 1) :
    Matrix.trace (uniformDensity n * ρ) = (n : ℝ)⁻¹ := by
  simp [uniformDensity_mul, Matrix.trace_smul, hρ]

theorem trace_mul_uniformDensity (ρ : MatrixSpace n) (hρ : Matrix.trace ρ = 1) :
    Matrix.trace (ρ * uniformDensity n) = (n : ℝ)⁻¹ := by
  rw [Matrix.trace_mul_comm]
  exact trace_uniformDensity_mul ρ hρ

theorem trace_uniformDensity_sq (hn : n ≠ 0) :
    Matrix.trace (uniformDensity n * uniformDensity n) = (n : ℝ)⁻¹ :=
  trace_uniformDensity_mul _ (uniformDensity_trace hn)

theorem radialDirection_trace_square (hn : n ≠ 0) (ρ : MatrixSpace n)
    (hρ : Matrix.trace ρ = 1) :
    Matrix.trace (radialDirection ρ * radialDirection ρ) =
      Matrix.trace (ρ * ρ) - (n : ℝ)⁻¹ := by
  unfold radialDirection
  rw [sub_mul, mul_sub, mul_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_sub, trace_uniformDensity_mul ρ hρ,
    trace_mul_uniformDensity ρ hρ, trace_uniformDensity_sq hn]
  ring

/-- This is the radius-squared law on all trace-one real matrices. -/
theorem radialMix_purity (hn : n ≠ 0) (r : ℝ) (ρ : MatrixSpace n)
    (hρ : Matrix.trace ρ = 1) :
    Matrix.trace (radialMix r ρ * radialMix r ρ) =
      (n : ℝ)⁻¹ + r ^ 2 * (Matrix.trace (ρ * ρ) - (n : ℝ)⁻¹) := by
  simp only [radialMix, add_mul, mul_add, smul_mul_smul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [trace_uniformDensity_mul ρ hρ, trace_mul_uniformDensity ρ hρ,
    trace_uniformDensity_sq hn]
  ring

theorem hilbertSchmidtPairing_self_eq_zero_iff (A : MatrixSpace n) :
    hilbertSchmidtPairing A A = 0 ↔ A = 0 := by
  simpa [hilbertSchmidtPairing] using
    (Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := A))

theorem radialDirection_hilbertSchmidt (hn : n ≠ 0) (ρ : MatrixSpace n)
    (htr : Matrix.trace ρ = 1) (hsym : ρ.transpose = ρ) :
    hilbertSchmidtPairing (radialDirection ρ) (radialDirection ρ) =
      Matrix.trace (ρ * ρ) - (n : ℝ)⁻¹ := by
  unfold hilbertSchmidtPairing
  have hs : (radialDirection ρ).transpose = radialDirection ρ := by
    simp [radialDirection, hsym]
  rw [hs, radialDirection_trace_square hn ρ htr]

theorem purity_ge_uniformDensity (hn : n ≠ 0) (ρ : MatrixSpace n)
    (htr : Matrix.trace ρ = 1) (hsym : ρ.transpose = ρ) :
    (n : ℝ)⁻¹ ≤ Matrix.trace (ρ * ρ) := by
  apply sub_nonneg.mp
  rw [← radialDirection_hilbertSchmidt hn ρ htr hsym]
  exact hilbertSchmidtPairing_nonneg _

theorem purity_eq_uniformDensity_iff (hn : n ≠ 0) (ρ : MatrixSpace n)
    (htr : Matrix.trace ρ = 1) (hsym : ρ.transpose = ρ) :
    Matrix.trace (ρ * ρ) = (n : ℝ)⁻¹ ↔ ρ = uniformDensity n := by
  rw [← sub_eq_zero, ← radialDirection_hilbertSchmidt hn ρ htr hsym,
    hilbertSchmidtPairing_self_eq_zero_iff, radialDirection, sub_eq_zero]

private theorem scalar_radial_purity_lt (c p r : ℝ)
    (hcp : c < p) (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    c + r ^ 2 * (p - c) < p := by
  have hr₂ : r ^ 2 < 1 := by nlinarith
  have hmul := mul_lt_mul_of_pos_right hr₂ (sub_pos.mpr hcp)
  linarith

theorem radialMix_purity_lt (hn : n ≠ 0) (r : ℝ) (ρ : MatrixSpace n)
    (htr : Matrix.trace ρ = 1) (hsym : ρ.transpose = ρ)
    (hne : ρ ≠ uniformDensity n) (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Matrix.trace (radialMix r ρ * radialMix r ρ) < Matrix.trace (ρ * ρ) := by
  rw [radialMix_purity hn r ρ htr]
  have hne' : Matrix.trace (ρ * ρ) ≠ (n : ℝ)⁻¹ :=
    mt (purity_eq_uniformDensity_iff hn ρ htr hsym).mp hne
  exact scalar_radial_purity_lt _ _ _
    (lt_of_le_of_ne (purity_ge_uniformDensity hn ρ htr hsym) hne'.symm) hr₀ hr₁

/-! ## A genuine trace-zero orbit tangent orthogonal to the radial direction -/

theorem trace_commutatorActionNative (K ρ : MatrixSpace n) :
    Matrix.trace (commutatorActionNative K ρ) = 0 := by
  simp only [commutatorActionNative, leftActionNative, rightActionNative,
    Matrix.trace_sub, Matrix.trace_mul_comm K ρ, sub_self]

theorem self_tracePairing_commutator (K ρ : MatrixSpace n) :
    tracePairingNative ρ (commutatorActionNative K ρ) = 0 := by
  have h := commutator_tracePairing_energyOrthogonal ρ K
  dsimp [tracePairingNative, commutatorActionNative,
    leftActionNative, rightActionNative] at h ⊢
  rw [mul_sub, Matrix.trace_sub] at h ⊢
  exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm

theorem commutatorActionNative_symmetric (K ρ : MatrixSpace n)
    (hK : K.transpose = -K) (hρ : ρ.transpose = ρ) :
    (commutatorActionNative K ρ).transpose = commutatorActionNative K ρ := by
  dsimp [commutatorActionNative, leftActionNative, rightActionNative]
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hK, hρ]
  noncomm_ring

/-- The radial state displacement is orthogonal to every conjugation direction.
The metric is Hilbert--Schmidt; this is not a universal metric assertion. -/
theorem radialDirection_orthogonal_commutator (K ρ : MatrixSpace n)
    (hρ : ρ.transpose = ρ) :
    hilbertSchmidtPairing (radialDirection ρ) (commutatorActionNative K ρ) = 0 := by
  unfold hilbertSchmidtPairing radialDirection
  rw [Matrix.transpose_sub, hρ, uniformDensity_transpose, sub_mul, Matrix.trace_sub]
  change tracePairingNative ρ (commutatorActionNative K ρ) -
    Matrix.trace (uniformDensity n * commutatorActionNative K ρ) = 0
  rw [self_tracePairing_commutator, uniformDensity_mul, Matrix.trace_smul,
    trace_commutatorActionNative]
  simp

/-- A noncommuting real pair has a nonzero orbit direction and radial orthogonality. -/
theorem exists_noncommuting_symmetric_orbit :
    ∃ K R : Matrix (Fin 2) (Fin 2) ℝ, K * R ≠ R * K ∧ K.transpose = -K ∧
      R.transpose = R ∧ R.PosSemidef ∧ Matrix.trace R = 1 ∧
      hilbertSchmidtPairing (radialDirection R) (commutatorActionNative K R) = 0 := by
  let K : MatrixSpace 2 := !![0, -1; 1, 0]
  let ρ : MatrixSpace 2 := !![1, 0; 0, 0]
  have hK : K.transpose = -K := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [K]
  have hρ : ρ.transpose = ρ := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [ρ]
  have hpos : ρ.PosSemidef := by
    have heq : ρ = Matrix.diagonal (![1, 0] : Fin 2 → ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [ρ, Matrix.diagonal]
    rw [heq]
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  refine ⟨K, ρ, ?_, hK, hρ, hpos, ?_, radialDirection_orthogonal_commutator K ρ hρ⟩
  · intro h
    have h01 := congrArg (fun A : MatrixSpace 2 => A 0 1) h
    norm_num [K, ρ, Matrix.mul_apply, Fin.sum_univ_two] at h01
  · norm_num [ρ, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

end InfoGeometry.Thermo.RealDensityRadialFlow

end
