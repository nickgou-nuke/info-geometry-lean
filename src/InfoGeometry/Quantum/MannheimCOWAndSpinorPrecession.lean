/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.PauliSoldering
import InfoGeometry.Canonical.ZitterbewegungMassEmergenceBridge
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-!
# Mannheim Part 2 (R1): COW (1975) Neutron Interferometry & Spin-1/2 4π Precession

This module formalizes the Colella–Overhauser–Werner (COW, 1975) gravitational
interferometry phase shift, the quantum equivalence principle via de Broglie
wavelengths (with an algebraic bridge to `comptonFrequency`), and the genuine
`SU(2)` spin-1/2 precession `U(θ) = exp(-i (θ / 2) σ_n)` exhibiting `4π`
periodicity (`U(2π) = -I₂ ≠ I₂`, `U(4π) = I₂`).

1. **COW (1975) Gravitational Action & Phase Shift:**
   `ΔS = -m_g g H L / v` (for a square loop `L = H`, `ΔS_COW = -m_g g H² / v`)
   and `ΔΦ_COW = ΔS_COW / ħ = -m_g g H² / (ħ v)`. Classical free-fall
   acceleration `a = (m_g / m_I) g` is mass-independent when `m_I = m_g ≠ 0`,
   whereas `ΔS_COW` and `ΔΦ_COW` separate distinct nonzero masses `m₁ ≠ m₂`.
2. **Quantum Equivalence Principle (de Broglie & Compton):**
   For `ħ ≠ 0` and `v ≠ 0`, `λ_dB(m_I) = λ_dB(m_g) ↔ m_I = m_g`, connected
   to `InfoGeometry.Canonical.ZitterbewegungMassEmergence.comptonFrequency`.
3. **Genuine `SU(2)` Spin-1/2 Rotation (`4π` Periodicity):**
   `spinHalfSU2Rot n θ = NormedSpace.exp ((-Complex.I * (θ / 2)) • pauliDir n)`
   satisfies the matrix Euler formula, belongs to `Matrix.specialUnitaryGroup (Fin 2) ℂ`,
   obeys `U(θ₁ + θ₂) = U(θ₁) * U(θ₂)`, and yields `U(2π) = -1 ≠ 1` and `U(4π) = 1`.
-/

noncomputable section

namespace InfoGeometry.Quantum.MannheimCOWAndSpinorPrecession

open Matrix
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Canonical.ZitterbewegungMassEmergence

/-! ## Part A: COW (1975) Interferometry, de Broglie Equivalence, and Compton Relation -/

/-- Gravitational action difference along a rectangular COW neutron interferometer loop
of vertical height `H`, horizontal arm length `L`, speed `v`, gravitational mass `m_g`,
and gravitational acceleration `g`: `ΔS = -m_g g H L / v`. -/
def cowActionDiff (m_g g H L v : ℝ) : ℝ :=
  -(m_g * g * H * L) / v

/-- Gravitational action difference for a square COW interferometer (`L = H`):
`ΔS_COW = -m_g g H² / v`. -/
def cowSquareActionDiff (m_g g H v : ℝ) : ℝ :=
  -(m_g * g * H ^ 2) / v

/-- Observable COW quantum phase shift:
`ΔΦ_COW = ΔS_COW / ħ = -m_g g H² / (ħ v)`. -/
def cowPhaseShift (m_g g H hbar v : ℝ) : ℝ :=
  cowSquareActionDiff m_g g H v / hbar

/-- Classical free-fall acceleration `a = (m_g / m_I) g` from Newton's law `m_I a = m_g g`. -/
def classicalFreeFallAccel (m_I m_g g : ℝ) : ℝ :=
  m_g * g / m_I

/-- Reduced de Broglie wavelength `λ_dB = ħ / (m v)`. -/
def deBroglieWavelength (hbar m v : ℝ) : ℝ :=
  hbar / (m * v)

/-- Specializing the rectangular COW action difference to a square loop (`L = H`)
recovers `cowSquareActionDiff`. -/
theorem cowSquareActionDiff_eq (m_g g H v : ℝ) :
    cowActionDiff m_g g H H v = cowSquareActionDiff m_g g H v := by
  unfold cowActionDiff cowSquareActionDiff
  ring

/-- Explicit closed form for the COW quantum phase shift `ΔΦ_COW = -m_g g H² / (ħ v)`. -/
theorem cowPhaseShift_eq (m_g g H hbar v : ℝ) :
    cowPhaseShift m_g g H hbar v = -(m_g * g * H ^ 2) / (hbar * v) := by
  unfold cowPhaseShift cowSquareActionDiff
  rw [div_div, mul_comm v hbar]

/-- Under `m_I = m_g = m ≠ 0`, classical free-fall acceleration equals `g` independently of `m`. -/
theorem classicalFreeFallAccel_eq_self {m g : ℝ} (hm : m ≠ 0) :
    classicalFreeFallAccel m m g = g := by
  unfold classicalFreeFallAccel
  field_simp [hm]

/-- Contrast between classical universality of free fall and mass dependence of the
COW interferometer: for distinct nonzero masses `m₁ ≠ m₂` (under weak equivalence
`m_I = m_g = mᵢ`) and nondegenerate `g, H, v, ħ ≠ 0`, classical free fall gives the
same acceleration `g` while both the COW action difference and COW quantum phase shift
distinguish `m₁` and `m₂`. -/
theorem classical_free_fall_mass_independent_vs_cow_mass_dependent
    (m₁ m₂ g H v hbar : ℝ)
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hm_ne : m₁ ≠ m₂)
    (hg : g ≠ 0) (hH : H ≠ 0) (hv : v ≠ 0) (hhbar : hbar ≠ 0) :
    classicalFreeFallAccel m₁ m₁ g = classicalFreeFallAccel m₂ m₂ g ∧
    cowSquareActionDiff m₁ g H v ≠ cowSquareActionDiff m₂ g H v ∧
    cowPhaseShift m₁ g H hbar v ≠ cowPhaseShift m₂ g H hbar v := by
  refine ⟨?_, ?_, ?_⟩
  · rw [classicalFreeFallAccel_eq_self hm₁, classicalFreeFallAccel_eq_self hm₂]
  · intro hS
    apply hm_ne
    unfold cowSquareActionDiff at hS
    have hscaled := congrArg (· * (-v)) hS
    field_simp [hv, hg, hH] at hscaled
    exact hscaled
  · intro hP
    apply hm_ne
    rw [cowPhaseShift_eq, cowPhaseShift_eq] at hP
    have hhv : hbar * v ≠ 0 := mul_ne_zero hhbar hv
    have hscaled := congrArg (· * (-(hbar * v))) hP
    field_simp [hhv, hg, hH] at hscaled
    exact hscaled

/-- Quantum equivalence principle via de Broglie wavelengths: for `ħ ≠ 0` and `v ≠ 0`,
equality of inertial and gravitational de Broglie wavelengths is equivalent to
equality of inertial and gravitational masses `m_I = m_g`. -/
theorem quantum_equivalence_deBroglie_iff (hbar m_I m_g v : ℝ)
    (hhbar : hbar ≠ 0) (hv : v ≠ 0) :
    deBroglieWavelength hbar m_I v = deBroglieWavelength hbar m_g v ↔ m_I = m_g := by
  constructor
  · intro h
    unfold deBroglieWavelength at h
    simp only [div_eq_mul_inv] at h
    have hinv : (m_I * v)⁻¹ = (m_g * v)⁻¹ := mul_right_injective₀ hhbar h
    have hmul : m_I * v = m_g * v := inv_injective hinv
    exact mul_left_injective₀ hv hmul
  · intro h
    rw [h]

/-- Complementarity identity linking `deBroglieWavelength` with `comptonFrequency`
from `InfoGeometry.Canonical.ZitterbewegungMassEmergenceBridge`:
`λ_dB(ħ, m, v) * ω_Z(m, c, ħ) = 2 c² / v` for `m ≠ 0` and `ħ ≠ 0`. -/
theorem deBroglieWavelength_mul_comptonFrequency (hbar m v c : ℝ)
    (hm : m ≠ 0) (hhbar : hbar ≠ 0) :
    deBroglieWavelength hbar m v * comptonFrequency m c hbar = 2 * c ^ 2 / v := by
  unfold deBroglieWavelength
  rw [comptonFrequency_eq]
  field_simp [hm, hhbar]

/-- Quantum equivalence principle across both `deBroglieWavelength` and `comptonFrequency`:
for `ħ ≠ 0`, `v ≠ 0`, and `c ≠ 0`, equality of de Broglie wavelengths, equality of
Compton Zitterbewegung frequencies, and equality of inertial and gravitational masses
are all pairwise equivalent. -/
theorem quantum_equivalence_deBroglie_compton_iff (hbar m_I m_g v c : ℝ)
    (hhbar : hbar ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0) :
    (deBroglieWavelength hbar m_I v = deBroglieWavelength hbar m_g v ↔ m_I = m_g) ∧
    (comptonFrequency m_I c hbar = comptonFrequency m_g c hbar ↔ m_I = m_g) ∧
    (deBroglieWavelength hbar m_I v = deBroglieWavelength hbar m_g v ↔
      comptonFrequency m_I c hbar = comptonFrequency m_g c hbar) := by
  have hdb : deBroglieWavelength hbar m_I v = deBroglieWavelength hbar m_g v ↔ m_I = m_g :=
    quantum_equivalence_deBroglie_iff hbar m_I m_g v hhbar hv
  have hcomp : comptonFrequency m_I c hbar = comptonFrequency m_g c hbar ↔ m_I = m_g := by
    constructor
    · intro h
      rw [comptonFrequency_eq, comptonFrequency_eq] at h
      have hscaled := congrArg (· * hbar) h
      field_simp [hhbar, hc] at hscaled
      exact hscaled
    · intro h
      rw [h]
  exact ⟨hdb, hcomp, hdb.trans hcomp.symm⟩

/-- Expressing the COW quantum phase shift in terms of the Zitterbewegung Compton
angular frequency `ω_Z = 2 m_g c² / ħ` for `c ≠ 0` and `ħ ≠ 0`:
`ΔΦ_COW = -(ω_Z g H²) / (2 c² v)`. -/
theorem cowPhaseShift_eq_comptonFrequency (m_g g H hbar v c : ℝ)
    (hc : c ≠ 0) (hhbar : hbar ≠ 0) :
    cowPhaseShift m_g g H hbar v =
      -(comptonFrequency m_g c hbar * g * H ^ 2) / (2 * c ^ 2 * v) := by
  rw [cowPhaseShift_eq, comptonFrequency_eq]
  field_simp [hc, hhbar]

/-! ## Part B: Genuine `SU(2)` Spin-1/2 Precession (`4π` Periodicity) & T16 Witnesses -/

/-- Directional Pauli matrix `σ_n = n₀ σ₁ + n₁ σ₂ + n₂ σ₃` for `n : Fin 3 → ℝ`. -/
def pauliDir (n : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (n 0 : ℂ) • σ1 + (n 1 : ℂ) • σ2 + (n 2 : ℂ) • σ3

/-- Unit-axis predicate `n₀² + n₁² + n₂² = 1` for directional vector `n : Fin 3 → ℝ`. -/
def IsUnitAxis (n : Fin 3 → ℝ) : Prop :=
  n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1

/-- Spin-1/2 `SU(2)` rotation operator `U_n(θ) = exp(-i (θ / 2) σ_n)` defined genuinely
via `NormedSpace.exp` on `Matrix (Fin 2) (Fin 2) ℂ`. -/
def spinHalfSU2Rot (n : Fin 3 → ℝ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp ((-Complex.I * ((θ / 2 : ℝ) : ℂ)) • pauliDir n)

/-- T16 explicit non-commutativity witness for Pauli matrices `σ₁ * σ₂ ≠ σ₂ * σ₁`. -/
theorem pauli_noncomm_witness : σ1 * σ2 ≠ σ2 * σ1 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp only [σ1, σ2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue,
    mul_zero, zero_add, mul_one, one_mul] at h00
  have him := congrArg Complex.im h00
  norm_num at him

/-- T16 existential non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem pauli_mat2_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨σ1, σ2, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp only [σ1, σ2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue,
    mul_zero, zero_add, mul_one, one_mul] at h00
  have him := congrArg Complex.im h00
  norm_num at him

private lemma pauliDir_explicit (n : Fin 3 → ℝ) :
    pauliDir n =
      !![(n 2 : ℂ), (n 0 : ℂ) - Complex.I * (n 1 : ℂ);
         (n 0 : ℂ) + Complex.I * (n 1 : ℂ), -(n 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliDir, σ1, σ2, σ3, sub_eq_add_neg] <;> ring

/-- `pauliDir n` is Hermitian for every real direction `n : Fin 3 → ℝ`. -/
theorem pauliDir_hermitian (n : Fin 3 → ℝ) :
    (pauliDir n)ᴴ = pauliDir n := by
  simp only [pauliDir, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, σ1_adjoint, σ2_adjoint, σ3_adjoint]

/-- `pauliDir n` is traceless for every `n : Fin 3 → ℝ`. -/
theorem pauliDir_trace (n : Fin 3 → ℝ) :
    Matrix.trace (pauliDir n) = 0 := by
  rw [pauliDir_explicit]
  simp [Matrix.trace, Fin.sum_univ_two]

/-- Squaring `pauliDir n` gives `‖n‖² I₂` for any `n : Fin 3 → ℝ`. -/
theorem pauliDir_mul_self (n : Fin 3 → ℝ) :
    pauliDir n * pauliDir n =
      ((n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pauliDir_explicit]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- For a unit axis `IsUnitAxis n`, `σ_n^2 = I₂`. -/
theorem pauliDir_sq {n : Fin 3 → ℝ} (hn : IsUnitAxis n) :
    (pauliDir n) ^ 2 = 1 := by
  rw [pow_two, pauliDir_mul_self, hn, Complex.ofReal_one, one_smul]

private lemma ring_exp_anti_involutive {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (J : 𝔸) (hJ : J ^ 2 = -1) (t : ℝ) :
    NormedSpace.exp (t • J) = Real.cos t • (1 : 𝔸) + Real.sin t • J := by
  let E : ℝ → 𝔸 := fun s => NormedSpace.exp (s • (-J))
  let C : ℝ → 𝔸 := fun s => Real.cos s • (1 : 𝔸) + Real.sin s • J
  let F : ℝ → 𝔸 := fun s => E s * C s
  have hC_diff : ∀ s : ℝ, HasDerivAt C ((-Real.sin s) • (1 : 𝔸) + Real.cos s • J) s :=
    fun s =>
      ((Real.hasDerivAt_cos s).smul_const (1 : 𝔸)).add ((Real.hasDerivAt_sin s).smul_const J)
  have hE_diff : ∀ s : ℝ, HasDerivAt E (-(E s * J)) s := fun s => by
    simpa only [E, mul_neg] using hasDerivAt_exp_smul_const (𝕂 := ℝ) (-J) s
  have hJ2 : J * J = -1 := by simpa only [pow_two] using hJ
  have hF_diff : ∀ s : ℝ, HasDerivAt F 0 s := fun s => by
    have hprod := (hE_diff s).mul (hC_diff s)
    refine hprod.congr_deriv ?_
    have hJC : J * C s = (-Real.sin s) • (1 : 𝔸) + Real.cos s • J := by
      dsimp only [C]
      rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, hJ2, smul_neg, ← neg_smul, add_comm]
    rw [← hJC, neg_mul, ← mul_assoc, neg_add_cancel]
  have hF_const : F t = F 0 :=
    is_const_of_deriv_eq_zero (fun s => (hF_diff s).differentiableAt)
      (fun s => (hF_diff s).deriv) t 0
  have hF0 : F 0 = 1 := by
    dsimp only [F, E, C]
    simp [Real.cos_zero, Real.sin_zero, NormedSpace.exp_zero]
  have hEC : NormedSpace.exp ((-t) • J) * C t = 1 := by
    have h1 : NormedSpace.exp (t • (-J)) * C t = 1 := hF_const.trans hF0
    rwa [smul_neg, ← neg_smul] at h1
  have hcomm : Commute (t • J) ((-t) • J) := ((Commute.refl J).smul_left t).smul_right (-t)
  have hadd : NormedSpace.exp (t • J) * NormedSpace.exp ((-t) • J) = 1 := by
    rw [← NormedSpace.exp_add_of_commute hcomm, ← add_smul, add_neg_cancel, zero_smul,
      NormedSpace.exp_zero]
  calc
    NormedSpace.exp (t • J) = NormedSpace.exp (t • J) * 1 := (mul_one _).symm
    _ = NormedSpace.exp (t • J) * (NormedSpace.exp ((-t) • J) * C t) := by rw [hEC]
    _ = (NormedSpace.exp (t • J) * NormedSpace.exp ((-t) • J)) * C t := (mul_assoc _ _ _).symm
    _ = 1 * C t := by rw [hadd]
    _ = C t := one_mul _

private lemma matrix_exp_anti_involutive {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J ^ 2 = -1) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • J) = (Real.cos t : ℂ) • 1 + (Real.sin t : ℂ) • J := by
  have hsmul : ∀ (r : ℝ) (M : Matrix (Fin n) (Fin n) ℂ), (r : ℂ) • M = r • M := by
    intro r M
    ext i j
    simp [Complex.real_smul]
  rw [hsmul t J, hsmul (Real.cos t) 1, hsmul (Real.sin t) J]
  open scoped Matrix.Norms.Operator in
  exact @ring_exp_anti_involutive (Matrix (Fin n) (Fin n) ℂ) _ _
    (NormedAlgebra.restrictScalars ℚ ℝ (Matrix (Fin n) (Fin n) ℂ)) _ J hJ t

/-- Euler's formula for spin-1/2 `SU(2)` rotations along a unit axis `n`:
`exp(-i (θ / 2) σ_n) = cos(θ / 2) I₂ - i sin(θ / 2) σ_n`. -/
theorem spinHalfSU2Rot_euler {n : Fin 3 → ℝ} (hn : IsUnitAxis n) (θ : ℝ) :
    spinHalfSU2Rot n θ =
      (Real.cos (θ / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        (Complex.I * (Real.sin (θ / 2) : ℂ)) • pauliDir n := by
  let J : Matrix (Fin 2) (Fin 2) ℂ := (-Complex.I) • pauliDir n
  have hJ2 : J ^ 2 = -1 := by
    dsimp only [J]
    rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hmul : pauliDir n * pauliDir n = 1 := by simpa only [pow_two] using pauliDir_sq hn
    rw [hmul, neg_mul_neg, Complex.I_mul_I, neg_one_smul]
  have hexp_eq :
      (-Complex.I * ((θ / 2 : ℝ) : ℂ)) • pauliDir n = ((θ / 2 : ℝ) : ℂ) • J := by
    dsimp only [J]
    rw [mul_comm, smul_smul]
  unfold spinHalfSU2Rot
  rw [hexp_eq, matrix_exp_anti_involutive J hJ2 (θ / 2)]
  dsimp only [J]
  rw [smul_smul, mul_neg, mul_comm (Real.sin (θ / 2) : ℂ) Complex.I, neg_smul, sub_eq_add_neg]

private lemma spinHalfSU2Rot_det_one_aux {n : Fin 3 → ℝ} (hn : IsUnitAxis n) (θ : ℝ) :
    (spinHalfSU2Rot n θ).det = 1 := by
  rw [spinHalfSU2Rot_euler hn θ, pauliDir_explicit, Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.isValue, one_ne_zero, zero_ne_one, ite_true, ite_false,
    mul_one, mul_zero, zero_sub]
  have hunit : ((n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2 + (n 2 : ℂ) ^ 2) = 1 := by
    exact_mod_cast hn
  have htrig : (Real.cos (θ / 2) : ℂ) ^ 2 + (Real.sin (θ / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (θ / 2)
  calc
    ((Real.cos (θ / 2) : ℂ) - Complex.I * (Real.sin (θ / 2) : ℂ) * (n 2 : ℂ)) *
        ((Real.cos (θ / 2) : ℂ) - Complex.I * (Real.sin (θ / 2) : ℂ) * -(n 2 : ℂ)) -
      (-(Complex.I * (Real.sin (θ / 2) : ℂ) * ((n 0 : ℂ) - Complex.I * (n 1 : ℂ)))) *
        (-(Complex.I * (Real.sin (θ / 2) : ℂ) * ((n 0 : ℂ) + Complex.I * (n 1 : ℂ))))
      = (Real.cos (θ / 2) : ℂ) ^ 2 -
          Complex.I ^ 2 * (Real.sin (θ / 2) : ℂ) ^ 2 *
            ((n 0 : ℂ) ^ 2 - Complex.I ^ 2 * (n 1 : ℂ) ^ 2 + (n 2 : ℂ) ^ 2) := by
          ring
    _ = (Real.cos (θ / 2) : ℂ) ^ 2 +
          (Real.sin (θ / 2) : ℂ) ^ 2 *
            ((n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2 + (n 2 : ℂ) ^ 2) := by
          rw [Complex.I_sq]; ring
    _ = (Real.cos (θ / 2) : ℂ) ^ 2 + (Real.sin (θ / 2) : ℂ) ^ 2 := by
          rw [hunit, mul_one]
    _ = 1 := htrig

/-- `spinHalfSU2Rot n θ` is unitary (`Uᴴ * U = 1`, `U * Uᴴ = 1`), has determinant `1`,
and belongs to `Matrix.specialUnitaryGroup (Fin 2) ℂ` for every unit axis `n` and angle `θ`. -/
theorem spinHalfSU2Rot_unitary_and_det_one {n : Fin 3 → ℝ} (hn : IsUnitAxis n) (θ : ℝ) :
    (spinHalfSU2Rot n θ)ᴴ * spinHalfSU2Rot n θ = 1 ∧
    spinHalfSU2Rot n θ * (spinHalfSU2Rot n θ)ᴴ = 1 ∧
    (spinHalfSU2Rot n θ).det = 1 ∧
    spinHalfSU2Rot n θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := (-Complex.I * ((θ / 2 : ℝ) : ℂ)) • pauliDir n
  have hA_skew : Aᴴ = -A := by
    dsimp only [A]
    rw [Matrix.conjTranspose_smul, pauliDir_hermitian n]
    simp only [Complex.star_def, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
      neg_neg, neg_smul, neg_mul]
  have hexp_conj : (spinHalfSU2Rot n θ)ᴴ = NormedSpace.exp (-A) := by
    change (NormedSpace.exp A)ᴴ = NormedSpace.exp (-A)
    rw [← Matrix.exp_conjTranspose, hA_skew]
  have hcomm1 : Commute (-A) A := (Commute.refl A).neg_left
  have hcomm2 : Commute A (-A) := (Commute.refl A).neg_right
  have hHU : (spinHalfSU2Rot n θ)ᴴ * spinHalfSU2Rot n θ = 1 := by
    rw [hexp_conj]
    change NormedSpace.exp (-A) * NormedSpace.exp A = 1
    rw [← Matrix.exp_add_of_commute (-A) A hcomm1, neg_add_cancel, NormedSpace.exp_zero]
  have hUH : spinHalfSU2Rot n θ * (spinHalfSU2Rot n θ)ᴴ = 1 := by
    rw [hexp_conj]
    change NormedSpace.exp A * NormedSpace.exp (-A) = 1
    rw [← Matrix.exp_add_of_commute A (-A) hcomm2, add_neg_cancel, NormedSpace.exp_zero]
  have hdet : (spinHalfSU2Rot n θ).det = 1 := spinHalfSU2Rot_det_one_aux hn θ
  have hmemU : spinHalfSU2Rot n θ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_unitaryGroup_iff).2 (by simpa [Matrix.star_eq_conjTranspose] using hUH)
  have hmemSU : spinHalfSU2Rot n θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff).2 ⟨hmemU, hdet⟩
  exact ⟨hHU, hUH, hdet, hmemSU⟩

private lemma spinHalfSU2Rot_coeff_add (θ₁ θ₂ : ℝ) :
    (-Complex.I * (((θ₁ + θ₂) / 2 : ℝ) : ℂ)) =
      (-Complex.I * ((θ₁ / 2 : ℝ) : ℂ)) + (-Complex.I * ((θ₂ / 2 : ℝ) : ℂ)) := by
  push_cast
  ring

/-- Group composition law for spin-1/2 rotations around a fixed axis `n`:
`U_n(θ₁ + θ₂) = U_n(θ₁) * U_n(θ₂)`. -/
theorem spinHalfSU2Rot_add (n : Fin 3 → ℝ) (θ₁ θ₂ : ℝ) :
    spinHalfSU2Rot n (θ₁ + θ₂) = spinHalfSU2Rot n θ₁ * spinHalfSU2Rot n θ₂ := by
  unfold spinHalfSU2Rot
  rw [spinHalfSU2Rot_coeff_add θ₁ θ₂, add_smul]
  have hcomm :
      Commute ((-Complex.I * ((θ₁ / 2 : ℝ) : ℂ)) • pauliDir n)
              ((-Complex.I * ((θ₂ / 2 : ℝ) : ℂ)) • pauliDir n) :=
    ((Commute.refl (pauliDir n)).smul_left _).smul_right _
  exact Matrix.exp_add_of_commute _ _ hcomm

/-- `2π` spinor sign flip: `U_n(2π) = -I₂` and `U_n(2π) ≠ I₂`. -/
theorem spinHalfSU2Rot_two_pi {n : Fin 3 → ℝ} (hn : IsUnitAxis n) :
    spinHalfSU2Rot n (2 * Real.pi) = -1 ∧ spinHalfSU2Rot n (2 * Real.pi) ≠ 1 := by
  have hhalf : (2 * Real.pi) / 2 = Real.pi := by
    have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
    field_simp [h2]
  have hneg : spinHalfSU2Rot n (2 * Real.pi) = -1 := by
    rw [spinHalfSU2Rot_euler hn (2 * Real.pi), hhalf, Real.cos_pi, Real.sin_pi]
    simp
  refine ⟨hneg, ?_⟩
  intro h1
  rw [hneg] at h1
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h1
  norm_num at h00

/-- `4π` periodicity of a spin-1/2 spinor: `U_n(4π) = +I₂`. -/
theorem spinHalfSU2Rot_four_pi {n : Fin 3 → ℝ} (hn : IsUnitAxis n) :
    spinHalfSU2Rot n (4 * Real.pi) = 1 := by
  have hhalf : (4 * Real.pi) / 2 = 2 * Real.pi := by
    ring
  rw [spinHalfSU2Rot_euler hn (4 * Real.pi), hhalf, Real.cos_two_pi, Real.sin_two_pi]
  simp

/-- Shifting the rotation angle by `2π` negates the spin-1/2 state: `U_n(θ + 2π) = -U_n(θ)`. -/
theorem spinHalfSU2Rot_add_two_pi {n : Fin 3 → ℝ} (hn : IsUnitAxis n) (θ : ℝ) :
    spinHalfSU2Rot n (θ + 2 * Real.pi) = -spinHalfSU2Rot n θ := by
  rw [spinHalfSU2Rot_add, (spinHalfSU2Rot_two_pi hn).1, mul_neg_one]

/-- Shifting the rotation angle by `4π` restores the spin-1/2 state: `U_n(θ + 4π) = U_n(θ)`. -/
theorem spinHalfSU2Rot_add_four_pi {n : Fin 3 → ℝ} (hn : IsUnitAxis n) (θ : ℝ) :
    spinHalfSU2Rot n (θ + 4 * Real.pi) = spinHalfSU2Rot n θ := by
  rw [spinHalfSU2Rot_add, spinHalfSU2Rot_four_pi hn, mul_one]

end InfoGeometry.Quantum.MannheimCOWAndSpinorPrecession
