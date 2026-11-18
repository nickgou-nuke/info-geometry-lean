/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixGibbsEntropy
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Affine scale and unitary transport of actual matrix Gibbs states

The Hamiltonian, its Gibbs weight, its normalized density, and its entropy all
remain on the existing full complex matrix carrier. Scaling the Hamiltonian
and inversely scaling the inverse temperature preserves the normalized state;
a central shift of energy only rescales the unnormalized partition weight.
Arbitrary unitary changes of frame transport the actual density by conjugation.

These are finite-dimensional endpoint identities. They construct neither a
thermalization process nor an adiabatic evolution, heat integral, or Carnot
engine. The algebraic scale parameter need only be nonzero; preserving a
positive-temperature interpretation additionally requires a positive scale.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixGibbsScaleTransport

open FiniteMatrixGibbsFunctional PolarFrameTraceDensity
open MatrixEntropyUnitaryOrbit MatrixGibbsEntropy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- Hamiltonian scale and inverse temperature occur through their product. -/
theorem gibbsDensity_smul (H : Mat) (hH : H.IsHermitian) (a β : ℝ) :
    gibbsDensity (a • H) (hH.smul (IsSelfAdjoint.all a)) β =
      gibbsDensity H hH (β * a) := by
  rw [gibbsDensity_eq_exp_neg_smul, gibbsDensity_eq_exp_neg_smul,
    smul_smul, neg_mul]

/-- A central energy shift multiplies the actual Gibbs weight by its scalar
Boltzmann factor; the remaining Hamiltonian need not be diagonal. -/
theorem gibbsDensity_add_smul_one (H : Mat) (hH : H.IsHermitian) (b β : ℝ) :
    gibbsDensity (H + b • (1 : Mat))
        (hH.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all b))) β =
      Real.exp (-β * b) • gibbsDensity H hH β := by
  have hcomm : Commute ((-β) • H) ((-β * b) • (1 : Mat)) :=
    (Commute.one_right ((-β) • H)).smul_right (-β * b)
  have hexp : NormedSpace.exp ((-β * b) • (1 : Mat)) =
      Real.exp (-β * b) • (1 : Mat) := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Mat) (-β * b)).symm
  rw [gibbsDensity_eq_exp_neg_smul, gibbsDensity_eq_exp_neg_smul,
    smul_add, smul_smul, Matrix.exp_add_of_commute _ _ hcomm, hexp,
    mul_smul_comm, mul_one]

/-- Naturality of the actual Gibbs exponential under a unitary frame change. -/
theorem gibbsDensity_unitary_conjugate (U : unitary Mat)
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    gibbsDensity ((U : Mat) * H * star (U : Mat))
        (Matrix.isHermitian_mul_mul_conjTranspose (U : Mat) hH) β =
      (U : Mat) * gibbsDensity H hH β * star (U : Mat) := by
  let φ := Unitary.conjStarAlgAut ℝ Mat U
  have hφ : Continuous φ := by
    change Continuous (fun X : Mat => (U : Mat) * X * star (U : Mat))
    fun_prop
  have hK := Matrix.isHermitian_mul_mul_conjTranspose (U : Mat) hH
  change hK.cfc (expWeight β) =
    (U : Mat) * hH.cfc (expWeight β) * star (U : Mat)
  rw [← hK.cfc_eq, ← hH.cfc_eq]
  have hf : ContinuousOn (expWeight β) (spectrum ℝ H) := by
    unfold expWeight
    fun_prop
  simpa only [φ, Unitary.conjStarAlgAut_apply] using
    (StarAlgHomClass.map_cfc φ (expWeight β) H hf hφ
      hH.isSelfAdjoint (hH.isSelfAdjoint.map φ)).symm

theorem gibbsPartition_smul (H : Mat) (hH : H.IsHermitian) (a β : ℝ) :
    gibbsPartition (a • H) (hH.smul (IsSelfAdjoint.all a)) β =
      gibbsPartition H hH (β * a) := by
  unfold gibbsPartition
  rw [gibbsDensity_smul H hH a β]

theorem gibbsPartition_add_smul_one (H : Mat) (hH : H.IsHermitian) (b β : ℝ) :
    gibbsPartition (H + b • (1 : Mat))
        (hH.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all b))) β =
      Real.exp (-β * b) * gibbsPartition H hH β := by
  unfold gibbsPartition
  rw [gibbsDensity_add_smul_one H hH b β]
  simp only [traceMass, Matrix.trace_smul, RCLike.smul_re]

theorem gibbsPartition_unitary_conjugate (U : unitary Mat)
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    gibbsPartition ((U : Mat) * H * star (U : Mat))
        (Matrix.isHermitian_mul_mul_conjTranspose (U : Mat) hH) β =
      gibbsPartition H hH β := by
  unfold gibbsPartition traceMass
  rw [gibbsDensity_unitary_conjugate U H hH β, trace_unitary_conjugate]

theorem normalizedGibbsDensity_smul
    (H : Mat) (hH : H.IsHermitian) (a β : ℝ) :
    normalizedGibbsDensity (a • H) (hH.smul (IsSelfAdjoint.all a)) β =
      normalizedGibbsDensity H hH (β * a) := by
  unfold normalizedGibbsDensity
  rw [gibbsDensity_smul H hH a β]

theorem normalizedGibbsDensity_unitary_conjugate (U : unitary Mat)
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    normalizedGibbsDensity ((U : Mat) * H * star (U : Mat))
        (Matrix.isHermitian_mul_mul_conjTranspose (U : Mat) hH) β =
      (U : Mat) * normalizedGibbsDensity H hH β * star (U : Mat) := by
  unfold normalizedGibbsDensity
  rw [gibbsDensity_unitary_conjugate U H hH β, normalizedDensity_unitary_conjugate]

/-- The transported Hamiltonian is Hermitian by native matrix operations. -/
theorem isHermitian_affine_unitary (U : unitary Mat)
    (H : Mat) (hH : H.IsHermitian) (a b : ℝ) :
    (a • ((U : Mat) * H * star (U : Mat)) + b • (1 : Mat)).IsHermitian :=
  ((Matrix.isHermitian_mul_mul_conjTranspose (U : Mat) hH).smul
    (IsSelfAdjoint.all a)).add
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.all b))

/-- Scale, central shift, and unitary covariance combined for the actual
unnormalized matrix Gibbs weight. -/
theorem gibbsDensity_affine_unitary (U : unitary Mat)
    (H : Mat) (hH : H.IsHermitian) (a b β : ℝ) (ha : a ≠ 0) :
    gibbsDensity
        (a • ((U : Mat) * H * star (U : Mat)) + b • (1 : Mat))
        (isHermitian_affine_unitary U H hH a b) (β / a) =
      Real.exp (-(β / a) * b) •
        ((U : Mat) * gibbsDensity H hH β * star (U : Mat)) := by
  have hU := Matrix.isHermitian_mul_mul_conjTranspose (U : Mat) hH
  rw [gibbsDensity_add_smul_one
    (a • ((U : Mat) * H * star (U : Mat))) (hU.smul (IsSelfAdjoint.all a)) b (β / a)]
  rw [gibbsDensity_smul ((U : Mat) * H * star (U : Mat)) hU a (β / a),
    div_mul_cancel₀ β ha, gibbsDensity_unitary_conjugate U H hH β]

theorem gibbsPartition_affine_unitary (U : unitary Mat)
    (H : Mat) (hH : H.IsHermitian) (a b β : ℝ) (ha : a ≠ 0) :
    gibbsPartition
        (a • ((U : Mat) * H * star (U : Mat)) + b • (1 : Mat))
        (isHermitian_affine_unitary U H hH a b) (β / a) =
      Real.exp (-(β / a) * b) * gibbsPartition H hH β := by
  unfold gibbsPartition
  rw [gibbsDensity_affine_unitary U H hH a b β ha]
  simp only [traceMass, Matrix.trace_smul, RCLike.smul_re, trace_unitary_conjugate]

/-- The actual energy trace transforms affinely under a simultaneous unitary
frame change. The comparison matrix may fail to commute with the Hamiltonian. -/
theorem trace_energy_affine_unitary (U : unitary Mat)
    (ρ H : Mat) (hρ : Matrix.trace ρ = 1) (a b : ℝ) :
    (Matrix.trace
      (((U : Mat) * ρ * star (U : Mat)) *
        (a • ((U : Mat) * H * star (U : Mat)) + b • (1 : Mat)))).re =
      a * (Matrix.trace (ρ * H)).re + b := by
  have hmul :
      ((U : Mat) * ρ * star (U : Mat)) *
          ((U : Mat) * H * star (U : Mat)) =
        (U : Mat) * (ρ * H) * star (U : Mat) := by
    simpa only [Unitary.conjStarAlgAut_apply] using
      (map_mul (Unitary.conjStarAlgAut ℝ Mat U) ρ H).symm
  rw [mul_add, Matrix.trace_add, Complex.add_re,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, hmul, mul_one, trace_unitary_conjugate,
    trace_unitary_conjugate, hρ]
  simp

variable [Nonempty n]

/-- Changing the zero of energy changes the partition weight but not its
trace-normalized state. -/
theorem normalizedGibbsDensity_add_smul_one
    (H : Mat) (hH : H.IsHermitian) (b β : ℝ) :
    normalizedGibbsDensity (H + b • (1 : Mat))
        (hH.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all b))) β =
      normalizedGibbsDensity H hH β := by
  unfold normalizedGibbsDensity
  rw [gibbsDensity_add_smul_one H hH b β]
  exact normalizedDensity_scale _ (gibbsDensity_strictlyPositive H hH β)
    (Real.exp (-β * b)) (Real.exp_pos _)

omit [Nonempty n] in
/-- A compensated Hamiltonian scale leaves the actual normalized state fixed. -/
theorem normalizedGibbsDensity_inverse_scale
    (H : Mat) (hH : H.IsHermitian) (a β : ℝ) (ha : a ≠ 0) :
    normalizedGibbsDensity (a • H) (hH.smul (IsSelfAdjoint.all a)) (β / a) =
      normalizedGibbsDensity H hH β := by
  rw [normalizedGibbsDensity_smul H hH a (β / a), div_mul_cancel₀ β ha]

/-- The entropy-preserving Gibbs endpoint transport is an actual unitary
conjugation, after inverse-temperature compensation and trace normalization. -/
theorem normalizedGibbsDensity_affine_unitary (U : unitary Mat)
    (H : Mat) (hH : H.IsHermitian) (a b β : ℝ) (ha : a ≠ 0) :
    normalizedGibbsDensity
        (a • ((U : Mat) * H * star (U : Mat)) + b • (1 : Mat))
        (isHermitian_affine_unitary U H hH a b) (β / a) =
      (U : Mat) * normalizedGibbsDensity H hH β * star (U : Mat) := by
  have hU := Matrix.isHermitian_mul_mul_conjTranspose (U : Mat) hH
  rw [normalizedGibbsDensity_add_smul_one
    (a • ((U : Mat) * H * star (U : Mat))) (hU.smul (IsSelfAdjoint.all a)) b (β / a)]
  rw [normalizedGibbsDensity_inverse_scale
    ((U : Mat) * H * star (U : Mat)) hU a β ha,
    normalizedGibbsDensity_unitary_conjugate U H hH β]

theorem matrixEntropy_affine_unitary (U : unitary Mat)
    (H : Mat) (hH : H.IsHermitian) (a b β : ℝ) (ha : a ≠ 0) :
    matrixEntropy (normalizedGibbsDensity
        (a • ((U : Mat) * H * star (U : Mat)) + b • (1 : Mat))
        (isHermitian_affine_unitary U H hH a b) (β / a)) =
      matrixEntropy (normalizedGibbsDensity H hH β) := by
  rw [normalizedGibbsDensity_affine_unitary U H hH a b β ha]
  exact matrixEntropy_unitary_conjugate U _
    (normalizedGibbsDensity_isStrictlyPositive H hH β)

/-- The partition correction retains precisely the central energy shift. -/
theorem log_gibbsPartition_affine_unitary (U : unitary Mat)
    (H : Mat) (hH : H.IsHermitian) (a b β : ℝ) (ha : a ≠ 0) :
    Real.log (gibbsPartition
        (a • ((U : Mat) * H * star (U : Mat)) + b • (1 : Mat))
        (isHermitian_affine_unitary U H hH a b) (β / a)) =
      Real.log (gibbsPartition H hH β) - (β / a) * b := by
  rw [gibbsPartition_affine_unitary U H hH a b β ha,
    Real.log_mul (Real.exp_pos _).ne' (gibbsPartition_pos H hH β).ne',
    Real.log_exp]
  rw [neg_mul]
  abel

/-- Actual Gibbs energy has the same affine law as the Hamiltonian. -/
theorem gibbsEnergy_affine_unitary (U : unitary Mat)
    (H : Mat) (hH : H.IsHermitian) (a b β : ℝ) (ha : a ≠ 0) :
    (Matrix.trace
      (normalizedGibbsDensity
          (a • ((U : Mat) * H * star (U : Mat)) + b • (1 : Mat))
          (isHermitian_affine_unitary U H hH a b) (β / a) *
        (a • ((U : Mat) * H * star (U : Mat)) + b • (1 : Mat)))).re =
      a * (Matrix.trace (normalizedGibbsDensity H hH β * H)).re + b := by
  rw [normalizedGibbsDensity_affine_unitary U H hH a b β ha]
  exact trace_energy_affine_unitary U _ H (trace_normalizedGibbsDensity H hH β) a b

end InfoGeometry.Canonical.MatrixGibbsScaleTransport
