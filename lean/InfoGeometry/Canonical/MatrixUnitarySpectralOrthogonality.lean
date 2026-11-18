/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FreeEnergyDissipationRate
import InfoGeometry.Canonical.FreeEnergyEquilibriumUnitaryBridge
import InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit
import InfoGeometry.Core.JordanMultiplicationClosure

/-!
# Spectral directions orthogonal to the native unitary matrix flow

The reversible flow is the existing `MetriplecticDissipation.unitaryFlow` on
the full complex matrix algebra. Cyclic trace makes it orthogonal to the
centralizer of the state, hence to real functional-calculus directions and
the radial direction about the maximally mixed state. The Hamiltonian and
state are not assumed to commute.

The final result discharges the unitary-invariance premise of the existing
free-energy-rate theorem for the concrete score `H + T • (CFC.log ρ + 1)`.
That rate is the owner's algebraic trace contraction. This file does not
identify the score with a Frechet derivative, construct a density-preserving
Onsager flow, or prove a thermal cycle or entropy-production inequality.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixUnitarySpectralOrthogonality

open MetriplecticDissipation
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- The existing Hamiltonian commutator flow is tangent to the trace-one
affine space; this algebraic identity does not require positivity. -/
theorem trace_unitaryFlow (H ρ : Mat) :
    Matrix.trace (unitaryFlow H ρ) = 0 := by
  dsimp [unitaryFlow, MetriplecticDissipation.commutator]
  rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm H ρ,
    sub_self, smul_zero]

/-- The trace pairing with a matrix commuting with the state annihilates the
Hamiltonian tangent, without a commutation assumption on the Hamiltonian. -/
theorem trace_mul_unitaryFlow_of_commute (H ρ A : Mat) (hA : Commute A ρ) :
    Matrix.trace (A * unitaryFlow H ρ) = 0 := by
  have hcyclic := InfoGeometry.Core.JordanMultiplicationClosure.trace_adjoint_identity
    (Matrix.traceAddMonoidHom n ℂ) Matrix.trace_mul_comm ρ A H
  change Matrix.trace (A * (ρ * H - H * ρ)) +
    Matrix.trace ((ρ * A - A * ρ) * H) = 0 at hcyclic
  rw [← hA.eq, sub_self, zero_mul, Matrix.trace_zero, add_zero] at hcyclic
  have hzero : Matrix.trace (A * (H * ρ - ρ * H)) = 0 := by
    rw [← neg_sub (ρ * H) (H * ρ), mul_neg, Matrix.trace_neg, hcyclic, neg_zero]
  dsimp [unitaryFlow, MetriplecticDissipation.commutator]
  rw [Matrix.mul_smul, Matrix.trace_smul, hzero, smul_zero]

/-- For Hermitian directions the trace identity is exactly the complex
Hilbert–Schmidt orthogonality identity. -/
theorem hilbertSchmidt_unitaryFlow_of_commute
    (H ρ A : Mat) (hA : A.IsHermitian) (hcomm : Commute A ρ) :
    Matrix.trace (star A * unitaryFlow H ρ) = 0 := by
  rw [hA.star_eq]
  exact trace_mul_unitaryFlow_of_commute H ρ A hcomm

/-- Every real functional-calculus direction of a Hermitian state is normal
to its unitary tangent for the Hilbert–Schmidt pairing. -/
theorem hilbertSchmidt_cfc_unitaryFlow
    (H ρ : Mat) (hρ : ρ.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (star (cfc f ρ) * unitaryFlow H ρ) = 0 := by
  have hsa : IsSelfAdjoint (cfc f ρ) := IsSelfAdjoint.cfc
  apply hilbertSchmidt_unitaryFlow_of_commute H ρ (cfc f ρ) hsa
  have hcomm := cfc_commute_cfc f (id : ℝ → ℝ) ρ
  rwa [cfc_id ℝ ρ hρ] at hcomm

/-- The actual CFC logarithm, rather than a supplied logarithm variable,
has zero Hilbert–Schmidt pairing with the reversible tangent. -/
theorem hilbertSchmidt_log_unitaryFlow
    (H ρ : Mat) (hρ : ρ.IsHermitian) :
    Matrix.trace (star (CFC.log ρ) * unitaryFlow H ρ) = 0 :=
  hilbertSchmidt_cfc_unitaryFlow H ρ hρ Real.log

/-- The trace-one state space is centered at `1 / card n`. This vector is
distinct from scaling an unnormalized positive weight before normalization. -/
def radialDirection (ρ : Mat) : Mat :=
  ρ - ((Fintype.card n : ℝ)⁻¹) • (1 : Mat)

theorem radialDirection_isHermitian (ρ : Mat) (hρ : ρ.IsHermitian) :
    (radialDirection ρ).IsHermitian :=
  hρ.sub ((IsSelfAdjoint.all ((Fintype.card n : ℝ)⁻¹)).smul (IsSelfAdjoint.one Mat))

theorem radialDirection_commutes (ρ : Mat) : Commute (radialDirection ρ) ρ :=
  (Commute.refl ρ).sub_left ((Commute.one_left ρ).smul_left _)

/-- Radial and unitary directions are orthogonal in every finite dimension;
only in dimension two does one radius parametrize the state spectrum. -/
theorem hilbertSchmidt_radial_unitaryFlow
    (H ρ : Mat) (hρ : ρ.IsHermitian) :
    Matrix.trace (star (radialDirection ρ) * unitaryFlow H ρ) = 0 :=
  hilbertSchmidt_unitaryFlow_of_commute H ρ (radialDirection ρ)
    (radialDirection_isHermitian ρ hρ) (radialDirection_commutes ρ)

/-- The concrete logarithmic free-energy score. A theorem identifying this
matrix with a Frechet derivative is a separate analytic obligation. -/
def freeEnergyScore (H ρ : Mat) (T : ℝ) : Mat :=
  H + T • (CFC.log ρ + (1 : Mat))

theorem freeEnergyScore_isHermitian
    (H ρ : Mat) (hH : H.IsHermitian) (T : ℝ) :
    (freeEnergyScore H ρ T).IsHermitian :=
  hH.add ((IsSelfAdjoint.all T).smul (IsSelfAdjoint.cfc.add (IsSelfAdjoint.one Mat)))

/-- The exact unitary-invariance premise needed by the existing dissipation
owner is derived for this score, with no assumption `[H, ρ] = 0`. -/
theorem hilbertSchmidt_freeEnergyScore_unitaryFlow
    (H ρ : Mat) (hH : H.IsHermitian) (hρ : ρ.IsHermitian) (T : ℝ) :
    Matrix.trace (star (freeEnergyScore H ρ T) * unitaryFlow H ρ) = 0 := by
  have henergy : Matrix.trace (H * unitaryFlow H ρ) = 0 :=
    MetriplecticEquilibrium.unitary_flow_conserves_energy H ρ
  have hlog : Matrix.trace (CFC.log ρ * unitaryFlow H ρ) = 0 := by
    have h := hilbertSchmidt_log_unitaryFlow H ρ hρ
    have hsa : IsSelfAdjoint (CFC.log ρ) := IsSelfAdjoint.cfc
    rwa [hsa.star_eq] at h
  rw [(freeEnergyScore_isHermitian H ρ hH T).star_eq]
  simp only [freeEnergyScore, add_mul, smul_mul_assoc, Matrix.trace_add,
    Matrix.trace_smul, one_mul, henergy, hlog, trace_unitaryFlow,
    zero_add, smul_zero]

/-- The existing algebraic rate is exactly minus the Onsager quadratic form
for the actual logarithmic score. No positivity of the mobility is assumed
for this identity. -/
theorem freeEnergyRate_logarithmic_eq
    (H ρ : Mat) (hH : H.IsHermitian) (hρ : ρ.IsHermitian) (T : ℝ)
    (M : Mat →ₗ[ℂ] Mat) :
    freeEnergyRate ⟨ρ, H, freeEnergyScore H ρ T, M⟩ =
      -(Matrix.trace (star (freeEnergyScore H ρ T) * M (freeEnergyScore H ρ T))).re := by
  change (Matrix.trace (star (freeEnergyScore H ρ T) *
    (unitaryFlow H ρ - M (freeEnergyScore H ρ T)))).re = _
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re,
    hilbertSchmidt_freeEnergyScore_unitaryFlow H ρ hH hρ T,
    Complex.zero_re, zero_sub]

/-- Instantiation of the existing dissipation theorem: its unitary-invariance
premise is now proved from the actual CFC score rather than supplied. -/
theorem freeEnergyRate_logarithmic_nonpos
    (H ρ : Mat) (hH : H.IsHermitian) (hρ : ρ.IsHermitian) (T : ℝ)
    (M : Mat →ₗ[ℂ] Mat)
    (hM : ∀ A : Mat, 0 ≤ (Matrix.trace (star A * M A)).re) :
    freeEnergyRate ⟨ρ, H, freeEnergyScore H ρ T, M⟩ ≤ 0 := by
  apply freeEnergy_rate_nonpos
  · exact hM
  · exact congrArg Complex.re
      (hilbertSchmidt_freeEnergyScore_unitaryFlow H ρ hH hρ T)

end InfoGeometry.Canonical.MatrixUnitarySpectralOrthogonality
