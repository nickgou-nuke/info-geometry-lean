/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.ReplacementHamiltonian
import InfoGeometry.Quantum.ReplacementDetailedBalance
import InfoGeometry.Quantum.MatrixBoundaryPurification

/-!
# The native Gibbs state as a stationary replacement target

The target is the already constructed full-matrix CFC Gibbs state. Its
commutation with the Hamiltonian supplies the stationary-target condition.
The reversible generator is `ad (-I • H)`, with the factor `-I` required for
Hermitian-state evolution. The resulting balance retains the energy supplied
by the replacement bath and makes no claim of a closed GENERIC system.
-/

noncomputable section

namespace InfoGeometry.Quantum.ReplacementGibbs

open Matrix
open InfoGeometry.Quantum.ReplacementStateChannel
open InfoGeometry.Quantum.ReplacementRelaxation
open InfoGeometry.Quantum.ReplacementHamiltonian
open InfoGeometry.Quantum.ReplacementDetailedBalance
open InfoGeometry.Quantum.MatrixBoundaryPurification
open InfoGeometry.OperatorAlgebra.LieJordanDuality
open scoped ComplexOrder

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The physical infinitesimal unitary generator is skew-adjoint. -/
theorem skew_adjoint_hamiltonian (H : Mat) (hH : H.IsHermitian) :
    star ((-Complex.I) • H) = -((-Complex.I) • H) := by
  have hstar : star H = H := hH
  simp [star_smul, hstar]

/-- Functional-calculus commutation supplies the stationary Gibbs target. -/
theorem ad_normalizedGibbs_zero (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    ad ℂ ((-Complex.I) • H) (normalizedGibbs H hH β) = 0 := by
  rw [ad_apply]
  exact sub_eq_zero.mpr
    ((normalizedGibbs_commute H hH β).symm.smul_left (-Complex.I)).eq

/-- Replacement by the native Gibbs state commutes with the actual
Hamiltonian inner derivation on every full matrix input. -/
theorem ad_commute_replacement_normalizedGibbs
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    Commute (ad ℂ ((-Complex.I) • H)) (replacement (normalizedGibbs H hH β)) :=
  ad_replacement_commute_of_stationary _ _ (ad_normalizedGibbs_zero H hH β)

/-- The actual CFC Gibbs target couples the relaxation family to the physical
Hamiltonian derivation on the same full matrix carrier. -/
theorem ad_commute_relaxation_normalizedGibbs
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (weight : ℂ) :
    Commute (ad ℂ ((-Complex.I) • H)) (relaxation (normalizedGibbs H hH β) weight) :=
  ad_relaxation_commute_of_stationary _ _ weight (ad_normalizedGibbs_zero H hH β)

/-- The same stationary target gives radial/orbit trace orthogonality. -/
theorem trace_gibbs_radial_orbit_zero
    (H ρ : Mat) (hH : H.IsHermitian) (β : ℝ) :
    Matrix.trace ((ρ - normalizedGibbs H hH β) * ad ℂ ((-Complex.I) • H) ρ) = 0 :=
  trace_radial_orbit_zero _ _ _ (ad_normalizedGibbs_zero H hH β)

/-- The constructed trace-one Gibbs state is fixed by the combined generator. -/
theorem normalizedGibbs_generator_stationary [Nonempty (Fin n)]
    (H : Mat) (hH : H.IsHermitian) (β γ : ℝ) :
    generator ((-Complex.I) • H) (normalizedGibbs H hH β) γ
      (normalizedGibbs H hH β) = 0 :=
  generator_stationary _ _ γ (trace_normalizedGibbs H hH β)
    (ad_normalizedGibbs_zero H hH β)

/-- The real energy rate is `γ` times its mismatch with the Gibbs target.
For `γ ≥ 0` this has the relaxation sign. No commutation of the input state
with the Hamiltonian is required. -/
theorem normalizedGibbs_energy_rate
    (H ρ : Mat) (hH : H.IsHermitian) (β γ : ℝ)
    (hρ : Matrix.trace ρ = 1) :
    (Matrix.trace (H *
      generator ((-Complex.I) • H) (normalizedGibbs H hH β) γ ρ)).re =
      γ * ((Matrix.trace (H * normalizedGibbs H hH β)).re -
        (Matrix.trace (H * ρ)).re) := by
  apply energy_rate _ _ _ _ γ _ hρ
  rw [ad_apply]
  exact sub_eq_zero.mpr ((Commute.refl H).smul_left (-Complex.I)).eq

/-- The finite relaxation formula changes system energy by `1 - weight` times
its mismatch with the native Gibbs target. This identity is algebraic for
every real `weight`; the positive-channel regime is `0 ≤ weight ≤ 1`. -/
theorem normalizedGibbs_relaxation_energy_difference
    (H ρ : Mat) (hH : H.IsHermitian) (β weight : ℝ)
    (hρ : Matrix.trace ρ = 1) :
    (Matrix.trace (H * relaxation (normalizedGibbs H hH β) (weight : ℂ) ρ)).re -
        (Matrix.trace (H * ρ)).re =
      (1 - weight) * ((Matrix.trace (H * normalizedGibbs H hH β)).re -
        (Matrix.trace (H * ρ)).re) := by
  have h := trace_relaxation_energy_difference H (normalizedGibbs H hH β) (weight : ℂ) ρ
  rw [hρ, one_mul] at h
  simpa [smul_eq_mul, Complex.mul_re] using congrArg Complex.re h

/-! ## Detailed balance of the dissipative component

The weighted symmetry below concerns `generator 0`, not the full
Hamiltonian-plus-relaxation generator. The actual CFC Gibbs density supplies
the Hermitian, positivity, and normalization hypotheses.
-/

/-- The actual Gibbs target is stationary under the replacement dissipator. -/
theorem normalizedGibbs_dissipator_stationary [Nonempty (Fin n)]
    (H : Mat) (hH : H.IsHermitian) (β γ : ℝ) :
    generator (0 : Mat) (normalizedGibbs H hH β) γ
      (normalizedGibbs H hH β) = 0 := by
  apply generator_stationary _ _ γ (trace_normalizedGibbs H hH β)
  simp [ad_apply]

/-- The right-weight form of detailed balance for the constructed Gibbs state. -/
theorem normalizedGibbs_dissipator_right_weight
    (H A : Mat) (hH : H.IsHermitian) (β γ : ℝ) :
    generator (0 : Mat) (normalizedGibbs H hH β) γ
        (A * normalizedGibbs H hH β) =
      observableGenerator (normalizedGibbs H hH β) γ A * normalizedGibbs H hH β :=
  generator_right_weight _ A γ

/-- The observable dissipator is symmetric in the actual Gibbs-weighted
pairing for arbitrary observables, without a commutation hypothesis. -/
theorem normalizedGibbs_dissipator_weighted_symm
    (H A B : Mat) (hH : H.IsHermitian) (β γ : ℝ) :
    weightedPairing (normalizedGibbs H hH β) A
        (observableGenerator (normalizedGibbs H hH β) γ B) =
      weightedPairing (normalizedGibbs H hH β)
        (observableGenerator (normalizedGibbs H hH β) γ A) B :=
  observableGenerator_weighted_symm _ A B γ
    (normalizedGibbs_posSemidef H hH β).isHermitian

/-- Every observable has nonnegative Dirichlet form for a nonnegative rate
and the normalized CFC Gibbs target. -/
theorem normalizedGibbs_dirichlet_nonneg [Nonempty (Fin n)]
    (H A : Mat) (hH : H.IsHermitian) (β γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ (-weightedPairing (normalizedGibbs H hH β) A
      (observableGenerator (normalizedGibbs H hH β) γ A)).re :=
  dirichlet_self_nonneg _ A γ (normalizedGibbs_posSemidef H hH β)
    (trace_normalizedGibbs H hH β) hγ

end InfoGeometry.Quantum.ReplacementGibbs

end
