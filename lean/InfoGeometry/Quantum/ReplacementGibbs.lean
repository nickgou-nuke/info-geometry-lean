/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.ReplacementHamiltonian
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
open InfoGeometry.Quantum.MatrixBoundaryPurification
open InfoGeometry.OperatorAlgebra.LieJordanDuality

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
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (λ : ℂ) :
    Commute (ad ℂ ((-Complex.I) • H)) (relaxation (normalizedGibbs H hH β) λ) :=
  ad_relaxation_commute_of_stationary _ _ λ (ad_normalizedGibbs_zero H hH β)

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

/-- The finite relaxation formula changes system energy by `1 - λ` times
its mismatch with the native Gibbs target. This identity is algebraic for
every real `λ`; the positive-channel regime is `0 ≤ λ ≤ 1`. -/
theorem normalizedGibbs_relaxation_energy_difference
    (H ρ : Mat) (hH : H.IsHermitian) (β λ : ℝ)
    (hρ : Matrix.trace ρ = 1) :
    (Matrix.trace (H * relaxation (normalizedGibbs H hH β) (λ : ℂ) ρ)).re -
        (Matrix.trace (H * ρ)).re =
      (1 - λ) * ((Matrix.trace (H * normalizedGibbs H hH β)).re -
        (Matrix.trace (H * ρ)).re) := by
  have h := trace_relaxation_energy_difference H (normalizedGibbs H hH β) (λ : ℂ) ρ
  rw [hρ, one_mul] at h
  simpa [smul_eq_mul, Complex.mul_re] using congrArg Complex.re h

end InfoGeometry.Quantum.ReplacementGibbs

end
