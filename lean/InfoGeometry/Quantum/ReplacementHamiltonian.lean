/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.ReplacementRelaxation
import InfoGeometry.OperatorAlgebra.LieJordanTraceDuality

/-!
# Replacement channels and ordered Hamiltonian derivations

The existing replacement map `X ↦ trace X • σ` acts on the full finite matrix
algebra. Its commutator with the existing inner derivation is another
replacement map, with target `ad K σ`. This gives the exact stationary-target
condition for commuting reversible and relaxation operations.

The radial/orbit trace identity retains its defect before stationarity is
assumed. The energy balance also retains the heat exchange with the target:
replacement relaxation need not preserve system energy. These statements do
not assert a closed GENERIC system, entropy monotonicity, or a Carnot cycle.
For physical unitary evolution, `K` must be skew-adjoint; the algebraic trace
identities themselves need no adjoint assumptions.
-/

noncomputable section

namespace InfoGeometry.Quantum.ReplacementHamiltonian

open Matrix
open InfoGeometry.Quantum.ReplacementStateChannel
open InfoGeometry.Quantum.ReplacementRelaxation
open InfoGeometry.OperatorAlgebra.LieJordanDuality
open InfoGeometry.OperatorAlgebra.LieJordanTraceDuality

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- Cyclicity annihilates the trace of the existing inner derivation. -/
theorem trace_ad_zero (K X : Mat) : Matrix.trace (ad ℂ K X) = 0 := by
  rw [ad_apply, Matrix.trace_sub, Matrix.trace_mul_comm K X, sub_self]

/-- The exact failure of covariance of a replacement map on an arbitrary
matrix input. No commutation of `K`, `σ`, or `X` is assumed. -/
theorem ad_replacement_defect (K σ X : Mat) :
    ad ℂ K (replacement σ X) - replacement σ (ad ℂ K X) =
      Matrix.trace X • ad ℂ K σ := by
  change ad ℂ K (Matrix.trace X • σ) - Matrix.trace (ad ℂ K X) • σ = _
  rw [map_smul, trace_ad_zero, zero_smul, sub_zero]

/-- The pointwise defect is an identity in the associative endomorphism
algebra, with multiplication given by composition. -/
theorem ad_replacement_commutator (K σ : Mat) :
    ad ℂ K * replacement σ - replacement σ * ad ℂ K =
      replacement (ad ℂ K σ) := by
  apply LinearMap.ext
  intro X
  change ad ℂ K (replacement σ X) - replacement σ (ad ℂ K X) =
    Matrix.trace X • ad ℂ K σ
  exact ad_replacement_defect K σ X

/-- A stationary target makes the derivation commute with replacement. -/
theorem ad_replacement_commute_of_stationary (K σ : Mat)
    (hKσ : ad ℂ K σ = 0) : Commute (ad ℂ K) (replacement σ) := by
  change ad ℂ K * replacement σ = replacement σ * ad ℂ K
  apply LinearMap.ext
  intro X
  change ad ℂ K (replacement σ X) = replacement σ (ad ℂ K X)
  apply sub_eq_zero.mp
  simpa only [hKσ, smul_zero] using ad_replacement_defect K σ X

/-- For a trace-one target, stationarity is also necessary for covariance. -/
theorem ad_replacement_commute_iff (K σ : Mat)
    (hσ : Matrix.trace σ = 1) :
    Commute (ad ℂ K) (replacement σ) ↔ ad ℂ K σ = 0 := by
  constructor
  · intro h
    have hcomm := congrArg (fun f : Module.End ℂ Mat => f σ) h.eq
    change ad ℂ K (replacement σ σ) = replacement σ (ad ℂ K σ) at hcomm
    have hdefect := ad_replacement_defect K σ σ
    rw [hcomm, sub_self, hσ, one_smul] at hdefect
    exact hdefect.symm
  · exact ad_replacement_commute_of_stationary K σ

/-- The relaxation family has the exact scaled covariance defect of its
replacement part. No input matrix is required to commute with the generator. -/
theorem ad_relaxation_defect (K σ : Mat) (weight : ℂ) (X : Mat) :
    ad ℂ K (relaxation σ weight X) - relaxation σ weight (ad ℂ K X) =
      (1 - weight) • (Matrix.trace X • ad ℂ K σ) := by
  simp only [relaxation_apply, map_add, map_smul]
  calc
    weight • ad ℂ K X + (1 - weight) • ad ℂ K (replacement σ X) -
        (weight • ad ℂ K X + (1 - weight) • replacement σ (ad ℂ K X)) =
        (1 - weight) • (ad ℂ K (replacement σ X) - replacement σ (ad ℂ K X)) := by
      rw [smul_sub]
      abel
    _ = (1 - weight) • (Matrix.trace X • ad ℂ K σ) := by
      rw [ad_replacement_defect]

/-- Stationarity of the target makes every relaxation map commute with the
inner derivation on the full matrix algebra. -/
theorem ad_relaxation_commute_of_stationary (K σ : Mat) (weight : ℂ)
    (hKσ : ad ℂ K σ = 0) : Commute (ad ℂ K) (relaxation σ weight) := by
  change ad ℂ K * relaxation σ weight = relaxation σ weight * ad ℂ K
  apply LinearMap.ext
  intro X
  change ad ℂ K (relaxation σ weight X) = relaxation σ weight (ad ℂ K X)
  apply sub_eq_zero.mp
  simpa only [hKσ, smul_zero] using ad_relaxation_defect K σ weight X

/-- The radial direction and the conjugation-orbit tangent have this exact
trace defect before the reference state is assumed stationary. -/
theorem trace_radial_orbit_defect (K σ ρ : Mat) :
    Matrix.trace ((ρ - σ) * ad ℂ K ρ) =
      Matrix.trace (ad ℂ K σ * ρ) := by
  simp only [ad_apply, sub_mul, mul_sub, Matrix.trace_sub, ← mul_assoc]
  rw [Matrix.trace_mul_cycle ρ K ρ, Matrix.trace_mul_cycle σ ρ K]
  abel

/-- A stationary reference makes radial displacement trace-orthogonal to
the infinitesimal conjugation orbit. -/
theorem trace_radial_orbit_zero (K σ ρ : Mat)
    (hKσ : ad ℂ K σ = 0) :
    Matrix.trace ((ρ - σ) * ad ℂ K ρ) = 0 := by
  rw [trace_radial_orbit_defect, hKσ, zero_mul, Matrix.trace_zero]

/-- For Hermitian reference and input, this is orthogonality for the actual
star-trace pairing on the full matrix algebra. -/
theorem star_trace_radial_orbit_zero (K σ ρ : Mat)
    (hσ : star σ = σ) (hρ : star ρ = ρ) (hKσ : ad ℂ K σ = 0) :
    Matrix.trace (star (ρ - σ) * ad ℂ K ρ) = 0 := by
  rw [star_sub, hρ, hσ]
  exact trace_radial_orbit_zero K σ ρ hKσ

/-- A candidate infinitesimal generator combining the inner derivation with
linear replacement relaxation. The real coefficient is unrestricted here;
this definition alone does not construct or differentiate a trajectory. -/
def generator (K σ : Mat) (γ : ℝ) : Module.End ℂ Mat :=
  ad ℂ K + γ • (replacement σ - LinearMap.id)

@[simp] theorem generator_apply (K σ X : Mat) (γ : ℝ) :
    generator K σ γ X = ad ℂ K X + γ • (replacement σ X - X) := rfl

/-- Trace-one replacement targets make the generator trace preserving. -/
theorem trace_generator_zero (K σ X : Mat) (γ : ℝ)
    (hσ : Matrix.trace σ = 1) : Matrix.trace (generator K σ γ X) = 0 := by
  rw [generator_apply, Matrix.trace_add, trace_ad_zero, Matrix.trace_smul,
    Matrix.trace_sub, replacement_trace σ X hσ]
  simp

/-- The target is a fixed point when it is normalized and stationary. -/
theorem generator_stationary (K σ : Mat) (γ : ℝ)
    (hσ : Matrix.trace σ = 1) (hKσ : ad ℂ K σ = 0) :
    generator K σ γ σ = 0 := by
  rw [generator_apply, hKσ, replacement_on_density σ σ hσ]
  simp

/-- Cyclic trace pairing transports conservation of the energy observable
to a zero reversible energy rate. -/
theorem trace_reversible_energy_zero (K H ρ : Mat)
    (hKH : ad ℂ K H = 0) : Matrix.trace (H * ad ℂ K ρ) = 0 := by
  have h := trace_ad_skew K H ρ
  rw [hKH, zero_mul, Matrix.trace_zero, zero_add] at h
  exact h

/-- Exact open-system energy balance, including the normalization factor
for an arbitrary matrix input. -/
theorem trace_generator_energy (K H σ ρ : Mat) (γ : ℝ)
    (hKH : ad ℂ K H = 0) :
    Matrix.trace (H * generator K σ γ ρ) =
      γ • (Matrix.trace ρ * Matrix.trace (H * σ) - Matrix.trace (H * ρ)) := by
  rw [generator_apply, mul_add, Matrix.trace_add,
    trace_reversible_energy_zero K H ρ hKH, zero_add,
    Matrix.mul_smul, Matrix.trace_smul, mul_sub, Matrix.trace_sub]
  simp [replacement, Matrix.mul_smul, Matrix.trace_smul]

/-- On normalized states, the real energy rate is the bath-target mismatch.
It vanishes only when this mismatch or the rate vanishes; system energy is
not imposed as a Casimir of replacement relaxation. -/
theorem energy_rate (K H σ ρ : Mat) (γ : ℝ)
    (hKH : ad ℂ K H = 0) (hρ : Matrix.trace ρ = 1) :
    (Matrix.trace (H * generator K σ γ ρ)).re =
      γ * ((Matrix.trace (H * σ)).re - (Matrix.trace (H * ρ)).re) := by
  rw [trace_generator_energy K H σ ρ γ hKH, hρ]
  simp

/-- The finite relaxation stroke has exactly this energy difference. The
centered-action theorem controls the full matrix change before taking trace. -/
theorem trace_relaxation_energy_difference (H σ : Mat) (weight : ℂ) (ρ : Mat) :
    Matrix.trace (H * relaxation σ weight ρ) - Matrix.trace (H * ρ) =
      (1 - weight) • (Matrix.trace ρ * Matrix.trace (H * σ) - Matrix.trace (H * ρ)) := by
  have hchange : relaxation σ weight ρ - ρ = (1 - weight) • (replacement σ ρ - ρ) := by
    calc
      relaxation σ weight ρ - ρ =
          (relaxation σ weight ρ - replacement σ ρ) + (replacement σ ρ - ρ) := by abel
      _ = weight • (ρ - replacement σ ρ) + (replacement σ ρ - ρ) := by
        rw [relaxation_sub_replacement]
      _ = (1 - weight) • (replacement σ ρ - ρ) := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
  calc
    Matrix.trace (H * relaxation σ weight ρ) - Matrix.trace (H * ρ) =
        Matrix.trace (H * (relaxation σ weight ρ - ρ)) := by
      rw [mul_sub, Matrix.trace_sub]
    _ = (1 - weight) • (Matrix.trace ρ * Matrix.trace (H * σ) - Matrix.trace (H * ρ)) := by
      rw [hchange, Matrix.mul_smul, Matrix.trace_smul, mul_sub, Matrix.trace_sub]
      simp [replacement, Matrix.mul_smul, Matrix.trace_smul]

/-- Exact finite energy bookkeeping for two ordered stages: change the
state at the initial Hamiltonian, then switch the Hamiltonian at the final
state. This does not assert path independence of heat for a general stroke. -/
theorem trace_energy_increment (H₀ H₁ ρ₀ ρ₁ : Mat) :
    Matrix.trace (H₁ * ρ₁) - Matrix.trace (H₀ * ρ₀) =
      Matrix.trace (H₀ * (ρ₁ - ρ₀)) + Matrix.trace ((H₁ - H₀) * ρ₁) := by
  rw [mul_sub, sub_mul, Matrix.trace_sub, Matrix.trace_sub]
  abel

end InfoGeometry.Quantum.ReplacementHamiltonian

end
