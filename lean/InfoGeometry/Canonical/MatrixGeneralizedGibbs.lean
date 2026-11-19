/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixGibbsScaleTransport
import InfoGeometry.Canonical.MatrixGibbsMetriplecticEquilibrium
import Mathlib.LinearAlgebra.Pi

/-!
# Real charge parameters and full matrix Gibbs states

A finite family of Hermitian observables defines a real-linear charge pencil
`K β = ∑ a, β a • Q a`. The parameter `β` is a vector of real coefficients;
its represented thermal generator is the Hermitian matrix `K β`. The Gibbs
state is the existing `normalizedGibbsDensity (K β) _ 1`, whose exponential
and logarithm are the actual native matrix functional calculus.

The observables need not commute with one another. The entropy balance also
allows a comparison density that does not commute with the thermal generator.
Equality of normalized Gibbs states determines their generators exactly up
to a real scalar multiple of the identity. The unitary version classifies
endpoints, without asserting the existence of a controlled connecting path.

The exact weighted charge balance is the bath part of a generalized Landauer
identity. It does not by itself construct a joint system-bath process or prove
nonnegativity of quantum relative entropy. Stationarity under a separate
Hamiltonian is proved only from explicit conservation of each charge.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixGeneralizedGibbs

open FiniteMatrixGibbsFunctional PolarFrameTraceDensity MatrixEntropyUnitaryOrbit
open MatrixGibbsEntropy MatrixGibbsScaleTransport MetriplecticDissipation
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

local notation "Mat" => Matrix n n ℂ

/-- The real-linear representation of the finite charge parameter vector. -/
def chargePencil (Q : ι → Mat) : (ι → ℝ) →ₗ[ℝ] Mat :=
  ∑ a, (LinearMap.proj a : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight (Q a)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem chargePencil_apply (Q : ι → Mat) (β : ι → ℝ) :
    chargePencil Q β = ∑ a, β a • Q a := by
  simp [chargePencil]

omit [Fintype n] [DecidableEq n] in
/-- Real coefficients preserve Hermiticity without pairwise commutation. -/
theorem chargePencil_isHermitian (Q : ι → Mat)
    (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ) :
    (chargePencil Q β).IsHermitian := by
  rw [chargePencil_apply]
  exact isSelfAdjoint_sum Finset.univ
    (fun a _ => (hQ a).smul (IsSelfAdjoint.all (β a)))

omit [DecidableEq n] in
/-- The operator pairing with a state is the dual pairing with mean charges. -/
theorem trace_mul_chargePencil (Q : ι → Mat) (β : ι → ℝ) (ρ : Mat) :
    (Matrix.trace (ρ * chargePencil Q β)).re =
      ∑ a, β a * (Matrix.trace (ρ * Q a)).re := by
  let f : Mat →ₗ[ℝ] ℝ :=
    Complex.reLm.comp ((weightedTrace ρ).restrictScalars ℝ)
  change f (chargePencil Q β) = ∑ a, β a * f (Q a)
  rw [chargePencil_apply, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Conservation of each charge implies conservation of their real pencil.
The charges need not commute with one another. -/
theorem chargePencil_commutes (Q : ι → Mat) (β : ι → ℝ)
    (H : Mat) (hQH : ∀ a, Commute (Q a) H) :
    Commute (chargePencil Q β) H := by
  rw [chargePencil_apply]
  exact Commute.sum_left Finset.univ (fun a => β a • Q a) H
    (fun a _ => (hQH a).smul_left (β a))

/-- A matrix commuting with the generator commutes with its normalized Gibbs
state. This is the actual CFC centralizer relation. -/
theorem normalizedGibbsDensity_commutes_of_commute
    (K : Mat) (hK : K.IsHermitian) (β : ℝ)
    (H : Mat) (hKH : Commute K H) :
    Commute (normalizedGibbsDensity K hK β) H := by
  have hcomm : Commute (gibbsDensity K hK β) H := by
    rw [gibbsDensity, ← hK.cfc_eq]
    exact hK.isSelfAdjoint.commute_cfc hKH (expWeight β)
  change Commute
    ((traceMass (gibbsDensity K hK β))⁻¹ • gibbsDensity K hK β) H
  exact hcomm.smul_left _

/-- A generalized Gibbs state is stationary under a distinct Hamiltonian
when that Hamiltonian conserves all of its charges. -/
theorem unitaryFlow_chargePencil_eq_zero (Q : ι → Mat)
    (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ)
    (H : Mat) (hQH : ∀ a, Commute (Q a) H) :
    unitaryFlow H
      (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1) =
      0 := by
  have hcomm := normalizedGibbsDensity_commutes_of_commute
    (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1 H
    (chargePencil_commutes Q β H hQH)
  dsimp only [unitaryFlow, MetriplecticDissipation.commutator]
  rw [← hcomm.eq, sub_self, smul_zero]

variable [Nonempty n]

/-- The normalized operator logarithm records all real charge parameters. -/
theorem log_normalizedGibbsDensity_chargePencil (Q : ι → Mat)
    (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ) :
    CFC.log
        (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1) =
      -(∑ a, β a • Q a) -
        Real.log (gibbsPartition (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1) •
          (1 : Mat) := by
  rw [log_normalizedGibbsDensity, neg_one_smul]
  exact congrArg
    (fun K : Mat => -K -
      Real.log (gibbsPartition (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1) •
        (1 : Mat))
    (chargePencil_apply Q β)

/-- Gibbs entropy is the weighted mean charge plus the logarithmic partition. -/
theorem matrixEntropy_chargePencil (Q : ι → Mat)
    (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ) :
    matrixEntropy
        (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1) =
      (∑ a, β a *
        (Matrix.trace
          (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1 *
            Q a)).re) +
        Real.log (gibbsPartition (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1) := by
  rw [matrixEntropy_normalizedGibbsDensity, one_mul, trace_mul_chargePencil]

/-- The actual relative-log trace for an arbitrary trace-one comparison matrix.
Positivity is needed for its physical entropy interpretation, not this identity. -/
theorem relativeLogTrace_chargePencil (Q : ι → Mat)
    (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ)
    (ρ : Mat) (hρ : Matrix.trace ρ = 1) :
    (Matrix.trace
      (ρ * (CFC.log ρ - CFC.log
        (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1)))).re =
      -matrixEntropy ρ + (∑ a, β a * (Matrix.trace (ρ * Q a)).re) +
        Real.log (gibbsPartition (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1) := by
  rw [relativeLogTrace_eq_energy_sub_entropy _ _ _ ρ hρ,
    one_mul, trace_mul_chargePencil]

/-- Exact bath entropy accounting with vector inverse temperature. The left
side is the dual pairing of `β` with charge gains from the Gibbs reference.
No charge-charge or state-generator commutation hypothesis is imposed. -/
theorem gibbs_charge_entropy_balance (Q : ι → Mat)
    (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ)
    (ρ : Mat) (hρ : Matrix.trace ρ = 1) :
    (∑ a, β a * ((Matrix.trace (ρ * Q a)).re -
      (Matrix.trace
        (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1 *
          Q a)).re)) =
      matrixEntropy ρ - matrixEntropy
        (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1) +
        (Matrix.trace
          (ρ * (CFC.log ρ - CFC.log
            (normalizedGibbsDensity (chargePencil Q β)
              (chargePencil_isHermitian Q hQ β) 1)))).re := by
  have h := gibbs_energy_entropy_balance
    (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1 ρ hρ
  rw [one_mul, trace_mul_chargePencil, trace_mul_chargePencil] at h
  simpa only [mul_sub, Finset.sum_sub_distrib] using h

/-- A normalized Gibbs density determines its Hermitian exponent generator
exactly modulo the real scalar identity direction. -/
theorem normalizedGibbsDensity_one_eq_iff (K L : Mat)
    (hK : K.IsHermitian) (hL : L.IsHermitian) :
    normalizedGibbsDensity K hK 1 = normalizedGibbsDensity L hL 1 ↔
      ∃ c : ℝ, K = L + c • (1 : Mat) := by
  constructor
  · intro h
    have hlog := congrArg CFC.log h
    rw [log_normalizedGibbsDensity, log_normalizedGibbsDensity] at hlog
    simp only [neg_one_smul] at hlog
    refine ⟨Real.log (gibbsPartition L hL 1) - Real.log (gibbsPartition K hK 1), ?_⟩
    rw [sub_smul]
    calc
      K = -(-K - Real.log (gibbsPartition K hK 1) • (1 : Mat)) -
          Real.log (gibbsPartition K hK 1) • (1 : Mat) := by abel
      _ = -(-L - Real.log (gibbsPartition L hL 1) • (1 : Mat)) -
          Real.log (gibbsPartition K hK 1) • (1 : Mat) := by rw [hlog]
      _ = L + (Real.log (gibbsPartition L hL 1) • (1 : Mat) -
          Real.log (gibbsPartition K hK 1) • (1 : Mat)) := by abel
  · rintro ⟨c, rfl⟩
    exact normalizedGibbsDensity_add_smul_one L hL c 1

/-- Identifiability for an arbitrary real-linear Hermitian representation:
two parameters give the same state precisely when their represented difference
is a real scalar matrix. No injectivity or Lie structure is silently assumed. -/
theorem normalizedGibbsDensity_parameter_eq_iff
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : V →ₗ[ℝ] Mat) (hQ : ∀ β, (Q β).IsHermitian) (β γ : V) :
    normalizedGibbsDensity (Q β) (hQ β) 1 =
        normalizedGibbsDensity (Q γ) (hQ γ) 1 ↔
      ∃ c : ℝ, Q (β - γ) = c • (1 : Mat) := by
  rw [normalizedGibbsDensity_one_eq_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [map_sub, hc]
    abel
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [map_sub] at hc
    exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)

/-- Exact unitary endpoint compatibility of two Gibbs generators. This is
stronger than equality of entropy and supplies no controlled path by itself. -/
theorem normalizedGibbsDensity_one_eq_unitary_iff (U : unitary Mat)
    (K L : Mat) (hK : K.IsHermitian) (hL : L.IsHermitian) :
    normalizedGibbsDensity K hK 1 =
        (U : Mat) * normalizedGibbsDensity L hL 1 * star (U : Mat) ↔
      ∃ c : ℝ, K = (U : Mat) * L * star (U : Mat) + c • (1 : Mat) := by
  rw [← normalizedGibbsDensity_unitary_conjugate U L hL 1]
  exact normalizedGibbsDensity_one_eq_iff K ((U : Mat) * L * star (U : Mat)) hK
    (Matrix.isHermitian_mul_mul_conjTranspose (U : Mat) hL)

end InfoGeometry.Canonical.MatrixGeneralizedGibbs
