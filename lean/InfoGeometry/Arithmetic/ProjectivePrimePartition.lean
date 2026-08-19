/-
InfoGeometry/Arithmetic/ProjectivePrimePartition.lean

Witness-gated modular flow of von Mangoldt weights over the projective
temperature interval.

This module is a narrow facade over `PrimitivePrimeProjectiveTemperature`.
It gives the compact-flow name `projectivePrimePartition` and a model
calibration relation, without asserting analytic continuation, the prime number
theorem, an Euler product, or the logarithmic-derivative theorem for `ζ`.
-/

import InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature

noncomputable section

namespace InfoGeometry.Arithmetic.ProjectivePrimePartition

open InfoGeometry.Arithmetic
open InfoGeometry.Thermodynamics.ProjectiveTemperature
open InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature

/-! ## 1. Projective von Mangoldt partition flow -/

/--
Projected von Mangoldt partition evaluated at inverted temperature `u = 1 / β`.

This is the finite-support compact-temperature shadow of the prime-weighted
Dirichlet readout.  It is not an analytic assertion about `-ζ'/ζ`.
-/
def projectivePrimePartition (A : Finset ℕ) (u : ℝ) : ℝ :=
  arithmeticPrimePartition A (betaInvert u)

/-- The projective prime partition is the restricted prime partition at `β = u⁻¹`. -/
theorem projectivePrimePartition_eq_restricted
    (A : Finset ℕ) (u : ℝ) :
    projectivePrimePartition A u =
      arithmeticPrimeRestrictedPartition A (betaInvert u) :=
  rfl

/-- The projective prime partition is nonnegative. -/
theorem projectivePrimePartition_nonneg
    (A : Finset ℕ) (u : ℝ) :
    0 ≤ projectivePrimePartition A u := by
  simpa [projectivePrimePartition] using
    arithmeticPrimePartition_nonneg A (betaInvert u)

/-- The projective prime partition is positive on supports containing a positive-weight state. -/
lemma projectivePrimePartition_pos_of_mem_positive_weight
    {A : Finset ℕ} {u : ℝ} {n : ℕ}
    (hnA : n ∈ A) (hΛ : 0 < realVonMangoldt n) (hn : 1 < n) :
    0 < projectivePrimePartition A u := by
  exact arithmeticPrimeRestrictedPartition_pos_of_mem_positive_weight
    (β := betaInvert u) hnA hΛ hn

/-- Strict positivity of the finite projective prime partition is equivalent to
having a support element with positive von Mangoldt weight. -/
theorem projectivePrimePartition_pos_iff_mem_positive_weight
    (A : Finset ℕ) (u : ℝ) :
    0 < projectivePrimePartition A u ↔
      ∃ n ∈ A, 0 < realVonMangoldt n ∧ 1 < n := by
  constructor
  · intro h
    by_contra hmem
    push_neg at hmem
    have hz : projectivePrimePartition A u = 0 := by
      unfold projectivePrimePartition arithmeticPrimePartition
      rw [Finset.sum_eq_zero]
      intro n hn
      by_cases hn1 : 1 < n
      · have hΛ0 : realVonMangoldt n = 0 := by
          apply le_antisymm
          · apply le_of_not_gt
            intro hΛ
            exact (not_lt_of_ge (hmem n hn hΛ)) hn1
          · exact realVonMangoldt_nonneg n
        rw [hΛ0, zero_mul]
      · rw [primitiveMellinKernel_eq_zero_of_le_one (le_of_not_gt hn1)]
        simp
    linarith
  · rintro ⟨n, hnA, hΛ, hn⟩
    exact projectivePrimePartition_pos_of_mem_positive_weight hnA hΛ hn

/-- A prime contained in the finite support gives positive projective prime
partition mass. -/
theorem projectivePrimePartition_pos_of_mem_prime
    {A : Finset ℕ} {u : ℝ} {p : ℕ}
    (hpA : p ∈ A) (hp : p.Prime) :
    0 < projectivePrimePartition A u := by
  apply projectivePrimePartition_pos_of_mem_positive_weight hpA
    ((realVonMangoldt_pos_iff p).mpr hp.isPrimePow)
  exact hp.one_lt

/-- A prime in the support prevents the projective prime partition from
vanishing. -/
theorem projectivePrimePartition_ne_zero_of_mem_prime
    {A : Finset ℕ} {u : ℝ} {p : ℕ}
    (hpA : p ∈ A) (hp : p.Prime) :
    projectivePrimePartition A u ≠ 0 := by
  exact ne_of_gt (projectivePrimePartition_pos_of_mem_prime hpA hp)

/-- The finite projective prime partition vanishes exactly when no support
element has positive von Mangoldt weight above the cutoff. -/
theorem projectivePrimePartition_eq_zero_iff_no_mem_positive_weight
    (A : Finset ℕ) (u : ℝ) :
    projectivePrimePartition A u = 0 ↔
      ¬ ∃ n ∈ A, 0 < realVonMangoldt n ∧ 1 < n := by
  constructor
  · intro h hpos
    have hstrict : 0 < projectivePrimePartition A u :=
      (projectivePrimePartition_pos_iff_mem_positive_weight A u).2 hpos
    linarith
  · intro hnone
    have hnotpos : ¬ 0 < projectivePrimePartition A u := by
      intro hpos
      exact hnone
        ((projectivePrimePartition_pos_iff_mem_positive_weight A u).1 hpos)
    exact le_antisymm (le_of_not_gt hnotpos)
      (projectivePrimePartition_nonneg A u)

/--
On the compact interval `(0, 1)`, the inverted temperature lies in the
ordinary low-temperature regime `β > 1`.
-/
theorem one_lt_projective_beta_of_mem_Ioo
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    1 < betaInvert u :=
  one_lt_betaInvert_of_mem_Ioo_zero_one hu

/-! ## 2. Model calibration -/

/--
Calibration relation for a physical/geometric state space whose internal modular
flow readout reproduces the finite projective von Mangoldt partition on
`u ∈ (0, 1)`.
-/
structure ProjectivePrimeCalibration (State : Type*) where
  /-- Map a finite arithmetic support to the geometric state. -/
  stateOfFinset : Finset ℕ → State

  /-- Endogenous modular generator/flow readout on the state. -/
  modularFlowReadout : State → ℝ → ℝ

  /-- Calibration law on the compact projective temperature interval. -/
  flow_eq_projectivePrimePartition :
    ∀ A : Finset ℕ, ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      modularFlowReadout (stateOfFinset A) u = projectivePrimePartition A u

namespace ProjectivePrimeCalibration

variable {State : Type*}
variable (C : ProjectivePrimeCalibration State)

/-- The modular flow readout matches the arithmetic prime partition at `β = 1 / u`. -/
theorem flowReadout_eq_arithmeticPrimePartition
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    C.modularFlowReadout (C.stateOfFinset A) u =
      arithmeticPrimePartition A (betaInvert u) := by
  rw [C.flow_eq_projectivePrimePartition A u hu]
  rfl

/-- The calibrated modular flow readout is nonnegative on finite supports. -/
theorem modularFlowReadout_nonneg
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ C.modularFlowReadout (C.stateOfFinset A) u := by
  rw [C.flow_eq_projectivePrimePartition A u hu]
  exact projectivePrimePartition_nonneg A u

/-- The calibrated modular flow readout is positive on supports containing a positive-weight state. -/
lemma modularFlowReadout_pos_of_mem_positive_weight
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) {n : ℕ}
    (hnA : n ∈ A) (hΛ : 0 < realVonMangoldt n) (hn : 1 < n) :
    0 < C.modularFlowReadout (C.stateOfFinset A) u := by
  rw [C.flow_eq_projectivePrimePartition A u hu]
  exact projectivePrimePartition_pos_of_mem_positive_weight hnA hΛ hn

end ProjectivePrimeCalibration

end InfoGeometry.Arithmetic.ProjectivePrimePartition
