/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixGeneralizedGibbs
import InfoGeometry.Canonical.MatrixRelativeEntropy

/-!
# Generalized Gibbs bath bounds and unitary passivity

The native full-matrix Klein inequality turns the actual relative-log trace
balance into an entropy bound on weighted charge gains. It also proves
passivity of a Gibbs state under arbitrary unitary conjugation for its own
thermal generator. Neither the charges nor the comparison state are required
to commute with that generator.

These are finite-dimensional faithful-state results. The entropy on the bath
bound is the bath's own entropy change; replacing it by a memory's entropy
loss additionally requires a joint process and a correlation argument.
There is no independent scalar temperature or universal scalar Carnot ratio
for a generic vector of charge coefficients.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixGeneralizedGibbsInequalities

open MatrixEntropyUnitaryOrbit MatrixGibbsEntropy MatrixGibbsScaleTransport
open MatrixGeneralizedGibbs MatrixRelativeEntropy
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι]

local notation "Mat" => Matrix n n ℂ

/-- Weighted charge gain bounds the bath entropy increase from the actual
Gibbs reference. This is the bath inequality, with no erasure process assumed. -/
theorem entropy_change_le_charge_gain (Q : ι → Mat)
    (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ)
    (ρ : Mat) (hρ : IsStrictlyPositive ρ) (htρ : Matrix.trace ρ = 1) :
    matrixEntropy ρ - matrixEntropy
        (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1) ≤
      ∑ a, β a * ((Matrix.trace (ρ * Q a)).re -
        (Matrix.trace
          (normalizedGibbsDensity (chargePencil Q β)
            (chargePencil_isHermitian Q hQ β) 1 * Q a)).re) := by
  rw [gibbs_charge_entropy_balance Q hQ β ρ htρ]
  exact le_add_of_nonneg_right
    (relativeLogTrace_nonneg ρ
      (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1)
      hρ (normalizedGibbsDensity_isStrictlyPositive _ _ _)
      htρ (trace_normalizedGibbsDensity _ _ _))

/-- Among faithful trace-one matrices with the same mean charges, the actual
generalized Gibbs state has maximal entropy. No simultaneous eigenbasis for
the charge family is required. -/
theorem matrixEntropy_le_gibbs_of_charge_eq (Q : ι → Mat)
    (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ)
    (ρ : Mat) (hρ : IsStrictlyPositive ρ) (htρ : Matrix.trace ρ = 1)
    (hcharge : ∀ a, (Matrix.trace (ρ * Q a)).re =
      (Matrix.trace
        (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1 *
          Q a)).re) :
    matrixEntropy ρ ≤ matrixEntropy
      (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1) := by
  have h := entropy_change_le_charge_gain Q hQ β ρ hρ htρ
  have hzero : (∑ a, β a * ((Matrix.trace (ρ * Q a)).re -
      (Matrix.trace
        (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1 *
          Q a)).re)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [hcharge a, sub_self, mul_zero]
  rw [hzero] at h
  exact sub_nonpos.mp h

/-- At positive scalar inverse temperature, a unitary operation cannot lower
the expected energy of the corresponding Gibbs state. -/
theorem gibbsEnergy_le_unitary_energy (H : Mat) (hH : H.IsHermitian)
    (β : ℝ) (hβ : 0 < β) (U : unitary Mat) :
    (Matrix.trace (normalizedGibbsDensity H hH β * H)).re ≤
      (Matrix.trace
        (((U : Mat) * normalizedGibbsDensity H hH β * star (U : Mat)) * H)).re := by
  let ρ := normalizedGibbsDensity H hH β
  have hρ : IsStrictlyPositive ρ := normalizedGibbsDensity_isStrictlyPositive H hH β
  have htρ : Matrix.trace ρ = 1 := trace_normalizedGibbsDensity H hH β
  have hUρ : IsStrictlyPositive ((U : Mat) * ρ * star (U : Mat)) := by
    dsimp only [ρ]
    rw [← normalizedGibbsDensity_unitary_conjugate U H hH β]
    exact normalizedGibbsDensity_isStrictlyPositive _ _ _
  have htUρ : Matrix.trace ((U : Mat) * ρ * star (U : Mat)) = 1 := by
    rw [trace_unitary_conjugate, htρ]
  have hD := relativeLogTrace_nonneg
    ((U : Mat) * ρ * star (U : Mat)) ρ hUρ hρ htUρ htρ
  have hbalance := gibbs_energy_entropy_balance H hH β
    ((U : Mat) * ρ * star (U : Mat)) htUρ
  have hs := matrixEntropy_unitary_conjugate U ρ hρ
  change β * ((Matrix.trace (((U : Mat) * ρ * star (U : Mat)) * H)).re -
    (Matrix.trace (ρ * H)).re) =
      matrixEntropy ((U : Mat) * ρ * star (U : Mat)) - matrixEntropy ρ +
        (Matrix.trace (((U : Mat) * ρ * star (U : Mat)) *
          (CFC.log ((U : Mat) * ρ * star (U : Mat)) - CFC.log ρ))).re at hbalance
  rw [hs, sub_self, zero_add] at hbalance
  change (Matrix.trace (ρ * H)).re ≤
    (Matrix.trace (((U : Mat) * ρ * star (U : Mat)) * H)).re
  have hprod : 0 ≤ β * ((Matrix.trace (((U : Mat) * ρ * star (U : Mat)) * H)).re -
      (Matrix.trace (ρ * H)).re) := by rw [hbalance]; exact hD
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hβ).mp hprod)

/-- A generalized Gibbs state is passive for the weighted charge functional
represented by its own thermal generator. Individual charge gains need not
be nonnegative, and no ordering of the coefficient vector is needed. -/
theorem gibbs_charge_le_unitary_charge (Q : ι → Mat)
    (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ) (U : unitary Mat) :
    (∑ a, β a *
      (Matrix.trace
        (normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1 *
          Q a)).re) ≤
      ∑ a, β a *
        (Matrix.trace
          (((U : Mat) *
            normalizedGibbsDensity (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1 *
              star (U : Mat)) * Q a)).re := by
  have h := gibbsEnergy_le_unitary_energy
    (chargePencil Q β) (chargePencil_isHermitian Q hQ β) 1 zero_lt_one U
  simpa only [trace_mul_chargePencil] using h

end InfoGeometry.Canonical.MatrixGeneralizedGibbsInequalities
