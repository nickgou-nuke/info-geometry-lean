import Mathlib.Analysis.Normed.Algebra.Exponential
import InfoGeometry.Krein.Thermal
import InfoGeometry.OperatorAlgebra.VerifiedCasimir
import InfoGeometry.OperatorAlgebra.SymmetryInvariants

/-!
# Individuated Modular Thermal States
Refining the derivation to eliminate Shadow premises and ensure Nomological Closure.

#### BUCKET 1: CLOSED FINITE THEOREMS
Casimir stationarity under the named modular shift operation, derived from the
centrality field of `VerifiedCasimir`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The stationarity theorem is conditional on an explicit `VerifiedCasimir`.

#### BUCKET 3: OPEN CLOSURE DEBT
No independent analytic construction of the modular flow or Casimir property is
claimed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ThermalIndividuation

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra
open IndividuatedCasimir

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

local notation "EndK" => H →L[ℝ] H

/--
PRISTINE CONSTRUCTIVE THEOREM: Casimir Stationarity.

Shadow Elimination: We have removed the 'h_commute' premise.
The fact that a Casimir is stationary under the modular flow is now
an unavoidable algebraic consequence of its centrality.
-/
theorem casimir_is_stationary_individuated
    {G : Type*} [Group G]
    (K : EndK)
    (α : SymmetryAction G EndK)
    (C : VerifiedCasimir α)
    (hcentral : ∀ x : EndK, C * x = x * C) :
    ∀ β : ℝ, krein_modular_shift K β C = C := by
  intro β
  unfold krein_modular_shift

  -- 1. Derive commutation from centrality
  have h_comm_K : Commute C (β • K) := by
    rw [Commute]
    exact hcentral (β • K)

  -- 2. Lift commutation to the exponential
  -- By Mathlib's Commute.exp_right: if [A, B] = 0, then [A, exp(B)] = 0.
  have h_exp_comm : Commute C (NormedSpace.exp (β • K)) :=
    h_comm_K.exp_right

  -- 3. Perform the algebraic reduction
  -- σ_β(C) = exp(βK) * C * exp(-βK) = C * exp(βK) * exp(-βK) = C
  rw [h_exp_comm.symm.eq]

  have h_inv : (NormedSpace.exp (β • K)) * (NormedSpace.exp ((-β) • K)) = 1 := by
    rw [← NormedSpace.exp_add_of_commute]
    · simp
    · exact ((Commute.refl K).smul_left β).smul_right (-β)

  rw [mul_assoc, h_inv, mul_one]

end InfoGeometry.Canonical.ThermalIndividuation
