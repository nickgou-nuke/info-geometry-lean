import Mathlib
import InfoGeometry.Canonical.TensorColimitExpectation
import InfoGeometry.Thermo.BuresWassersteinKMSCost

/-!
# Bures Metric Stabilization

Theorem-safe stabilization interface for Bures/Fisher-type information metrics
along a compatible local-state tower.

This file does **not** construct the Bures metric from density operators, prove a
UHF/CAR completion theorem, or identify the limit metric with a geometric bulk
metric.  Instead, it records the exact finite-to-limit readback pattern needed
for those claims:

* a compatible family of finite linear functionals on a tensor tower;
* a supplied colimit carrier extending that family;
* finite and limit positive-state domains;
* finite and limit Bures-Wasserstein metric data; and
* explicit isometry/readout witnesses for the bonding maps and the limit cone.
-/

namespace BuresMetricStabilization

open InfoGeometry.Canonical.TensorColimitExpectation
open InfoGeometry.Thermo.BuresWassersteinKMSCost

universe u v w

variable {R : Type u} [CommSemiring R]
variable {A : ℕ → Type v}
variable [∀ n, Semiring (A n)] [∀ n, Algebra R (A n)]
variable {bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)}

/--
Finite-to-limit Bures metric stabilization data.

`State n` is the local state space at tensor depth `n`. `StateInf` is the chosen
limit-state carrier.  The fields `rho` and `sigma` select a compatible pair of
local positive states whose Bures/Wasserstein cost is tracked through the tower.
-/
structure BuresMetricStabilizationBridge
    (L : TensorInductiveLimit (R := R) (A := A) bond) where
  family : CompatibleFunctionalFamily (R := R) (A := A) bond
  globalFunctional : L.LimitFunctional
  extendsFamily : L.ExtendsFamily family globalFunctional

  State : ℕ → Type w
  StateInf : Type w

  Ω : ∀ n : ℕ, PositiveStateDomain (State n)
  ΩInf : PositiveStateDomain StateInf

  BW : ∀ n : ℕ, BuresWassersteinDatum (State n) (Ω n)
  BWInf : BuresWassersteinDatum StateInf ΩInf

  embedState :
    ∀ n : ℕ, PositiveState (Ω n) → PositiveState (Ω (n + 1))
  toLimitState :
    ∀ n : ℕ, PositiveState (Ω n) → PositiveState ΩInf

  rho : ∀ n : ℕ, PositiveState (Ω n)
  sigma : ∀ n : ℕ, PositiveState (Ω n)

  rho_compat : ∀ n : ℕ, embedState n (rho n) = rho (n + 1)
  sigma_compat : ∀ n : ℕ, embedState n (sigma n) = sigma (n + 1)

  one_step_isometry :
    ∀ n : ℕ,
      (BW (n + 1)).squaredDist (embedState n (rho n)) (embedState n (sigma n)) =
        (BW n).squaredDist (rho n) (sigma n)

  limit_readout :
    ∀ n : ℕ,
      BWInf.squaredDist (toLimitState n (rho n)) (toLimitState n (sigma n)) =
        (BW n).squaredDist (rho n) (sigma n)

namespace BuresMetricStabilizationBridge

variable {L : TensorInductiveLimit (R := R) (A := A) bond}
variable (B : BuresMetricStabilizationBridge L)

/-- The supplied global functional recovers the finite family at every stage. -/
theorem global_functional_recovers_stage
    (n : ℕ) (x : A n) :
    B.globalFunctional (L.inj n x) = B.family.omega n x :=
  L.limit_functional_recovers_stage B.family B.globalFunctional B.extendsFamily n x

/-- The supplied global functional implies the finite compatibility equations. -/
theorem global_implies_compatible
    (n : ℕ) (x : A n) :
    B.family.omega (n + 1) (bond n x) = B.family.omega n x :=
  L.extending_limit_functional_implies_compatible B.family B.globalFunctional B.extendsFamily n x

/-- The Bures/Wasserstein cost of the tracked local states is preserved by one tensor step. -/
theorem bures_cost_one_step_stable (n : ℕ) :
    (B.BW (n + 1)).squaredDist (B.rho (n + 1)) (B.sigma (n + 1)) =
      (B.BW n).squaredDist (B.rho n) (B.sigma n) := by
  rw [← B.rho_compat n, ← B.sigma_compat n]
  exact B.one_step_isometry n

/-- The limit Bures/Wasserstein cost reads back exactly to the chosen finite stage. -/
theorem bures_cost_limit_reads_stage (n : ℕ) :
    B.BWInf.squaredDist (B.toLimitState n (B.rho n)) (B.toLimitState n (B.sigma n)) =
      (B.BW n).squaredDist (B.rho n) (B.sigma n) :=
  B.limit_readout n

/-- Nonnegativity of the limit Bures/Wasserstein cost follows from the limit datum. -/
theorem bures_cost_limit_nonneg (n : ℕ) :
    0 ≤ B.BWInf.squaredDist (B.toLimitState n (B.rho n)) (B.toLimitState n (B.sigma n)) := by
  rw [B.bures_cost_limit_reads_stage n]
  exact (B.BW n).squaredDist_nonneg (B.rho n) (B.sigma n)

/-- If the tracked local pair agrees at stage `n`, then the limit cost vanishes on that readout. -/
theorem bures_cost_limit_eq_zero_of_stage_eq
    (n : ℕ)
    (hEq : B.rho n = B.sigma n) :
    B.BWInf.squaredDist (B.toLimitState n (B.rho n)) (B.toLimitState n (B.sigma n)) = 0 := by
  rw [B.bures_cost_limit_reads_stage n, hEq]
  exact (B.BW n).squaredDist_self (B.sigma n)

end BuresMetricStabilizationBridge

end BuresMetricStabilization
