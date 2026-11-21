/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Dynamics.RapiditySpace
import InfoGeometry.Dynamics.RindlerWedge
import InfoGeometry.Canonical.RealTomitaCore
import InfoGeometry.Canonical.WedgeBoostModularBridge
import InfoGeometry.Thermodynamics.UnruhTemperature
import InfoGeometry.Canonical.BisognanoWichmannUnruhAQFT
import InfoGeometry.Canonical.TomitaCommutantHeatBathBridge

/-!
# Bisognano–Wichmann Souriau Unification Bridge

This module packages the finite, source-backed parts of the
Bisognano–Wichmann / Unruh / Souriau pipeline. It does not prove the analytic
Bisognano–Wichmann theorem or identify an arbitrary finite involution with a
QFT horizon commutant.

1. **Stage 1 (Cartan Boost Flow in 𝔭):**
   The hyperbolic boost flow $A(a \tau)$ parameterizes the worldline of a uniformly
   accelerating Rindler observer with proper acceleration $a > 0$, preserving the
   light-cone proper distance $x_+ x_- = r^2$.
2. **Stage 2 (Modular-to-Proper Time Identification):**
   The Tomita–Takesaki modular flow parameter $\tau_{\mathrm{mod}}$ is related to the
   proper boost rapidity $\theta = a \tau$ by $\theta = 2\pi \tau_{\mathrm{mod}}$.
3. **Stage 3 (KMS Thermal State & Unruh Temperature):**
   The unit modular KMS period $\Delta \tau_{\mathrm{mod}} = 1$ transforms under proper
   acceleration to the inverse thermal temperature $\beta = 2\pi / a$, yielding
   the exact Unruh temperature $T_U = a / (2\pi)$.
4. **Stage 4 (Finite Involution Trace Identity):**
   A matrix involution $J^2 = 1$ gives the finite trace identity
   $\mathrm{Tr}(J A J) = \mathrm{Tr}(A)$. An actual commutant statement requires
   `TomitaCommutantDatum` and is not supplied by this matrix hypothesis.

All proofs are native Lean 4/Mathlib proofs with complete proof terms and no custom axioms.
-/

noncomputable section

open Matrix
open InfoGeometry.Dynamics.RindlerWedge
open InfoGeometry.Canonical.RealTomitaCore
open InfoGeometry.Canonical.WedgeBoostModularBridge
open InfoGeometry.Thermodynamics.UnruhTemperature
open InfoGeometry.Canonical.TomitaCommutant

namespace InfoGeometry.Canonical.BisognanoWichmannUnification

/-!
=============================================================================
STAGE 1: Hyperbolic Boost Flow & Rindler Invariance
=============================================================================
-/

/-- 
  THEOREM 1.1: Hyperbolic boost flow translates Rindler proper time and preserves
  the squared proper distance on the light-cone.
-/
theorem rindler_boost_flow_invariance (coords : RindlerCoordinates) (a tau : ℝ) :
    let flowed := InfoGeometry.Dynamics.HyperbolicComponent.componentAReal (a * tau) *
      rindlerToMinkowski coords
    flowed 0 0 * flowed 1 0 = coords.radius ^ 2 := by
  intro flowed
  exact rindler_flow_preserves_proper_distance coords (a * tau)

/-!
=============================================================================
STAGE 2: Modular Time Identification
=============================================================================
-/

/--
  THEOREM 2.1: The modular-to-proper time identification correctly matches the
  wedge boost rapidity parameter $\theta = 2\pi \tau_{\mathrm{mod}}$.
-/
theorem modular_to_proper_rapidity_match (obs : RindlerObserver) (tau_mod : ℝ) :
    rapidity obs (properTime_of_modularTime obs tau_mod) = wedgeBoostParameter tau_mod := by
  exact rapidity_properTime_eq_wedgeBoostParameter obs tau_mod

/--
  THEOREM 2.2: The modular time mapping is strictly linear:
  $\tau_{\mathrm{mod}}(\theta_1 + \theta_2) = \tau_{\mathrm{mod}}(\theta_1) + \tau_{\mathrm{mod}}(\theta_2)$.
-/
theorem modular_time_add (theta1 theta2 : ℝ) :
    modularTimeOfWedgeBoost (theta1 + theta2) =
      modularTimeOfWedgeBoost theta1 + modularTimeOfWedgeBoost theta2 := by
  dsimp [modularTimeOfWedgeBoost]
  ring

/-!
=============================================================================
STAGE 3: KMS Thermal Periodicity & Exact Unruh Temperature
=============================================================================
-/

/--
  THEOREM 3.1: Under the repository's normalized modular-time convention
  $\Delta \tau_{\mathrm{mod}} = 1$, the proper-time scale is
  $\beta = 2\pi / a$. This is a finite parameter conversion, not an analytic KMS theorem.
-/
theorem kms_modular_period_to_inverse_temperature (obs : RindlerObserver) :
    inverseTemperature obs = (2 * Real.pi) / obs.a := by
  exact inverseTemperature_eq obs

/--
  THEOREM 3.2: Exact Unruh Temperature Theorem:
  The thermal temperature perceived by an accelerating observer is strictly $T_U = a / (2\pi)$.
-/
theorem unruh_temperature_value (obs : RindlerObserver) :
    unruhTemperature obs = obs.a / (2 * Real.pi) := by
  exact unruhTemperature_eq obs

/--
  THEOREM 3.3: Positivity of Unruh Radiation:
  For every physical observer with positive acceleration $a > 0$, the perceived temperature is strictly positive.
-/
theorem unruh_temperature_strictly_positive (obs : RindlerObserver) :
    0 < unruhTemperature obs := by
  exact unruhTemperature_pos obs

/-!
=============================================================================
STAGE 4: Finite Involution Trace Conservation
=============================================================================
-/

/--
  THEOREM 4.1: Conjugation by any involutive finite matrix preserves trace.
  This theorem has no commutant or horizon interpretation by itself.
-/
theorem involutive_conjugation_trace_invariance {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (J A : Matrix (Fin n) (Fin n) ℝ) (hJ : J * J = 1) :
    trace (J * A * J) = trace A := by
  rw [trace_mul_comm (J * A) J, ← mul_assoc, hJ, one_mul]

/-!
=============================================================================
STAGE 5: The Unified Bisognano–Wichmann – Souriau Synthesis Structure
=============================================================================
-/

/--
  A finite Unruh–Souriau packet:
  packages the acceleration parameter, normalized modular period, and resulting
  thermodynamic temperature. It is not an AQFT state or a commutant witness.
-/
structure FiniteUnruhSouriauPacket where
  obs : RindlerObserver
  beta_thermal : ℝ
  h_beta : beta_thermal = (2 * Real.pi) / obs.a
  temperature : ℝ
  h_temp : temperature = obs.a / (2 * Real.pi)
  h_temp_pos : 0 < temperature

/--
  Construct the finite Unruh–Souriau packet from an accelerating observer.
-/
def makeFiniteUnruhSouriauPacket (obs : RindlerObserver) : FiniteUnruhSouriauPacket where
  obs := obs
  beta_thermal := inverseTemperature obs
  h_beta := inverseTemperature_eq obs
  temperature := unruhTemperature obs
  h_temp := unruhTemperature_eq obs
  h_temp_pos := unruhTemperature_pos obs

/--
  FINITE SYNTHESIS THEOREM:
  The finite geometric and thermodynamic identities are jointly available:
  1. Boost flow preserves the lightcone proper radius $r^2$;
  2. Modular rapidity matches proper rapidity $\theta = 2\pi \tau_{\mathrm{mod}}$;
  3. The normalized modular convention gives $\beta = 2\pi / a$;
  4. The finite Unruh temperature is $a / (2\pi) > 0$;
  5. An involutive matrix conjugation preserves trace. No analytic AQFT theorem
     or horizon-commutant identification is asserted.
-/
theorem finite_bisognano_wichmann_souriau_packet
    (obs : RindlerObserver)
    (coords : RindlerCoordinates) (tau : ℝ)
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (J A : Matrix (Fin n) (Fin n) ℝ) (hJ : J * J = 1) :
    -- (1) Geometric lightcone invariance
    (let flowed := InfoGeometry.Dynamics.HyperbolicComponent.componentAReal (obs.a * tau) *
      rindlerToMinkowski coords;
     flowed 0 0 * flowed 1 0 = coords.radius ^ 2) ∧
    -- (2) Modular-to-proper rapidity match
    rapidity obs (properTime_of_modularTime obs 1) = wedgeBoostParameter 1 ∧
    -- (3) Exact inverse temperature
    inverseTemperature obs = (2 * Real.pi) / obs.a ∧
    -- (4) Exact Unruh temperature
    unruhTemperature obs = obs.a / (2 * Real.pi) ∧
    -- (5) Positivity of temperature
    0 < unruhTemperature obs ∧
    -- (6) Horizon reflection trace conservation
    trace (J * A * J) = trace A := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rindler_boost_flow_invariance coords obs.a tau
  · exact modular_to_proper_rapidity_match obs 1
  · exact kms_modular_period_to_inverse_temperature obs
  · exact unruh_temperature_value obs
  · exact unruh_temperature_strictly_positive obs
  · exact involutive_conjugation_trace_invariance J A hJ

end InfoGeometry.Canonical.BisognanoWichmannUnification
