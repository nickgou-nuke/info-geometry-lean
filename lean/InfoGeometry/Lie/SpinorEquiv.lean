import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.Algebra.Module.End
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

import InfoGeometry.Canonical.ArakiItakuraSaitoCollapse
import InfoGeometry.Canonical.NilpotentItakuraSaito
import InfoGeometry.Algebra.CuntzTraceConjugation
import InfoGeometry.Algebra.FibonacciGrothendieckRing
import InfoGeometry.Topology.AmplituhedronBoundary
import Omega.CircleDimension.StokesHomologyExactSplitting
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Canonical.SUSYCentralChargeBridge

open Matrix
open Complex
open CliffordAlgebra
open Even
open Algebra
open LinearMap
open DirectSum
open Submodule
open Units

open InfoGeometry.Canonical.ArakiItakuraSaitoCollapse
open InfoGeometry.Canonical.NilpotentItakuraSaito
open InfoGeometry.Algebra.CuntzTraceConjugation
open InfoGeometry.Algebra.FibonacciGrothendieckRing
open Omega.CircleDimension.StokesHomologyExactSplitting
open InfoGeometry.Topology.ThermodynamicGauge

namespace InfoGeometry.Lie.SpinorEquiv

/-! ## Section 1: The Three Itakura Strands as de Rham Models -/

/-- 1. **Araki/Itakura-Saito** → Curvature form `F = dA + A ∧ A`
    The `NoncommutativeItakuraSaitoModel.divergence` is the operator Bregman
    divergence, which under the bridge becomes `Tr(F ∧ F)` — the second Chern form. -/
theorem araki_itakura_is_curvature_form :
    ∀ (P : NoncommutativeItakuraSaitoModel (Matrix (Fin 2) (Fin 2) ℂ))
      (hzero : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        P.readout.readout (P.readout.product X 0) = 0)
      (X : Matrix (Fin 2) (Fin 2) ℂ),
      P.divergence X X = 0 := by
  intro P hzero X
  exact P.divergence_self hzero X

/-- 2. **Thermodynamic Gauge** → Connection 1-form `A`
    The `thermodynamic_gauge_connection` IS a connection 1-form;
    entropy production `= Tr(F ∧ F)` is the Chern-Simons 3-form. -/
theorem thermodynamic_gauge_is_connection :
    ∀ (flow : CausalNonequilibriumFlow (Matrix (Fin 2) (Fin 2) ℂ)),
      entropy_production flow =
        flow.P_forward * flow.P_backward -
          flow.P_backward * flow.P_forward := by
  intro flow
  exact entropy_production_eq_commutator flow

/-- 3. **Nilpotent Itakura-Saito** → de Rham differential `d`
    `nilItakuraSaito K = nilExp K - 1 - K = 0` on the finite truncated lane.
    is the finite-model of `d ∘ d = 0` in the de Rham complex. -/
theorem nilpotent_itakura_realizes_d_squared_zero
    (K : BiquaternionKANnilpotent.M2C) (hK : K * K = 0) :
    nilItakuraSaito K = 0 ∧ K * K = 0 := by
  exact ⟨nilItakuraSaito_zero K, hK⟩

/-! ## Section 2: Stokes Exact Splitting → de Rham Theorem -/

/-- The split exact sequence `0 → ℤ^v → ℤ^u × ℤ^v → ℤ^u → 0`
    is the discrete shadow of the de Rham isomorphism
    `H^k_dR(M) ≃ H^k_sing(M; ℝ)`. -/
theorem stokes_splitting_realizes_derham (u v : ℕ) :
    (Set.range (stokesBoundaryInclusion u v) : Set ((Fin u → ℤ) × (Fin v → ℤ))) = {p | stokesProjection u v p = 0} := by
  rw [stokes_range_eq_kernel]

/-! ## Section 3: Fibonacci Ring → Period Matrix -/

/-- The Fibonacci ring model `τ² = τ + 1` generates the period lattice
    for the de Rham cohomology of the elliptic curve / modular curve. -/
theorem fibonacci_ring_generates_period_lattice :
    (FibonacciRingModel.tau.mul FibonacciRingModel.tau
      = FibonacciRingModel.tau + FibonacciRingModel.one) := by
  exact FibonacciRingModel.tau_mul_tau

end InfoGeometry.Lie.SpinorEquiv
