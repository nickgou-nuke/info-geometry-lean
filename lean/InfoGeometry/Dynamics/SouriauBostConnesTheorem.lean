import InfoGeometry.Quantum.FibonacciFusionCategory
import InfoGeometry.Canonical.CayleyBregmanBridge
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Canonical.BostConnesKMS
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Conditional zeta-limit and Fibonacci readouts

This module packages an explicit real-zeta limit proposition together with
finite algebraic identities supplied by the Fibonacci owners.  No analytic
convergence theorem or phase-transition identification is asserted here.
-/

set_option linter.unusedVariables false

open scoped Topology
open Filter Real

noncomputable section

namespace InfoGeometry.Dynamics.SouriauBostConnesTheorem

open FibonacciFusion
open InfoGeometry.Canonical
open InfoGeometry.Canonical.BostConnesKMS

/-! ### Partition function and order parameter -/

/-- Real part of the complex zeta readout along the real axis. -/
noncomputable def primonGasPartition (beta : ℝ) : ℝ :=
  (riemannZeta (beta : ℂ)).re

/-- The Fibonacci scalar `phi` exported by the fusion owner. -/
noncomputable def quantumDimension : ℝ := phi

/-- Diagonal matrix of the two supplied Fibonacci phase scalars. -/
noncomputable def fibonacciRMatrixPhases : Matrix (Fin 2) (Fin 2) ℂ :=
  !![R1_phase, 0;
     0, Rtau_phase]

/-! ### Explicit premise for the analytic limit -/

/-- The limit proposition supplied to the conditional transition theorem. -/
def zeroTemperatureZetaLimit : Prop :=
  Filter.Tendsto primonGasPartition Filter.atTop (nhds (1 : ℝ))

/-! ### Supporting lemmas from existing owners -/

/-- The imported Cayley-coordinate limit. -/
theorem cayley_boundary_limit :
    Filter.Tendsto Cayley.thermalCayley Filter.atTop (𝓝 1) :=
  Cayley.thermalCayley_tendsto_atTop_one

/-- Algebraic identities supplied by the Yang–Baxter owner. -/
theorem yang_baxter_parameters :
    YangBaxterProof.q ^ 5 = -1 ∧ YangBaxterProof.τ ^ 2 + YangBaxterProof.τ = 1 :=
  ⟨YangBaxterProof.q_pow_five, YangBaxterProof.tau_sq_add_tau⟩

/-- Algebraic identities supplied by the Fibonacci fusion owner. -/
theorem golden_ratio_identities :
    0 < phi ∧ 1 < phi ∧ 0 < phiInv ∧ phi ^ 2 = phi + 1 ∧ phiInv ^ 2 + phiInv = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact phi_pos
  · exact phi_gt_one
  · exact phiInv_pos
  · exact phi_sq
  · exact phiInv_sq_add_phiInv

/-- Norm and product identities for the supplied phase scalars. -/
theorem rmatrix_unitarity :
    ‖R1_phase‖ = 1 ∧ ‖Rtau_phase‖ = 1 ∧
    R1_phase * Rtau_phase = Complex.exp (Complex.I * (2 * Real.pi / 5)) := by
  rcases R_phases_unitary with ⟨hR1, hRτ⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hR1
  · exact hRτ
  · exact R_product

/-- The local scalar definition of the quantum dimension. -/
theorem quantum_dimension_tau_eq_phi : quantumDimension = phi := rfl

/-! ### The Capstone Theorem -/

/-- Conditional conjunction of the supplied zeta limit and a Fibonacci scalar
identity. -/
theorem souriau_bost_connes_transition :
    zeroTemperatureZetaLimit →
    Filter.Tendsto primonGasPartition Filter.atTop (nhds (1 : ℝ)) ∧
    quantumDimension = (1 + Real.sqrt 5) / 2 := by
  intro hZeta
  constructor
  · exact hZeta
  · -- φ = (1 + √5)/2 by definition of phi
    unfold quantumDimension
    unfold phi
    rfl

/-! ### Owner-backed transition property -/

/-- Closed algebraic content of the bulk-to-boundary transition packet. -/
def TransitionDictionary : Prop :=
  quantumDimension = phi ∧
    ‖R1_phase‖ = 1 ∧
    ‖Rtau_phase‖ = 1 ∧
    R1_phase * Rtau_phase = Complex.exp (Complex.I * (2 * Real.pi / 5))

/-- The transition property is assembled from the existing Fibonacci owners. -/
theorem transition_dictionary_nonempty : Nonempty TransitionDictionary := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact quantum_dimension_tau_eq_phi
  · exact R_phases_unitary.1
  · exact R_phases_unitary.2
  · exact R_product

end InfoGeometry.Dynamics.SouriauBostConnesTheorem
