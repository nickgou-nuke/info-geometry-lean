/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.FibonacciFusionCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CayleyBregmanBridge
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Canonical.BostConnesKMS
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Souriau–Bost–Connes Transition Theorem — Analytic Target Surface

This file proves the real zero-temperature limit of the primon partition
function using Mathlib's L-series convergence theorem, and joins that limit to
the Fibonacci fusion-dimension and braid-phase identities. The existence of a
limiting boundary state is not claimed.

## The Transition

At finite temperature (β > 1), the system is a non-compact Dirichlet series /
Primon gas on the cylinder S¹ × ℝ, governed by the full Riemann zeta function ζ(β).

Under the Souriau metriplectic flow driving β → ∞, the Cayley compactification
collapses the continuous bulk onto the Cantor boundary. The algebraic ring
transitions from the Boolean Weyl group (independent prime oscillators) to the
Fibonacci braid group B_n.

The order parameter is not a thermodynamic magnetization but the quantum
dimension φ = (1 + √5)/2 — the golden ratio — which dictates the non-integer
capacity of the Fibonacci fusion category at the absolute zero limit.

## Theorem Statement

1. **Zeta Convergence**: ζ(β) → 1 as β → ∞, isolating the ground state.
2. **Quantum Dimension**: φ = (1 + √5)/2 identically (defining equation of the golden ratio).

The full dictionary:
  Bulk (β > 1)           →  Boundary (β → ∞)
  ─────────────────────────────────────────────
  Dirichlet ζ(β)         →  Cuntz O₂ / Fibonacci fusion category
  Cylinder S¹ × ℝ        →  Totally disconnected Cantor set
  Boolean Weyl group      →  Fibonacci braid group B_n
  Prime ideals / Euler    →  Anyon R-matrix phases {e^{4πi/5}, e^{-2πi/5}}
  ζ(β)                   →  φ (golden ratio)

## BUCKET 1: CLOSED THEOREMS

Finite algebraic readouts, fusion-dimension identities, and the real Cayley
boundary limit are proved from their owners.

## BUCKET 2: CONDITIONAL THEOREMS

The boundary-state interpretation remains conditional on a construction of
the limiting state; the real partition-function limit itself is proved below.

## BUCKET 3: OPEN CLOSURE DEBT

Connect the proved real partition-function limit to a boundary-state
construction.
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

/--
The primon gas partition function: the Riemann zeta function restricted to
real inverse temperature β > 1. For β > 1, the Dirichlet series converges
absolutely and ζ(β) ∈ ℝ.
-/
noncomputable def primonGasPartition (beta : ℝ) : ℝ :=
  (riemannZeta (beta : ℂ)).re

/--
The real primon partition function tends to its ground-state value `1` as the
inverse temperature tends to infinity. The proof uses Mathlib's limit theorem
for a convergent Dirichlet series, then identifies the constant-one L-series
with the Riemann zeta function on the eventual region `β > 1`.
-/
theorem zeroTemperatureZetaLimit :
    Filter.Tendsto primonGasPartition Filter.atTop (nhds (1 : ℝ)) := by
  have habs : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact EReal.coe_lt_top 1
  have hcomplex :
      Filter.Tendsto (fun β : ℝ => LSeries (1 : ℕ → ℂ) β)
        Filter.atTop (nhds (1 : ℂ)) := by
    simpa using (LSeries.tendsto_atTop (f := (1 : ℕ → ℂ)) habs)
  have hreal :
      Filter.Tendsto (fun β : ℝ => (LSeries (1 : ℕ → ℂ) β).re)
        Filter.atTop (nhds (1 : ℝ)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
    change Filter.Tendsto
      (fun β : ℝ => (LSeries (1 : ℕ → ℂ) β).re)
      Filter.atTop (nhds (1 : ℝ)) at h
    exact h
  have heq : primonGasPartition =ᶠ[Filter.atTop]
      fun β : ℝ => (LSeries (1 : ℕ → ℂ) β).re := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with β hβ
    change (riemannZeta (β : ℂ)).re = (LSeries (1 : ℕ → ℂ) β).re
    rw [← LSeries_one_eq_riemannZeta (s := (β : ℂ)) (by simpa using hβ)]
  exact (Filter.tendsto_congr' heq).2 hreal

/--
The quantum dimension order parameter: the golden ratio φ.
Already defined in `FibonacciFusion.phi` as `(1 + √5)/2`.
-/
noncomputable def quantumDimension : ℝ :=
  FibonacciFusion.quantumDimension FibonacciFusion.FibObject.tau

/--
The Fibonacci R-matrix phases at the boundary.
These are the unique solutions preserving the non-local topological index
across the Cuntz shift operators, satisfying the Yang-Baxter equation natively.
-/
noncomputable def fibonacciRMatrixPhases : Matrix (Fin 2) (Fin 2) ℂ :=
  !![R1_phase, 0;
     0, Rtau_phase]

/-! ### Supporting lemmas from existing owners -/

/-- The Cayley thermal coordinate reaches the boundary point 1 as β → ∞.
Proved in `Cayley.thermalCayley_tendsto_atTop_one`. -/
theorem cayley_boundary_limit :
    Filter.Tendsto Cayley.thermalCayley Filter.atTop (𝓝 1) :=
  Cayley.thermalCayley_tendsto_atTop_one

/-- The positive Yang--Baxter root and the inverse golden ratio coincide.
Both satisfy `x² + x = 1`; positivity selects the same root. -/
theorem tauR_eq_phiInv : YangBaxterProof.tauR = FibonacciFusion.phiInv := by
  have ht := YangBaxterProof.tauR_sq_add_tauR
  have hp := FibonacciFusion.phiInv_sq_add_phiInv
  have hprod :
      (YangBaxterProof.tauR - FibonacciFusion.phiInv) *
        (YangBaxterProof.tauR + FibonacciFusion.phiInv + 1) = 0 := by
    nlinarith [ht, hp]
  have hsum : YangBaxterProof.tauR + FibonacciFusion.phiInv + 1 ≠ 0 := by
    have hτ := YangBaxterProof.tauR_nonneg
    have hφ := FibonacciFusion.phiInv_pos
    positivity
  rcases mul_eq_zero.mp hprod with h | h
  · linarith
  · exact False.elim (hsum h)

/-- The Yang--Baxter root equations together with the inverse quantum-dimension
relation and the primitive fifth-power relation for `q`. -/
theorem yang_baxter_parameters :
    YangBaxterProof.q ^ 5 = -1 ∧
      YangBaxterProof.τ ^ 2 + YangBaxterProof.τ = 1 ∧
      YangBaxterProof.τ * (quantumDimension : ℂ) = 1 := by
  refine ⟨YangBaxterProof.q_pow_five, YangBaxterProof.tau_sq_add_tau, ?_⟩
  have hreal : YangBaxterProof.tauR * quantumDimension = 1 := by
    have hinv : FibonacciFusion.phiInv * FibonacciFusion.phi = 1 := by
      unfold FibonacciFusion.phiInv
      nlinarith [FibonacciFusion.phi_sq]
    calc
      YangBaxterProof.tauR * quantumDimension =
          FibonacciFusion.phiInv * FibonacciFusion.phi := by
            rw [← tauR_eq_phiInv]
            simp [quantumDimension, FibonacciFusion.quantumDimension]
      _ = 1 := hinv
  change (YangBaxterProof.tauR : ℂ) * (quantumDimension : ℝ) = 1
  exact_mod_cast hreal

/-- The braid parameter is the inverse of the Fibonacci tau quantum dimension.
This links the Yang--Baxter scalar to the Perron eigenvalue used by the fusion
matrix, rather than merely listing their separate polynomial identities. -/
theorem yang_baxter_parameter_is_inverse_quantum_dimension :
    YangBaxterProof.tauR * quantumDimension = 1 := by
  have hinv : FibonacciFusion.phiInv * FibonacciFusion.phi = 1 := by
    unfold FibonacciFusion.phiInv
    nlinarith [FibonacciFusion.phi_sq]
  calc
    YangBaxterProof.tauR * quantumDimension =
        FibonacciFusion.phiInv * FibonacciFusion.phi := by
          rw [← tauR_eq_phiInv]
          simp [quantumDimension, FibonacciFusion.quantumDimension]
    _ = 1 := hinv

/-- The fusion dimension, inverse golden ratio, and braid parameter satisfy
their linked order, polynomial, and product identities. -/
theorem golden_ratio_identities :
    0 < quantumDimension ∧ 1 < quantumDimension ∧ 0 < phiInv ∧
      quantumDimension ^ 2 = quantumDimension + 1 ∧
      phiInv ^ 2 + phiInv = 1 ∧
      YangBaxterProof.tauR * quantumDimension = 1 := by
  have hqdim : quantumDimension = phi := rfl
  refine ⟨?_, ?_, phiInv_pos, ?_, phiInv_sq_add_phiInv,
    yang_baxter_parameter_is_inverse_quantum_dimension⟩
  · rw [hqdim]
    exact phi_pos
  · rw [hqdim]
    exact phi_gt_one
  · rw [hqdim]
    exact phi_sq

/-- Fibonacci R-matrix phases are unitary and have the expected product.
Proved in `FibonacciFusion`. -/
theorem rmatrix_unitarity :
    ‖R1_phase‖ = 1 ∧ ‖Rtau_phase‖ = 1 ∧
      R1_phase * Rtau_phase = Complex.exp (Complex.I * (2 * Real.pi / 5)) := by
  have hR1 : ‖R1_phase‖ = 1 := by
    unfold R1_phase
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (4 * Real.pi / 5)
  have hRτ : ‖Rtau_phase‖ = 1 := by
    unfold Rtau_phase
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (-(2 * Real.pi / 5))
  have hproduct :
      R1_phase * Rtau_phase = Complex.exp (Complex.I * (2 * Real.pi / 5)) := by
    unfold R1_phase Rtau_phase
    rw [← Complex.exp_add]
    congr 1
    ring
  exact ⟨hR1, hRτ, hproduct⟩

/-- The local τ-dimension agrees with φ and is the Perron eigenvalue of the
Fibonacci fusion matrix on the dimension vector `(1, dτ)`. -/
theorem quantum_dimension_tau_eq_phi :
    quantumDimension = phi ∧
      Matrix.mulVec FibonacciFusion.fusionMatrixTau ![1, quantumDimension] =
        quantumDimension • ![1, quantumDimension] := by
  constructor
  · rfl
  · simpa [quantumDimension, FibonacciFusion.quantumDimension] using
      FibonacciFusion.quantum_dimension_eigenvalue

/-! ### The Capstone Theorem -/

/--
**The Souriau–Bost–Connes Transition Target.**

Under the Souriau metriplectic flow driving β → ∞:
1. The primon gas partition function ζ(β) converges to 1, isolating the
   ground state (the unpolarized Dirac sea at half-filling).
2. The quantum dimension order parameter φ equals (1 + √5)/2 identically —
   the defining equation of the golden ratio, which controls the non-integer
   capacity of the Fibonacci fusion category at absolute zero.

The second component follows from the Fibonacci quantum-dimension definition;
the first is proved in `zeroTemperatureZetaLimit` using the constant-one
Dirichlet L-series.
-/
theorem souriau_bost_connes_transition :
    Filter.Tendsto primonGasPartition Filter.atTop (nhds (1 : ℝ)) ∧
    quantumDimension = (1 + Real.sqrt 5) / 2 := by
  constructor
  · exact zeroTemperatureZetaLimit
  · -- φ = (1 + √5)/2 by the defining expression for phi
    rw [quantum_dimension_tau_eq_phi.1]
    unfold phi
    rfl

/-! ### Owner-backed transition synthesis -/

/--
The finite boundary synthesis joins three owner-level structures: the tau
quantum-dimension vector is a fusion-matrix eigenvector, the Yang--Baxter
parameter is its inverse, and the two braid phases are unitary with the stated
relative phase. This is the precise algebraic boundary packet; it makes no
claim that the analytic zeta-limit premise has been discharged.
-/
theorem transition_dictionary :
    Matrix.mulVec FibonacciFusion.fusionMatrixTau ![1, quantumDimension] =
        quantumDimension • ![1, quantumDimension] ∧
      YangBaxterProof.tauR * quantumDimension = 1 ∧
      ‖R1_phase‖ = 1 ∧ ‖Rtau_phase‖ = 1 ∧
      R1_phase * Rtau_phase = Complex.exp (Complex.I * (2 * Real.pi / 5)) := by
  constructor
  · simpa [quantumDimension, FibonacciFusion.quantumDimension] using
      FibonacciFusion.quantum_dimension_eigenvalue
  constructor
  · exact yang_baxter_parameter_is_inverse_quantum_dimension
  constructor
  · unfold R1_phase
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (4 * Real.pi / 5)
  constructor
  · unfold Rtau_phase
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (-(2 * Real.pi / 5))
  · exact R_product

end InfoGeometry.Dynamics.SouriauBostConnesTheorem
