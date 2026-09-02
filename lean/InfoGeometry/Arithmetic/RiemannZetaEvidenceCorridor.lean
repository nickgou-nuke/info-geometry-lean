import Mathlib
import InfoGeometry.Arithmetic.PhysicsRiemannHypothesisFinite
import InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleFormulas
import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge
import InfoGeometry.Arithmetic.LatticeHilbertPolyaPipeline
import InfoGeometry.Spectral.RiemannWeilTrace

/-!
# Riemann zeta theorem/evidence corridor

This module assembles the repository-owned theorem surface behind the chain

`primes → Euler product → zeta → analytic continuation → functional equation
 → critical strip → critical line → finite spectral operator → zeros/trace`.

The module deliberately stops before the conjectural arrows.  It does **not**
assert:

* a self-adjoint Hilbert--Pólya operator whose spectrum is exactly the complete
  set of nontrivial zeta-zero ordinates;
* the Riemann--Weil explicit formula as a closed native theorem;
* Montgomery--Odlyzko/GUE asymptotics as a theorem;
* the Riemann Hypothesis.

Those statements are recorded by the companion Logos ledger as open debt or
external/numerical evidence rather than being laundered through structural
packages.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannZetaEvidenceCorridor

open Complex

/-! ## Arithmetic entrance: primes and Euler product -/

/-- A concrete prime-data witness used at the finite entrance of the corridor. -/
theorem finite_prime_entrance :
    ((Finset.Icc 1 30).filter Nat.Prime).card = 10 :=
  InfoGeometry.Arithmetic.PhysicsRiemannHypothesisFinite.prime_count_le_thirty

/-- The genuine infinite prime Euler product equals Mathlib's Riemann zeta
function on the half-plane of absolute convergence. -/
theorem primeEulerProduct_eq_zeta
    {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) = riemannZeta s :=
  InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleFormulas.primeEulerProduct_eq_riemannZeta hs

/-- The Dirichlet-series presentation agrees with the same zeta function on
`Re(s) > 1`. -/
theorem dirichletSeries_eq_zeta
    (s : ℂ) (hs : 1 < s.re) :
    InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta s =
      riemannZeta s :=
  InfoGeometry.Arithmetic.RiemannZetaEquivalences.dirichletSeriesZeta_eq_riemannZeta s hs

/-! ## Analytic continuation and functional symmetry -/

/-- Mathlib's `riemannZeta` is complex differentiable at every point except its
single pole at `1`.  Together with `dirichletSeries_eq_zeta`, this is the
repository-facing analytic-continuation bridge from the original Dirichlet
series to the global meromorphic zeta function. -/
theorem riemannZeta_differentiable_off_one
    {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

/-- Functional equation for the completed zeta readout. -/
theorem completed_zeta_functional_equation (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta (1 - s) :=
  InfoGeometry.Arithmetic.RiemannZetaEquivalences.completedXiFunctionalEquation s

/-! ## Critical strip and critical line -/

/-- Reflection preserves the open critical strip. -/
theorem critical_strip_reflection (s : ℂ) :
    InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.inCriticalStrip (1 - s) ↔
      InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.inCriticalStrip s :=
  InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.inCriticalStrip_one_sub s

/-- The critical line is the fixed locus of `s ↦ 1 - star s`. -/
theorem critical_line_fixed_locus (s : ℂ) :
    1 - star s = s ↔
      InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.onCriticalLine s :=
  InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.onCriticalLine_iff_one_sub_star s

/-- For the actual completed Xi representative, zeros of the real critical-line
readout are exactly zeros of Xi at `1/2 + i t`.  This is a critical-line zero
correspondence, not a theorem that every nontrivial zero lies there. -/
theorem actualXi_criticalLine_zero_iff (t : ℝ) :
    InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.criticalLineRealReadout
        InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi t = 0 ↔
      InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi
        (1 / 2 + Complex.I * t) = 0 :=
  InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.criticalLineRealReadout_zero_iff_xi_zero
    InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi
    InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.actualRiemannXiFunctionDatum
    t

/-! ## Finite Hilbert--Pólya-shaped spectral edge -/

/-- On the repository's finite Hestenes--Krein prime lattice, the zeta-twisted
Dirac operator is self-adjoint on the critical line, under the explicit finite
packet hypotheses.  This is a finite conditional spectral theorem and not an
exact Hilbert--Pólya realization of all zeta zeros. -/
theorem finiteCriticalLine_selfAdjoint
    {P : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff}
    (L : InfoGeometry.Arithmetic.LatticeHilbertPolyaPipeline.FiniteHestenesKreinLattice P)
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : L.packet.holonomy s =
      InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2) :
    InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.FiniteCantorZetaDirac.IsAdjointPair
      (P := P) (L.packet.D s) (L.packet.D s) :=
  L.D_selfAdjoint_of_zetaCriticalLine hP s hs

/-! ## Trace-formula-shaped finite structure -/

/-- Native finite Riemann--Weil trace shadow: positive prime-orbit weight,
unitary prime phase, multiplicativity in repetition number, and even spectral
mode.  It does not identify this packet with the full Weil explicit formula. -/
theorem finite_riemann_weil_trace_packet
    (p : ℕ) (m m₁ m₂ : ℕ) (γ τ : ℝ)
    (hp : 2 ≤ p) (hm : 1 ≤ m) :
    (0 < InfoGeometry.Spectral.RiemannWeilTrace.primeOrbitWeight p m) ∧
    (‖InfoGeometry.Spectral.RiemannWeilTrace.primePhaseHolonomy p m γ‖ = 1) ∧
    (InfoGeometry.Spectral.RiemannWeilTrace.primePhaseHolonomy p (m₁ + m₂) γ =
      InfoGeometry.Spectral.RiemannWeilTrace.primePhaseHolonomy p m₁ γ *
        InfoGeometry.Spectral.RiemannWeilTrace.primePhaseHolonomy p m₂ γ) ∧
    (InfoGeometry.Spectral.RiemannWeilTrace.monochromaticSpectralMode (-γ) τ =
      InfoGeometry.Spectral.RiemannWeilTrace.monochromaticSpectralMode γ τ) :=
  InfoGeometry.Spectral.RiemannWeilTrace.grand_riemann_weil_trace_synthesis
    p m m₁ m₂ γ τ hp hm

/-- The theorem-owned portion of the requested chain in one dependency packet.
The later Hilbert--Pólya, explicit-formula, and GUE arrows are intentionally
not included because they are not theorem-owned at this level. -/
theorem theorem_owned_corridor_packet
    (s : ℂ) (hs : 1 < s.re) (t : ℝ) :
    DifferentiableAt ℂ riemannZeta s ∧
    completedRiemannZeta s = completedRiemannZeta (1 - s) ∧
    (InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.inCriticalStrip (1 - s) ↔
      InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.inCriticalStrip s) ∧
    (InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge.criticalLineRealReadout
        InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi t = 0 ↔
      InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi
        (1 / 2 + Complex.I * t) = 0) := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  exact ⟨riemannZeta_differentiable_off_one hs1,
    completed_zeta_functional_equation s,
    critical_strip_reflection s,
    actualXi_criticalLine_zero_iff t⟩

end InfoGeometry.Arithmetic.RiemannZetaEvidenceCorridor

end noncomputable section
