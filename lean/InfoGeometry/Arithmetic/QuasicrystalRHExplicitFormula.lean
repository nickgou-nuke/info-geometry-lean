import Mathlib.Algebra.IsPrimePow
import InfoGeometry.Arithmetic.PrimitiveSetsAbove
import InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex
import InfoGeometry.Arithmetic.ZetaPrimeFluctuationBridge

/-!
# Repo-backed primon/quasicrystal/RH synthesis packet

This module is deliberately repo-first: it does not start from external slogans.
It stitches together the compiled theorem surfaces already present in the
codebase for:

* von-Mangoldt/prime-power arithmetic support;
* centered zeta-zero normal/tangent projection algebra;
* critical-line square-root wave envelopes;
* finite primon boson/signed-fermion cancellation;
* finite free-energy minimization from the Gibbs/KMS packet;
* finite Dyson/Vandermonde logarithmic repulsion.

The global analytic claim “all zeta zeros are saddles of a free-energy
quasicrystal potential” is represented only through already-existing packet
hypotheses when such hypotheses are supplied.  The closed content below is
exactly the repo-backed Lean content imported above.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.QuasicrystalRHExplicitFormula

open scoped BigOperators
open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.ZetaPrimeFluctuationBridge
open InfoGeometry.Arithmetic.ZetaPrimeFluctuationBridge.CenteredZeroReadout

/-- A finite/logarithmic Dirac atom index on the arithmetic side of an explicit
formula: the atom is supported at a prime power. -/
def PrimePowerAtom (n : ℕ) : Prop :=
  IsPrimePow n

/-- The real von-Mangoldt weight imported from the primitive-set owner surface. -/
abbrev lambdaR (n : ℕ) : ℝ :=
  realVonMangoldt n

/-- Exact support theorem: the arithmetic explicit-formula atoms carried by
`Λ(n)` are precisely prime powers. -/
theorem lambdaR_ne_zero_iff_primePowerAtom (n : ℕ) :
    lambdaR n ≠ 0 ↔ PrimePowerAtom n := by
  simpa [lambdaR, PrimePowerAtom] using realVonMangoldt_ne_zero_iff n

/-- Zero form of the same support theorem. -/
theorem lambdaR_eq_zero_iff_not_primePowerAtom (n : ℕ) :
    lambdaR n = 0 ↔ ¬ PrimePowerAtom n := by
  simpa [lambdaR, PrimePowerAtom] using realVonMangoldt_eq_zero_iff n

/-- Prime readback: a prime contributes a logarithmic atom with weight `log p`. -/
theorem lambdaR_apply_prime {p : ℕ} (hp : p.Prime) :
    lambdaR p = Real.log p := by
  simpa [lambdaR] using realVonMangoldt_apply_prime hp

/-- Prime-power readback: the von-Mangoldt weight is constant along positive
powers of a fixed base. -/
theorem lambdaR_apply_pow (n k : ℕ) (hk : k ≠ 0) :
    lambdaR (n ^ k) = lambdaR n := by
  simpa [lambdaR] using realVonMangoldt_apply_pow n k hk

/-- Divisor-sum readback: the finite logarithmic derivative identity behind the
Euler-product side of the explicit formula. -/
theorem sum_lambdaR_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, lambdaR d = Real.log (n : ℝ) := by
  simpa [lambdaR] using sum_realVonMangoldt_divisors n

/-- Repo-backed centered-zero statement: a supplied zero readout on the critical
line has vanishing normal projection. -/
theorem critical_zero_normalProjection_vanishes
    (z : CenteredZeroReadout) (hz : z.OnCriticalLine) :
    z.normalProjection = InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart.zero :=
  CenteredZeroReadout.normalProjection_eq_zero_of_critical z hz

/-- Repo-backed wave-envelope statement: on the critical line the scale-normal
envelope is removed and the wave is `sqrt` baseline times pure phase. -/
theorem critical_wave_squareRootEnvelope
    (W : PrimeWaveEnvelope) (hcrit : W.zero.OnCriticalLine) (N : ℕ) :
    W.fullWave N = ((W.baselineEnvelope N : ℝ) : ℂ) * W.oscillatoryPhase N :=
  PrimeWaveEnvelope.fullWave_eq_baseline_mul_phase_of_critical W hcrit N

/-- Repo-backed explicit-formula packet readout: when the packet supplies the
analytic explicit formula and critical-zero condition, normal projections vanish
for every supplied zero. -/
theorem packet_normalProjection_vanishes
    (P : ExplicitFormulaStabilityPacket) (ρ : P.zeros) :
    (P.zeroReadout ρ).normalProjection = InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart.zero :=
  P.normalProjection_vanishes ρ

/-- Repo-backed packet readout: the square-root prime-counting envelope law is
re-exported from a supplied explicit-formula stability packet. -/
theorem packet_squareRootEnvelope_holds
    (P : ExplicitFormulaStabilityPacket) :
    InfoGeometry.Arithmetic.PrimeDistributionLaw.RHPrimeCountingErrorLaw :=
  P.squareRootEnvelope_holds

/-- Finite primon boson/signed-fermion Euler cancellation, routed through the
compiled fact index. -/
theorem finite_boson_signed_closure
    {ι R : Type*} [Field R]
    (S : Finset ι) (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    InfoGeometry.Arithmetic.PrimeBosonFermionGas.bosonPartition S x *
        InfoGeometry.Arithmetic.PrimeBosonFermionGas.signedFermionPartition S x = 1 :=
  InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex.boson_signed_closure S x h

/-- Finite free-energy minimization: nonnegative relative entropy implies the
Gibbs state minimizes free energy. -/
theorem gibbs_kms_free_energy_minimizer
    (gk : InfoGeometry.Probability.Homological.GibbsKMSPacket)
    (ρ : gk.ObservableAlgebra)
    (hrel : 0 ≤ gk.relativeEntropyToGibbs ρ)
    (hβ : 0 < gk.beta) :
    gk.freeEnergy gk.gibbsState ≤ gk.freeEnergy ρ :=
  InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex.gibbs_kms_free_energy_minimizer gk ρ hrel hβ

/-- Finite Dyson/Vandermonde logarithmic repulsion bridge: for noncolliding
finite nodes, the β=2 Dyson Hamiltonian is the external potential minus the
logarithm of the squared Vandermonde separation product. -/
theorem finite_dyson_vandermonde_potential
    {N : ℕ} (lam : Fin N → ℝ) (V : ℝ → ℝ)
    (hsep : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, lam j ≠ lam i) :
    InfoGeometry.Canonical.PrimonCoulombGas.dyson_hamiltonian lam V =
      InfoGeometry.Canonical.PrimonCoulombGas.external_potential_energy lam V -
        Real.log ((InfoGeometry.Canonical.PrimonCoulombGas.vandermonde_product_abs lam) ^ 2) :=
  InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex.finite_dyson_vandermonde_potential lam V hsep

/-- Finite Vandermonde noncollision theorem. -/
theorem finite_vandermonde_nonzero_iff_injective
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (W : InfoGeometry.Canonical.VandermondeExclusionBridge.FiniteVandermondeExclusionWitness
      (R := R) (n := n)) :
    W.determinant ≠ 0 ↔ Function.Injective W.nodes :=
  InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex.finite_vandermonde_nonzero_iff_injective W

/-- Finite node collision is exactly the zero locus of the Vandermonde determinant. -/
theorem finite_vandermonde_zero_iff_collision
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (W : InfoGeometry.Canonical.VandermondeExclusionBridge.FiniteVandermondeExclusionWitness
      (R := R) (n := n)) :
    W.determinant = 0 ↔ ∃ i j : Fin n, W.nodes i = W.nodes j ∧ i ≠ j :=
  InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex.finite_vandermonde_zero_iff_collision W

/-- A small closed readback saying that this module is grounded in repo theorem
surfaces rather than external prose: the unit has zero von-Mangoldt weight while
all prime powers are exactly the nonzero support. -/
theorem repo_compiled_primon_crystal_surface_nonempty :
    lambdaR 1 = 0 ∧ (∀ n : ℕ, lambdaR n ≠ 0 ↔ PrimePowerAtom n) := by
  constructor
  · simpa [lambdaR] using realVonMangoldt_one
  · intro n
    exact lambdaR_ne_zero_iff_primePowerAtom n

end InfoGeometry.Arithmetic.QuasicrystalRHExplicitFormula
