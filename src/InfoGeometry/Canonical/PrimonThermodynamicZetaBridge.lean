import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Filtered
import InfoGeometry.Canonical.PrimonThermodynamicColimit
import InfoGeometry.Canonical.Determinant
import InfoGeometry.Canonical.ZetaRegularizedBoundaryReadout
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.PrimonZetaRegularization
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Arithmetic.PrimeBitMellinLaplaceBridge

/-!
# Primon Thermodynamic Zeta Channel Bridge

This module places the thermodynamic colimit and the zeta-regularized
determinant channel in one theorem-safe owner without identifying them.

The bridge has two channels:

## Channel 1: Thermodynamic (Real, Convex, Statistical)
- Finite partition functions `Z_n(s)` from `PrimonThermodynamicColimit`
- Gibbs states descended through the filtered colimit
- Massieu potential `log Z_n(s)` additive over prime modes
- Colimit expectation `⟨·⟩_β` descended through the filtered colimit

## Channel 2: Spectral/Analytic (Complex, Determinant)
- Fredholm determinants `det_n(I - e^{-s H_single}) = ∏_{k=1}^n (1 - p_k^{-s})`
- Finite bosonic determinant channel and its inverse Fredholm readout
- Zeta regularization as an explicitly supplied determinant calibration
- Completed Riemann zeta function `ξ(s)` via `CayleyCriticalLineCircleBridge`

## Theorem boundary
The finite Gibbs partition and the finite Fredholm determinant are separate
channels in this owner.  Their finite definitions are recorded, but no
thermodynamic-limit, analytic-continuation, or determinant-to-zeta equality is
asserted here.  A zeta-regularized determinant calibration is represented
only by explicit supplied data.

All formalized using the exact categorical colimit infrastructure — no
analytic continuation, no infinities as actualized numbers, only universal
properties of the inductive system.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimonThermodynamicZetaBridge

open InfoGeometry.Canonical.PrimonThermodynamicColimit
open InfoGeometry.Canonical.PrimonZetaRegularization
open InfoGeometry.Canonical.Determinant
open InfoGeometry.Canonical.ZetaRegularizedBoundaryReadout
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveLimitBoundary
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open CategoryTheory CategoryTheory.Limits

variable (primes : ℕ → ℕ)
variable (hprimes : ∀ n, Nat.Prime (primes n))
variable (β : ℝ)

/-- The finite thermodynamic partition is the fermionic Euler product. -/
theorem finitePartitionFunction_eq_fermionicEulerProduct (n : ℕ) :
    finitePartitionFunction primes β n =
      ∏ k ∈ Finset.range n, singlePrimeFactor primes β k := by
  exact finitePartitionFunction_eq_prod_singlePrimeFactor primes β n

/-- The finite Massieu potential reads the logarithm of the fermionic Euler
product.  The Fredholm/bosonic determinant channel is intentionally separate. -/
theorem finiteMassieu_eq_logFermionicEulerProduct (n : ℕ) :
    Real.log (finitePartitionFunction primes β n) =
      Real.log (∏ k ∈ Finset.range n, singlePrimeFactor primes β k) := by
  rw [finitePartitionFunction_eq_fermionicEulerProduct primes β n]

/-- The finite Fredholm determinant is the inverse of the finite bosonic
partition function. -/
theorem finiteFredholmDeterminant_inv_bosonicPartitionFunction (n : ℕ) (s : ℂ) :
    finiteFredholmDeterminant primes hprimes n s = (finiteBosonicPartitionFunction primes hprimes n s)⁻¹ := by
  simp [finiteBosonicPartitionFunction]

/-- The finite single-particle partition function is the trace of the single-particle
operator at stage n. -/
theorem singleParticlePartitionFunction_eq_trace (n : ℕ) (s : ℂ) :
    singleParticlePartitionFunction primes hprimes n s =
      (Finset.range n).sum fun k : ℕ =>
        Complex.exp (-s * (Real.log (primes k : ℝ) : ℂ)) := by rfl

/-- The finite multi-particle partition function at stage n is the sum over
all BitWords of the complex exponential of the logarithmic energy. -/
theorem multiParticlePartitionFunction_bitWord_sum (n : ℕ) (s : ℂ) :
    multiParticlePartitionFunction primes hprimes n s =
      (Finset.univ : Finset (BitWord n)).sum fun w =>
        if h : bitWordToNat primes w = 0 then 0 else
          Complex.exp (-s * (Real.log (bitWordToNat primes w : ℝ) : ℂ)) := by rfl

/-- The finite Gibbs state at zero inverse temperature equals the uniform
measure on BitWords. -/
theorem finiteGibbsState_zero_eq_uniform (n : ℕ) (w : BitWord n) :
    finiteGibbsState primes 0 n w = 1 / (2 ^ n : ℝ) := by
  have hweight : ∀ u : BitWord n,
      finiteBoltzmannWeight primes 0 n u = 1 := by
    intro u
    simp [finiteBoltzmannWeight, fermionOccupationWeight,
      fermionPrimeBoltzmannWeight]
  have hpartition : finitePartitionFunction primes 0 n = (2 ^ n : ℝ) := by
    simp [finitePartitionFunction, hweight]
  rw [finiteGibbsState, hweight w, hpartition]

/-- The colimit Gibbs expectation at zero inverse temperature equals the
normalized UHF stage trace. -/
theorem gibbsExpectationColimit_zero_eq_stageTrace
    (primes : ℕ → ℕ) (n : ℕ) (f : DiagAlg n) :
    gibbsExpectationColimit primes 0
        ((colimit.ι primonThermoModuleDiagram n).hom f) =
      stageTrace n f := by
  rw [gibbsExpectationColimit_on_stage, expectedValue_zero_eq_stageTrace]

/-- The Cayley transform relates the critical line to the unit circle. -/
theorem criticalLine_iff_unitCircle (s : ℂ) :
    OnCriticalLine s ↔ OnLeeYangCircle (cayleyToFugacity s) := by
  exact criticalLine_iff_cayley_unitCircle s

/-- The simplex (s, 1-s) encodes the quantum 2-level state. -/
structure SimplexSOneMinusS where
  s : ℂ
  oneMinusS : ℂ
  sum_eq_one : s + oneMinusS = 1

/-- Canonical homogeneous simplex point associated with `s`. -/
def simplexSOneMinusS (s : ℂ) : SimplexSOneMinusS :=
  ⟨s, 1 - s, by ring⟩

@[simp]
theorem simplexSOneMinusS_s (s : ℂ) :
    (simplexSOneMinusS s).s = s :=
  rfl

@[simp]
theorem simplexSOneMinusS_oneMinusS (s : ℂ) :
    (simplexSOneMinusS s).oneMinusS = 1 - s :=
  rfl

theorem simplexSOneMinusS_sum (s : ℂ) :
    (simplexSOneMinusS s).s +
        (simplexSOneMinusS s).oneMinusS = 1 := by
  exact (simplexSOneMinusS s).sum_eq_one

/-- The logit τ(s) = s/(1-s) gives the cayley fugacity. -/
def logit (s : ℂ) : ℂ :=
  s / (1 - s)

@[simp]
theorem logit_eq_cayleyToFugacity (s : ℂ) :
    logit s = cayleyToFugacity s :=
  rfl

theorem logit_one_sub_eq_inv (s : ℂ) :
    logit (1 - s) = (logit s)⁻¹ := by
  rw [logit_eq_cayleyToFugacity, logit_eq_cayleyToFugacity]
  exact cayleyToFugacity_one_sub_eq_inv s

theorem criticalLine_iff_logit_unitCircle (s : ℂ) :
    OnCriticalLine s ↔ OnLeeYangCircle (logit s) := by
  rw [logit_eq_cayleyToFugacity]
  exact criticalLine_iff_cayley_unitCircle s

/-- The surprisal W = ln τ gives the relative entropy coordinate. -/
def surprisal (s : ℂ) : ℂ :=
  Complex.log (logit s)

/-- The modular Hamiltonian is the surprisal operator: Ĥ = -ln ρ. -/
def modularHamiltonian (ρ : ℂ → ℂ) : ℂ → ℂ :=
  fun s => -Complex.log (ρ s)

/-- Twin thermal flows: ψ_left(y,t) = Φ(y)e^{-ity}, ψ_right(y,t) = Φ(y)e^{+ity}.
    At the center W=0 they meet: Ψ_total = 2Φ(y)cos(ty). -/
structure TwinThermalFlows where
  Φ : ℂ → ℂ
  leftFlow : ℂ → ℂ → ℂ := fun y t => Φ y * Complex.exp (-Complex.I * t * y)
  rightFlow : ℂ → ℂ → ℂ := fun y t => Φ y * Complex.exp (Complex.I * t * y)
  totalFlow : ℂ → ℂ → ℂ := fun y t => 2 * Φ y * Complex.cos (t * y)

/-- The spectral calibration readout is exactly the supplied calibration data.
    No equality with a thermodynamic colimit is asserted. -/
theorem completeBridgeTheorem
    (zetaTarget : ℂ → ℂ)
    (hdet : ∀ s : ℂ, zetaRegularizedDetPrimon s = zetaTarget s)
    (s : ℂ) :
    zetaRegularizedDetPrimon s = zetaTarget s :=
  hdet s

end InfoGeometry.Canonical.PrimonThermodynamicZetaBridge
