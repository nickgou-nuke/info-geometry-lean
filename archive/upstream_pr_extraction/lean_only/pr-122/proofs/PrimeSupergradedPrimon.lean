import proofs.FinitePrimeFock
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prime-indexed supergraded primon algebra

Finite theorem-honest wrapper around `FinitePrimeFock`.

The infinite Euler product and any analytic continuation remain outside scope.
-/

noncomputable section

namespace PrimeSupergradedPrimon

open scoped BigOperators

/-- A finite prime-indexed mode. -/
structure PrimeMode where
  p : ℕ
  isPrime : Nat.Prime p

/-- Primitive arithmetic energy scale `εₚ = log p`. -/
def primeEnergy (mode : PrimeMode) : ℝ :=
  Real.log (mode.p : ℝ)

/-- Real Gibbs weight `q_p = exp(β μ) * p^(-β)`. -/
def primonWeightR (mode : PrimeMode) (β μ : ℝ) : ℝ :=
  Real.exp (β * μ) * Real.rpow (mode.p : ℝ) (-β)

/-- Complexified Gibbs weight used in the finite partition products. -/
def primonWeight (mode : PrimeMode) (β μ : ℝ) : ℂ :=
  (primonWeightR mode β μ : ℂ)

/-- Package a prime mode with its complex Gibbs weight. -/
def weightedMode (mode : PrimeMode) (β μ : ℝ) : FinitePrimeFock.PrimeMode :=
  { p := mode.p
    isPrime := mode.isPrime
    weight := primonWeight mode β μ }

/-- Attach the prime Gibbs weight to a finite prime list. -/
def attachWeights (β μ : ℝ) (modes : List PrimeMode) : List FinitePrimeFock.PrimeMode :=
  modes.map fun mode => weightedMode mode β μ

/-- Finite bosonic partition over weighted prime modes. -/
def finiteBosonicPartition (modes : List PrimeMode) (β μ : ℝ) : ℂ :=
  FinitePrimeFock.finitePrimeBosonicPartition (attachWeights β μ modes)

/-- Finite ordinary fermionic partition over weighted prime modes. -/
def finiteFermionicPartition (modes : List PrimeMode) (β μ : ℝ) : ℂ :=
  FinitePrimeFock.ordinaryFermionTrace
    ((attachWeights β μ modes).map fun mode => mode.weight)

/-- Finite graded partition over weighted prime modes. -/
def finiteGradedPartition (modes : List PrimeMode) (β μ : ℝ) : ℂ :=
  FinitePrimeFock.finitePrimeGradedIndex (attachWeights β μ modes)

/-- At zero chemical potential, the real Gibbs weight is the standard prime power. -/
@[simp]
theorem primonWeightR_mu_zero (mode : PrimeMode) (β : ℝ) :
    primonWeightR mode β 0 = Real.rpow (mode.p : ℝ) (-β) := by
  simp [primonWeightR]

/-- At zero chemical potential, the complex Gibbs weight is the complexified prime power. -/
@[simp]
theorem primonWeight_mu_zero (mode : PrimeMode) (β : ℝ) :
    primonWeight mode β 0 = (Real.rpow (mode.p : ℝ) (-β) : ℂ) := by
  simp [primonWeight]

/-- Mapping weights at `μ = 0` yields the arithmetic prime-power sequence. -/
theorem attachWeights_mu_zero_weights (modes : List PrimeMode) (β : ℝ) :
    ((attachWeights β 0 modes).map fun mode => mode.weight) =
      modes.map fun mode => (Real.rpow (mode.p : ℝ) (-β) : ℂ) := by
  simp [attachWeights, weightedMode, primonWeight]

/-- Finite-stage compatibility under list concatenation for the bosonic sector. -/
theorem finiteBosonicPartition_append
    (modes₁ modes₂ : List PrimeMode) (β μ : ℝ) :
    finiteBosonicPartition (modes₁ ++ modes₂) β μ =
      finiteBosonicPartition modes₁ β μ * finiteBosonicPartition modes₂ β μ := by
  simpa [finiteBosonicPartition, attachWeights] using
    FinitePrimeFock.finitePrimeBosonicPartition_append
      (attachWeights β μ modes₁) (attachWeights β μ modes₂)

/-- Finite-stage compatibility under list concatenation for the graded sector. -/
theorem finiteGradedPartition_append
    (modes₁ modes₂ : List PrimeMode) (β μ : ℝ) :
    finiteGradedPartition (modes₁ ++ modes₂) β μ =
      finiteGradedPartition modes₁ β μ * finiteGradedPartition modes₂ β μ := by
  simpa [finiteGradedPartition, attachWeights] using
    FinitePrimeFock.finitePrimeGradedIndex_append
      (attachWeights β μ modes₁) (attachWeights β μ modes₂)

/-- Finite-stage compatibility under list concatenation for the fermionic trace. -/
theorem finiteFermionicPartition_append
    (modes₁ modes₂ : List PrimeMode) (β μ : ℝ) :
    finiteFermionicPartition (modes₁ ++ modes₂) β μ =
      finiteFermionicPartition modes₁ β μ * finiteFermionicPartition modes₂ β μ := by
  simpa [finiteFermionicPartition, attachWeights] using
    FinitePrimeFock.ordinaryFermionTrace_append
      ((attachWeights β μ modes₁).map fun mode => mode.weight)
      ((attachWeights β μ modes₂).map fun mode => mode.weight)

/-- Finite cancellation theorem for the weighted prime modes. -/
theorem finiteBosonicPartition_mul_finiteGradedPartition
    (modes : List PrimeMode) (β μ : ℝ)
    (h : ∀ mode ∈ modes, primonWeight mode β μ ≠ 1) :
    finiteBosonicPartition modes β μ * finiteGradedPartition modes β μ = 1 := by
  unfold finiteBosonicPartition finiteGradedPartition
  apply FinitePrimeFock.finite_prime_boson_cancels_graded
  intro mode hmode
  rw [attachWeights] at hmode
  rcases List.mem_map.mp hmode with ⟨m, hm, rfl⟩
  simpa [weightedMode] using h m hm

/-- Synthesis theorem for the prime sector at zero chemical potential. -/
theorem primeSector_mu_zero_synthesis
    (modes : List PrimeMode) (β : ℝ) :
    finiteBosonicPartition modes β 0 =
      FinitePrimeFock.finitePrimeBosonicPartition (attachWeights β 0 modes) ∧
    finiteGradedPartition modes β 0 =
      FinitePrimeFock.finitePrimeGradedIndex (attachWeights β 0 modes) ∧
    ((attachWeights β 0 modes).map fun mode => mode.weight) =
      modes.map fun mode => (Real.rpow (mode.p : ℝ) (-β) : ℂ) := by
  exact ⟨rfl, rfl, attachWeights_mu_zero_weights modes β⟩

end PrimeSupergradedPrimon
