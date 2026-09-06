import Mathlib
import proofs.NonIsoConf3LiteratureLemmaChain
import proofs.NonIsoConf3RankDecision
import proofs.PenroseSpinTilingCapstone

/-!
# Log-generating-potential finite sums

Finite index types with real-valued weights give partition sums, logarithmic
potentials, and derivative-based potentials.  The results below are finite
sum identities and rank equalities over the imported finite bases.
-/

noncomputable section

namespace LogCFTGeneratingPotential

open scoped BigOperators
open NonIsoConf3DeRhamCooperad
open NonIsoConf3RankDecision
open NonIsoConf3LiteratureLemmaChain
open PenroseSpinTilingCapstone

/-- A finite index type with a real-valued weight function. -/
structure FiniteSpectrum where
  ι : Type
  fintype : Fintype ι
  energy : ι → ℝ

attribute [instance] FiniteSpectrum.fintype

/-- Finite exponential partition sum `Z(λ)=Σ exp(-λ Eᵢ)`. -/
def partitionFunction (S : FiniteSpectrum) (lam : ℝ) : ℝ :=
  ∑ i : S.ι, Real.exp (-(lam * S.energy i))

/-- Log-generating potential `G(λ)=log Z(λ)`. -/
def logGeneratingPotential (S : FiniteSpectrum) (lam : ℝ) : ℝ :=
  Real.log (partitionFunction S lam)

/-- Scaled logarithmic potential `F(λ)=-(1/λ)G(λ)`. -/
def boltzmannFreeEnergy (S : FiniteSpectrum) (lam : ℝ) : ℝ :=
  -(1 / lam) * logGeneratingPotential S lam

/-- Derivative potential `S(λ)=λ² dF/dλ`. -/
def boltzmannEntropyPotential (S : FiniteSpectrum) (lam : ℝ) : ℝ :=
  lam ^ 2 * deriv (fun mu => boltzmannFreeEnergy S mu) lam

@[simp] theorem boltzmannEntropyPotential_def (S : FiniteSpectrum) (lam : ℝ) :
    boltzmannEntropyPotential S lam =
      lam ^ 2 * deriv (fun mu => boltzmannFreeEnergy S mu) lam := rfl

/-- Partition function at zero energy is a sum equal to the finite dimension. -/
theorem partitionFunction_zero_energy (ι : Type) [Fintype ι] :
    partitionFunction ⟨ι, inferInstance, fun _ => 0⟩ 0 = Fintype.card ι := by
  simp [partitionFunction]

/-- The corresponding log-potential is the normalizing `log N` term. -/
theorem logGeneratingPotential_zero_energy (ι : Type) [Fintype ι] :
    logGeneratingPotential ⟨ι, inferInstance, fun _ => 0⟩ 0 =
      Real.log (Fintype.card ι : ℝ) := by
  simp [logGeneratingPotential, partitionFunction_zero_energy]

/-- If two positive partition values multiply, the log-potential is additive. -/
theorem logGeneratingPotential_add_of_factorized
    (ZA ZB : ℝ) (hA : 0 < ZA) (hB : 0 < ZB) :
    Real.log (ZA * ZB) = Real.log ZA + Real.log ZB := by
  exact Real.log_mul (ne_of_gt hA) (ne_of_gt hB)

/-- Finite rank equalities for the imported bases. -/
theorem logCFT_rank32_finite_fingerprint :
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  constructor
  · exact productBasis_card
  constructor
  · exact osFluxBasis_card
  · exact product_vs_os_rank_gap

/-- Joint statement collecting the finite colimit target and rank equalities. -/
theorem penrose_capstone_logCFT_rank32_bridge :
    penrose_spin_tiling_colimit_target ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  constructor
  · exact penrose_spin_tiling_inductive_colimit
  constructor
  · exact productBasis_card
  constructor
  · exact osFluxBasis_card
  · exact product_vs_os_rank_gap

end LogCFTGeneratingPotential

end noncomputable section
