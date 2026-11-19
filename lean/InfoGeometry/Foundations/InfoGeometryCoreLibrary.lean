/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- Pre-existing Foundational Pillars (I–IV) & Krein Bridges
import InfoGeometry.InformationGeometry.ParametricCramerRaoAndCumulants
import InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity
import InfoGeometry.InformationGeometry.EguchiMetricsAndDualFlatCurvature
import InfoGeometry.Categorical.MarkovCategoryAndColimitInformation
import InfoGeometry.Categorical.MarkovComonoidAndBlackwellSufficiency
import InfoGeometry.OperatorAlgebra.KadisonSchwarzAndQuantumCramerRao
import InfoGeometry.OperatorAlgebra.GNSRepresentationAndPetzMonotoneMetrics
import InfoGeometry.Foundations.ClassicalToOperatorInformationBridge
import InfoGeometry.Epistemology.ChentsovUniqueness
import InfoGeometry.Canonical.DualConnectionsFiniteExpFamily
import InfoGeometry.Modular.AmariChentsovDualConnections
import InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
import InfoGeometry.Algebra.KreinPeirceTowerIntertwine
import InfoGeometry.Algebra.PeirceTetraktysKreinBridge
import InfoGeometry.Algebra.KitaevPeirceAporiaEpistemicSynthesis

-- Milestone 7: Umbrella Synthesis Integration
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.All

-- Peirce Bi-Sandwich Suite (Baselines, Archetypes 2–3 & Milestone 6B)
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Core
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.PinchedSuperExtension
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Clifford8BdGHorizon
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Supertwistor16AndRealBloch
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.OffShellCoercivityAndColimitGap
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSBathAndAnisotropicKuboMori
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.CustodialTwinLoopAndJosephsonLattice
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSCompletePositivityAndKrausSemigroup
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.BipartiteSeparabilityAndPeirceEntanglement

-- Archetype 4: Graded Clifford Superalgebra & Cut-Rank
import InfoGeometry.Clifford.Cl11SuperBaseAndEntanglementRank

-- Archetypes 7 & 8 and Milestone 6D Operator Algebra Extensions
import InfoGeometry.OperatorAlgebra.TripotentUnboundedResolventFlow
import InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness
import InfoGeometry.OperatorAlgebra.ElitzurLatticeGaugeProjection
import InfoGeometry.OperatorAlgebra.NLinkElitzurChainAndCompactU1Gauge

-- Modular Noncommutative GKSL, Bloch–Umegaki & Quantum Spohn Thermodynamics (Milestones 6 & 6D)
import InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants
import InfoGeometry.Modular.WeldedBlochQuantumSpohnSynthesis
import InfoGeometry.Modular.AnisotropicBKMHessianAndMultiQubitSpohn

-- C*-Algebra Inductive Limits & Cantor Fourier Uncertainty (Milestone 6B)
import InfoGeometry.Algebra.UHFColimitCStarCompletion
import InfoGeometry.Algebra.DiscreteCantorFourierUncertainty

-- Nondegenerate Krein Signature Bridge (Milestone 6B)
import InfoGeometry.Lie.Pin55NondegenerateKreinBridge

-- Noncommutative Weyl–Cartan Split, Iwasawa KAN & Polar Equivariance (Milestones 6C & 6D)
import InfoGeometry.Algebra.WeylCartanKANPolarEquivariance
import InfoGeometry.Algebra.ComplexSL2IwasawaAndHyperbolicPolar

-- Arithmetic Prime Counting & Fluctuation Bounds (Milestone 6D)
import InfoGeometry.Arithmetic.ChebyshevPrimeAndHoeffdingBounds

-- Epistemic Compiler Solve et Coagula Noncommutative Poset (Milestone 6E)
import InfoGeometry.OperatorAlgebra.SolveEtCoagulaPeirceAporiaPoset

-- Milestone 9: Quarantined Modular, Canonical & Algebra Integration
import InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn
import InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance
import InfoGeometry.Canonical.WeylTraceKANPolarEquivariance
import InfoGeometry.Modular.SchrodingerGKSLFlowBridge
import InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly

-- Four Mathematical Open Frontiers Precursors (Milestones M1–M4)
import InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap
import InfoGeometry.Analysis.ContinuousL2CantorFourierUncertainty
import InfoGeometry.Lie.SO55GlobalConformalPrecursors
import InfoGeometry.Arithmetic.RiemannZetaLogarithmicIntegralPrecursors

-- Wave 3 Constructive Unification: Penrose & 4D Colimit-Continuum Lanes
import InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge
import InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge
import InfoGeometry.Categorical.FourDimColimitContinuumSynthesis

/-!
# InfoGeometry Core Library Umbrella and Concrete Witnesses

Unifies the foundational pillars and archetypes of `InfoGeometry`:

1. **Pillar I — Statistical Manifolds & Information Geometry**
   - `InfoGeometry.InformationGeometry.ParametricCramerRaoAndCumulants`
   - `InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity`
   - `InfoGeometry.InformationGeometry.EguchiMetricsAndDualFlatCurvature`
   - `InfoGeometry.Epistemology.ChentsovUniqueness`
   - `InfoGeometry.Canonical.DualConnections`
   - `InfoGeometry.Modular.AmariChentsovDualConnections`
2. **Pillars II & IV — Noncommutative Krein–Peirce–Kraus Operator Algebra & Supertwistors**
   - `InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge`
   - `InfoGeometry.Algebra.KreinPeirceTowerIntertwine`
   - `InfoGeometry.Algebra.PeirceTetraktysKreinBridge`
   - `InfoGeometry.Algebra.KitaevPeirceAporiaEpistemicSynthesis`
   - `InfoGeometry.OperatorAlgebra.KadisonSchwarzAndQuantumCramerRao`
   - `InfoGeometry.OperatorAlgebra.GNSRepresentationAndPetzMonotoneMetrics`
   - `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.All`
   - `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Core`
   - `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.PinchedSuperExtension`
   - `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Clifford8BdGHorizon`
   - `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Supertwistor16AndRealBloch`
   - `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.OffShellCoercivityAndColimitGap`
   - `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSBathAndAnisotropicKuboMori`
   - `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.CustodialTwinLoopAndJosephsonLattice`
   - `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSCompletePositivityAndKrausSemigroup`
   - `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.BipartiteSeparabilityAndPeirceEntanglement`
   - `InfoGeometry.Clifford.Cl11SuperBaseAndEntanglementRank`
   - `InfoGeometry.OperatorAlgebra.TripotentUnboundedResolventFlow`
   - `InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness`
   - `InfoGeometry.OperatorAlgebra.ElitzurLatticeGaugeProjection`
   - `InfoGeometry.OperatorAlgebra.NLinkElitzurChainAndCompactU1Gauge`
   - `InfoGeometry.OperatorAlgebra.SolveEtCoagulaPeirceAporiaPoset`
3. **Pillar III — Markov Categories, Bregman Anti-Isomorphism & Filtered Colimit States**
   - `InfoGeometry.Categorical.MarkovCategoryAndColimitInformation`
   - `InfoGeometry.Categorical.MarkovComonoidAndBlackwellSufficiency`
   - `InfoGeometry.Algebra.UHFColimitCStarCompletion`
4. **Cross-Pillar Bridge — Classical Statistics Embedded in Operator Information Geometry**
   - `InfoGeometry.Foundations.ClassicalToOperatorInformationBridge`
5. **Modular Noncommutative GKSL, Bloch–Umegaki & Quantum Spohn Thermodynamics**
   - `InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants`
   - `InfoGeometry.Modular.WeldedBlochQuantumSpohnSynthesis`
   - `InfoGeometry.Modular.AnisotropicBKMHessianAndMultiQubitSpohn`
6. **Lie, Iwasawa KAN & Harmonic Analysis Bridges**
   - `InfoGeometry.Lie.Pin55NondegenerateKreinBridge`
   - `InfoGeometry.Algebra.WeylCartanKANPolarEquivariance`
   - `InfoGeometry.Algebra.ComplexSL2IwasawaAndHyperbolicPolar`
   - `InfoGeometry.Algebra.DiscreteCantorFourierUncertainty`
7. **Arithmetic Prime Counting & Fluctuation Bounds**
   - `InfoGeometry.Arithmetic.ChebyshevPrimeAndHoeffdingBounds`
   - `InfoGeometry.Arithmetic.RiemannZetaLogarithmicIntegralPrecursors`
8. **Four Research Frontiers Precursors (Yang–Mills OS Semigroup, Continuous L² Cantor FUP, Global SO(5,5) CFT, and ζ / li(x))**
   - `InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap`
   - `InfoGeometry.Analysis.ContinuousL2CantorFourierUncertainty`
   - `InfoGeometry.Lie.SO55GlobalConformalPrecursors`
   - `InfoGeometry.Arithmetic.RiemannZetaLogarithmicIntegralPrecursors`

Also provides concrete non-vacuous witnesses on `Bool` (`bernoulliExpFamily`,
`bernoulliMultiExpFamily`, and `binarySymmetricChannel`) and on `Fin 2` (`qubitGibbsState`
with Pauli-X and Pauli-Z tangent observables) instantiating exponential-family strict
convexity, KL–Bregman duality, Cramér–Rao saturation, dual-connection cubic tensors,
Fisher metric contraction, Amari `α`-divergence contraction, Kraus variance contraction,
and strict Morozova–Chentsov–Petz metric separation / classical collapse without vacuous
assumptions.
-/

noncomputable section

namespace InfoGeometry.Foundations.InfoGeometryCoreLibrary

open Finset
open scoped BigOperators
open InfoGeometry.ExponentialFamily
open InfoGeometry.Epistemology.VariationalRG
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.InformationGeometry.ParametricCramerRaoAndCumulants
open InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity
open InfoGeometry.InformationGeometry.EguchiMetricsAndDualFlatCurvature
open InfoGeometry.Categorical.MarkovComonoidAndBlackwellSufficiency
open InfoGeometry.OperatorAlgebra.GNSRepresentationAndPetzMonotoneMetrics
open InfoGeometry.Modular
open KuboMoriBogoliubov
open InfoGeometry.Foundations.ClassicalToOperatorInformationBridge

/-! ### 1. Concrete Non-Vacuous Bernoulli Exponential Family Witness -/

/-- Uniform base probability distribution on `Bool`. -/
def bernoulliBase : InfoGeometry.ProbabilityDist Bool :=
  InfoGeometry.FinProb.of_fintype (fun _ => (1 / 2 : ENNReal))
    (by
      rw [Fintype.sum_bool]
      exact ENNReal.add_halves 1)

lemma bernoulliBase_pos (b : Bool) : 0 < (bernoulliBase b).toReal := by
  dsimp [bernoulliBase, InfoGeometry.FinProb.of_fintype]
  norm_num

/-- Concrete Bernoulli finite exponential family on `Bool` with indicator statistic
`stat b := if b then 1 else 0`. -/
def bernoulliExpFamily : FiniteExponentialFamilyData Bool where
  base := bernoulliBase
  stat b := if b then 1 else 0
  base_pos := bernoulliBase_pos

/-- Non-vacuous strict convexity of the Bernoulli cumulant generating function on `ℝ`. -/
theorem bernoulliExpFamily_strictConvexOn :
    StrictConvexOn ℝ Set.univ (familyLogPartition bernoulliExpFamily) := by
  have hfn :
      familyLogPartition bernoulliExpFamily =
        InfoGeometry.Analytic.logSumExp (fun b => (bernoulliBase b).toReal)
          bernoulliExpFamily.stat := rfl
  rw [hfn]
  exact logSumExp_strictConvexOn_of_nonconstant
    (fun b => (bernoulliBase b).toReal) bernoulliExpFamily.stat
    bernoulliBase_pos ⟨true, false, by norm_num [bernoulliExpFamily]⟩

/-- Non-vacuous unconditional KL–Bregman identity on `bernoulliExpFamily`. -/
theorem bernoulliExpFamily_kl_eq_bregman (θ η : ℝ) :
    KLParam bernoulliExpFamily θ η = (logPotential bernoulliExpFamily).bregman η θ :=
  KLParam_eq_bregman_unconditional bernoulliExpFamily θ η

/-- Non-vacuous exact Cramér–Rao saturation of the Bernoulli sufficient statistic at all `θ`. -/
theorem bernoulliExpFamily_saturates_cramer_rao (θ : ℝ) :
    let dp := fun b =>
      familyDensity bernoulliExpFamily θ b *
        (bernoulliExpFamily.stat b - statMean bernoulliExpFamily θ)
    (∑ b, dp b * bernoulliExpFamily.stat b) ^ 2 =
      statVariance (familyDensity bernoulliExpFamily θ) bernoulliExpFamily.stat *
        modelFisherInfo (familyProbInterior bernoulliExpFamily θ) dp :=
  sufficient_statistic_saturates_cramer_rao bernoulliExpFamily θ

/-! ### 2. Concrete Binary Symmetric Channel Witness -/

/-- Binary symmetric Markov kernel `BSC(ε)` on `Bool` for flip probability `0 < ε < 1`. -/
def binarySymmetricChannel (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) : MarkovKernel Bool Bool where
  T a b := if a = b then 1 - ε else ε
  nonneg a b := by
    by_cases h : a = b
    · simp only [h, ↓reduceIte]
      linarith
    · simp only [h, ↓reduceIte]
      exact le_of_lt h0
  sum_one a := by
    rw [Fintype.sum_bool]
    cases a <;> simp

/-- Every `binarySymmetricChannel ε` with `0 < ε < 1` is column-nondegenerate. -/
theorem binarySymmetricChannel_colNondegenerate (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    ColNondegenerate (binarySymmetricChannel ε h0 h1) := by
  intro b
  refine ⟨b, ?_⟩
  simp [binarySymmetricChannel]
  linarith

/-- Non-vacuous Fisher metric contraction along `binarySymmetricChannel`. -/
theorem binarySymmetricChannel_fisher_contraction
    (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
    (P : ProbInterior Bool) (u : Bool → ℝ) :
    fisherMetric
        (pushInterior (binarySymmetricChannel ε h0 h1) P
          (binarySymmetricChannel_colNondegenerate ε h0 h1))
        (pushforwardTangentVec (binarySymmetricChannel ε h0 h1) u)
        (pushforwardTangentVec (binarySymmetricChannel ε h0 h1) u) ≤
      fisherMetric P u u :=
  chentsov_markov_fisher_contraction (binarySymmetricChannel ε h0 h1) P
    (binarySymmetricChannel_colNondegenerate ε h0 h1) u

/-- Non-vacuous Amari `α`-divergence contraction along `binarySymmetricChannel` for every
`αParam : ℝ`. -/
theorem binarySymmetricChannel_alphaDivergence_contraction
    (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) (αParam : ℝ) (P Q : ProbInterior Bool) :
    amariAlphaDivergence αParam
        (pushInterior (binarySymmetricChannel ε h0 h1) P
          (binarySymmetricChannel_colNondegenerate ε h0 h1)).p
        (pushInterior (binarySymmetricChannel ε h0 h1) Q
          (binarySymmetricChannel_colNondegenerate ε h0 h1)).p ≤
      amariAlphaDivergence αParam P.p Q.p :=
  amariAlphaDivergence_markov_contraction αParam (binarySymmetricChannel ε h0 h1)
    (binarySymmetricChannel_colNondegenerate ε h0 h1) P Q

/-- Non-vacuous Kraus conditional-expectation variance contraction along
`binarySymmetricChannel`. -/
theorem binarySymmetricChannel_variance_contraction
    (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) (P : ProbDist Bool) (f : Bool → ℝ) :
    statVariance P.p (fun a => ∑ b, (binarySymmetricChannel ε h0 h1).T a b * f b) ≤
      statVariance (pushforward (binarySymmetricChannel ε h0 h1) P).p f :=
  markov_conditional_expectation_variance_contraction (binarySymmetricChannel ε h0 h1) P f

/-! ### 3. Concrete Multivariate Dual-Connection Manifold Witness -/

/-- Multivariate 1D Bernoulli exponential family on `Bool` embedded in
`Information.FiniteExpFamily (α := Bool) 1`. -/
def bernoulliMultiExpFamily : InfoGeometry.Information.FiniteExpFamily (α := Bool) 1 where
  stat b _ := if b then 1 else 0
  base _ := 1 / 2
  base_pos _ := by norm_num

/-- Linear independence of the nonconstant Bernoulli statistic in `FiniteExpFamily 1`. -/
theorem bernoulliMultiExpFamily_indep (θ : Fin 1 → ℝ) :
    ∀ v : Fin 1 → ℝ, v ≠ 0 →
      ∃ x : Bool,
        InfoGeometry.Information.linearStat bernoulliMultiExpFamily v x ≠
          InfoGeometry.Information.expectation bernoulliMultiExpFamily θ
            (InfoGeometry.Information.linearStat bernoulliMultiExpFamily v) := by
  intro v hv
  have hv0 : v 0 ≠ 0 := by
    intro h0
    apply hv
    ext i
    rw [Fin.eq_zero i]
    exact h0
  have hneq :
      InfoGeometry.Information.linearStat bernoulliMultiExpFamily v true ≠
        InfoGeometry.Information.linearStat bernoulliMultiExpFamily v false := by
    unfold InfoGeometry.Information.linearStat bernoulliMultiExpFamily
    simp [hv0]
  by_cases htrue :
      InfoGeometry.Information.linearStat bernoulliMultiExpFamily v true =
        InfoGeometry.Information.expectation bernoulliMultiExpFamily θ
          (InfoGeometry.Information.linearStat bernoulliMultiExpFamily v)
  · refine ⟨false, ?_⟩
    intro hfalse
    exact hneq (htrue.trans hfalse.symm)
  · exact ⟨true, htrue⟩

/-- Constructive non-trivial `AmariChentsovDualConnections.DualConnectionManifold (Fin 1 → ℝ)`
attached to `bernoulliMultiExpFamily` at parameter `θ`. -/
def bernoulliDualConnectionManifold (θ : Fin 1 → ℝ) :
    AmariChentsovDualConnections.DualConnectionManifold (Fin 1 → ℝ) :=
  expFamilyDualConnectionManifold bernoulliMultiExpFamily θ (bernoulliMultiExpFamily_indep θ)

/-- Non-vacuous witness equating `amariCubicForm` of `bernoulliDualConnectionManifold θ` to
the exact Bernoulli third cumulant `thirdCumulant`. -/
theorem bernoulliDualConnectionManifold_cubic_eq_thirdCumulant
    (θ u v w : Fin 1 → ℝ) :
    AmariChentsovDualConnections.amariCubicForm
        (bernoulliDualConnectionManifold θ) u v w =
      thirdCumulant bernoulliMultiExpFamily θ u v w :=
  expFamily_amariCubicForm_eq_thirdCumulant bernoulliMultiExpFamily θ
    (bernoulliMultiExpFamily_indep θ) u v w

/-! ### 4. Concrete Qubit Gibbs State Petz Metric Hierarchy & Classical Collapse -/

/-- Non-maximally-mixed diagonal qubit Gibbs density state `diag(1/4, 3/4)` in `Fin 2`. -/
def qubitGibbsState : FaithfulDensityState (Fin 2) where
  eigenvalues := ![1 / 4, 3 / 4]
  p_pos i := by
    rcases i with ⟨_ | _ | n, hn⟩
    · norm_num
    · norm_num
    · omega
  p_sum := by
    rw [Fin.sum_univ_two]
    norm_num

/-- Pauli-X non-commuting tangent operator on `Fin 2`. -/
def pauliXTangent : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Diagonal Pauli-Z observable vector `(1, -1)` on `Fin 2`. -/
def pauliZDiag : Fin 2 → ℝ := ![1, -1]

/-- Pauli-Z commuting (classical) tangent operator on `Fin 2`. -/
def pauliZTangent : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => (pauliZDiag i : ℂ))

/-- Non-vacuous strict Morozova–Chentsov–Petz metric separation on a non-commuting Pauli-X
variation: `SLD < BKM < GM < RLD`. -/
theorem qubitGibbsState_pauliX_strict_hierarchy :
    sldTangentMetric qubitGibbsState pauliXTangent <
        bkmTangentMetric qubitGibbsState pauliXTangent ∧
      bkmTangentMetric qubitGibbsState pauliXTangent <
        geomTangentMetric qubitGibbsState pauliXTangent ∧
      geomTangentMetric qubitGibbsState pauliXTangent <
        rldTangentMetric qubitGibbsState pauliXTangent := by
  have hp0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hp1 : (0 : ℝ) < 3 / 4 := by norm_num
  have hne : (1 / 4 : ℝ) ≠ 3 / 4 := by norm_num
  have hx00 : pauliXTangent 0 0 = 0 := by simp [pauliXTangent]
  have hx01 : pauliXTangent 0 1 = 1 := by simp [pauliXTangent]
  have hx10 : pauliXTangent 1 0 = 1 := by simp [pauliXTangent]
  have hx11 : pauliXTangent 1 1 = 0 := by simp [pauliXTangent]
  have he0 : qubitGibbsState.eigenvalues 0 = 1 / 4 := by simp [qubitGibbsState]
  have he1 : qubitGibbsState.eigenvalues 1 = 3 / 4 := by simp [qubitGibbsState]
  have hsld :
      sldTangentMetric qubitGibbsState pauliXTangent = 2 / arithMean (1 / 4) (3 / 4) := by
    unfold sldTangentMetric
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [hx00, hx01, hx10, hx11, he0, he1]
    simp only [Complex.normSq_zero, Complex.normSq_one, zero_div, zero_add, add_zero]
    rw [arithMean_symm (3 / 4) (1 / 4)]
    ring
  have hbkm :
      bkmTangentMetric qubitGibbsState pauliXTangent = 2 / logMean (1 / 4) (3 / 4) := by
    unfold bkmTangentMetric
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [hx00, hx01, hx10, hx11]
    simp only [Complex.normSq_zero, Complex.normSq_one, zero_div, zero_add, add_zero]
    change 1 / logMean (qubitGibbsState.eigenvalues 0) (qubitGibbsState.eigenvalues 1) +
        1 / logMean (qubitGibbsState.eigenvalues 1) (qubitGibbsState.eigenvalues 0) =
      2 / logMean (1 / 4) (3 / 4)
    rw [he0, he1, logMean_symm (3 / 4) (1 / 4)]
    ring
  have hgeom :
      geomTangentMetric qubitGibbsState pauliXTangent = 2 / geomMean (1 / 4) (3 / 4) := by
    unfold geomTangentMetric
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [hx00, hx01, hx10, hx11, he0, he1]
    simp only [Complex.normSq_zero, Complex.normSq_one, zero_div, zero_add, add_zero]
    rw [geomMean_symm (3 / 4) (1 / 4)]
    ring
  have hrld :
      rldTangentMetric qubitGibbsState pauliXTangent = 2 / harmonicMean (1 / 4) (3 / 4) := by
    unfold rldTangentMetric
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [hx00, hx01, hx10, hx11, he0, he1]
    simp only [Complex.normSq_zero, Complex.normSq_one, zero_div, zero_add, add_zero]
    have hhsym : harmonicMean (3 / 4) (1 / 4) = harmonicMean (1 / 4) (3 / 4) := by
      unfold harmonicMean
      ring
    rw [hhsym]
    ring
  rw [hsld, hbkm, hgeom, hrld]
  refine ⟨?_, ?_, ?_⟩
  · exact div_lt_div_of_pos_left (by norm_num) (logMean_pos hp0 hp1)
      (logMean_lt_arithMean_of_ne hp0 hp1 hne)
  · exact div_lt_div_of_pos_left (by norm_num) (geomMean_pos hp0 hp1)
      (geomMean_lt_logMean_of_ne hp0 hp1 hne)
  · exact div_lt_div_of_pos_left (by norm_num) (harmonicMean_pos hp0 hp1)
      (harmonicMean_lt_geomMean_of_ne hp0 hp1 hne)

/-- Non-vacuous classical collapse on commuting Pauli-Z tangent observable:
`SLD = BKM = GM = RLD = 16 / 3`. -/
theorem qubitGibbsState_pauliZ_classical_collapse :
    sldTangentMetric qubitGibbsState pauliZTangent = 16 / 3 ∧
      bkmTangentMetric qubitGibbsState pauliZTangent = 16 / 3 ∧
      geomTangentMetric qubitGibbsState pauliZTangent = 16 / 3 ∧
      rldTangentMetric qubitGibbsState pauliZTangent = 16 / 3 := by
  have hcoll := petz_metrics_diagonal_eq_classical_fisher qubitGibbsState pauliZDiag
  have hval : (∑ i : Fin 2, pauliZDiag i ^ 2 / qubitGibbsState.eigenvalues i) = 16 / 3 := by
    rw [Fin.sum_univ_two]
    simp [pauliZDiag, qubitGibbsState]
    norm_num
  dsimp only [pauliZTangent]
  rw [hcoll.1, hcoll.2.1, hcoll.2.2.1, hcoll.2.2.2, hval]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### 5. Four Mathematical Open Frontiers Precursor Realization Witnesses -/

/-- Non-vacuous Frontier 1 witness: the Euclidean lattice transfer-matrix spectral mass gap
`Δ(J) = -log(tanh J)` is strictly positive at coupling `J = 1`. -/
theorem yangMills_transfer_spectral_gap_witness :
    0 < InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap.spectralMassGap 1 :=
  InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap.spectralMassGap_pos
    one_pos

/-- Non-vacuous Frontier 2 witness: the continuous `L²([0, 1])` multiscale Cantor Fourier
uncertainty contraction ratio at base `b = 4` and `m = 3` removed digits equals `1 / 4`. -/
theorem continuous_fup_cantor_contraction_witness :
    InfoGeometry.Analysis.ContinuousL2CantorFourierUncertainty.cantor_fup_ratio 4 3 = 1 / 4 :=
  (InfoGeometry.Analysis.ContinuousL2CantorFourierUncertainty.continuous_cantor_witness_b4_m3).1

/-- Non-vacuous Frontier 3 witness: the 1-parameter hyperbolic boost `Λ(1)` belongs to the
global non-compact Lie group `SO(5,5)` preserving the signature `(5,5)` Krein form `J55`. -/
theorem so55_conformal_hyperbolic_boost_witness :
    InfoGeometry.Lie.SO55GlobalConformalPrecursors.IsSO55GroupMatrix
      (InfoGeometry.Lie.SO55GlobalConformalPrecursors.so55Boost 1) :=
  InfoGeometry.Lie.SO55GlobalConformalPrecursors.so55Boost_isSO55 1

/-- Non-vacuous Frontier 4 witness: the logarithmic integral `li(x) = ∫ t in 2..x, 1 / log t`
evaluates to `0` at its base point `x = 2`. -/
theorem riemannZeta_li_calculus_witness :
    InfoGeometry.Arithmetic.GenuineBounds.li 2 = 0 :=
  InfoGeometry.Arithmetic.RiemannZetaLogarithmicIntegralPrecursors.li_two

/-! ### 6. Penrose & 4D Colimit--Continuum Unification Witnesses -/

/-- Unification witness 1: a Penrose--Onsager--Yang two-mode spinor induces a future-null
`Q55` celestial paravector matching `rankOneKernel χ`, while a spatial Pauli matrix yields a
strict Moore--Penrose inverse and square-zero nonzero oblique projector mismatch. -/
theorem penrose_spinor_dyad_and_oblique_defect_witness
    (χ : InfoGeometry.Quantum.PenroseOnsagerYang.Mode (Fin 2)) :
    let p_spin := InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.spinorToMinkowski13 χ
    let v : Fin 3 → ℝ := ![1, 0, 0]
    let X := InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence.paravectorToSolderingMatrix (0, v)
    InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence.paravectorToSolderingMatrix p_spin =
        InfoGeometry.Quantum.PenroseOnsagerYang.rankOneKernel χ ∧
      InfoGeometry.Clifford.Clifford55.Q55
          (InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice.minkowskiSlice p_spin) = 0 ∧
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse
          (InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.wittIncidenceBlockIdempotent X)
          (InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.wittIncidenceBlockMPInverse X 1) ∧
      InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.incidenceProjectorMismatch X 1 *
          InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.incidenceProjectorMismatch X 1 = 0 ∧
      InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.incidenceProjectorMismatch X 1 ≠ 0 := by
  intro p_spin v X
  have hv := InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.spatial_pauli_sq_eq_smul v
  have hr1 : (∑ i : Fin 3, v i ^ 2 : ℝ) = 1 := by simp [v, Fin.sum_univ_three]
  have hX1 : Matrix.conjTranspose X * X =
      ((1 : ℝ) : ℂ) • (1 : InfoGeometry.Twistor.PenroseIncidence.ComplexSpacetime) := by
    simpa [hr1, X] using hv.2
  have hXne : X ≠ 0 := by
    intro h0
    have h01 := congrArg (fun M : InfoGeometry.Twistor.PenroseIncidence.ComplexSpacetime => M 0 1) h0
    simp [X, v, InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence.paravectorToSolderingMatrix,
      InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence.minkowski13ToMinkowski4,
      InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix,
      InfoGeometry.Geometry.PauliParavectorBridge.toPauliParavector,
      InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix] at h01
  have hObs :=
    InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.incidenceProjectorMismatch_nilpotent_and_obstruction
      X 1 zero_le_one hX1 hXne
  exact ⟨InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.paravectorToSolderingMatrix_spinorToMinkowski13 χ,
    (InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.spinorToMinkowski13_null_and_causal χ).1,
    InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge.isMoorePenroseInverse_wittIncidenceBlock
      X 1 zero_le_one hX1,
    hObs.1, hObs.2.1⟩

/-- Unification witness 2: Dirac `(5,5)` conformal inversion preserves projective lightlike
grammar and `NullQuadric` membership across rescaled Minkowski charts, and the noncommutative
`2 × 2` matrix Penrose Kite/Dart system satisfies `K^2 = K + 1` via `evalFibonacciK0OnPenroseKite`. -/
theorem penrose_ccc_so55_and_fibonacciK0_kite_witness
    (k : InfoGeometry.Algebra.FibonacciGrothendieckRing.FibonacciK0) :
    let p₀ : InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice.Minkowski13 := (2, ![1, 0, 0])
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.diracNullConeEmbed
          (InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.minkowskiConformalInvert p₀) ∈
        InfoGeometry.Lie.SO55GlobalConformalPrecursors.NullQuadric ∧
      InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.spatialRatioConformalGrammar.grammar
          (InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.diracNullConeEmbed
            (InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.minkowskiConformalInvert p₀)) =
        1 / 2 ∧
      A * C ≠ C * A ∧
      InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.evalFibonacciK0OnPenroseKite
          P A C
          (InfoGeometry.Algebra.FibonacciGrothendieckRing.k0Mul
            InfoGeometry.Algebra.FibonacciGrothendieckRing.fibTauK0 k) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.penroseKiteOp P A C *
          InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.evalFibonacciK0OnPenroseKite
            P A C k := by
  intro p₀ P A C
  have hccc :=
    InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.spatialRatioConformalGrammar_nontrivial_crossover_witness
  have hkite :=
    InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.concrete_matrix_penroseKite_unit_dart_witness
  refine ⟨InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.diracNullConeEmbed_mem_nullQuadric _,
    hccc.2.2.1, hkite.2.1, ?_⟩
  rw [hkite.2.2.2.2.1 InfoGeometry.Algebra.FibonacciGrothendieckRing.fibTauK0 k,
    InfoGeometry.OperatorAlgebra.PenroseConformalAndInflationColimitBridge.evalFibonacciK0OnPenroseKite_tau]

/-- Unification witness 3: 4D dyadic spacetime lattice refinement scales as `16^n`, embeds
injectively into `Field4DContinuum`, and dualizes additive continuum functionals to compatible
projective threads. -/
theorem fourDim_dyadic_colimit_hom_duality_witness
    (m n : ℕ) (hmn : m ≤ n)
    (Ψ : InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.Field4DContinuum →+ ℝ) :
    Fintype.card (InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.SpacetimeLattice4D n) =
        16 ^ n ∧
      Function.Injective
        (InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.spacetime4DRetractionSectionTower.ι
          m n hmn) ∧
      Function.Injective
        (AddCommGroup.DirectLimit.of
          InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.Field4D
          (fun _ _ h =>
            (InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.refineField4D h).toAddMonoidHom)
          n) ∧
      (InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.addCommGroupDirectLimitHomEquivProjectiveLimit
          InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.Field4D
          (fun _ _ h =>
            (InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.refineField4D h).toAddMonoidHom)
          ℝ).symm
        ((InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.addCommGroupDirectLimitHomEquivProjectiveLimit
            InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.Field4D
            (fun _ _ h =>
              (InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.refineField4D h).toAddMonoidHom)
            ℝ) Ψ) = Ψ := by
  have hfaith :=
    InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.field4DContinuum_faithful_and_dual_threads n
  exact ⟨InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.card_spacetimeLattice4D n,
    InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.spacetime4DRetractionSectionTower.ι_injective
      m n hmn,
    hfaith.1,
    (InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.addCommGroupDirectLimitHomEquivProjectiveLimit
      InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.Field4D
      (fun _ _ h =>
        (InfoGeometry.Categorical.FourDimColimitContinuumSynthesis.refineField4D h).toAddMonoidHom)
      ℝ).left_inv Ψ⟩

end InfoGeometry.Foundations.InfoGeometryCoreLibrary

end section
