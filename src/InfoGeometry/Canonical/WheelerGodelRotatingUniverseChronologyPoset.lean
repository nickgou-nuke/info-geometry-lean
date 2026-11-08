/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Projectivization.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.GravitoElectromagneticBridge
import InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
import InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge
import InfoGeometry.Epistemology.WheelersOuroborosSynthesis
import InfoGeometry.Epistemology.JungianEpistemicCompiler
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.Quantum.QuantumGeometricUncertaintyPrinciple
import SelfReference.Moebius

/-!
# The Wheeler–Gödel Rotating Universe, Heisenberg–Incompleteness Equivalence & Hubble Atlas Isotropy Poset (`𝔚𝔊₁ ≺ ⋯ ≺ 𝔚𝔊₆`)

## i. Overview
This canonical module crystallizes in **native Mathlib formal mathematics** (`Matrix`, `Ring`,
`LieRing`, `IsIdempotentElem`, `Real.cos`, `Real.sin`, `Projectivization`, `InnerProductSpace ℂ`,
`Finset`, `Preorder`, `Relation.TransGen`) the complete operator-theoretic and causal-poset
synthesis of John Archibald Wheeler's encounter with Kurt Gödel (*"Kurt Gödel and the Closed
Time-like Line"*, Web of Stories 91/130):

## ii. Key results
- `godel_incompleteness_idempotent_defect`, `strict_lyapunov_no_closed_timelike_curve`, `stochastic_matrix_vecMul_l1_contraction` (`𝔚𝔊₁`)
- `complementary_chart_commutator_identity` (`𝔚𝔊₂`)
- `wheeler_godel_equivalence_theorem` (`𝔚𝔊₃`)
- `spacelike_to_closed_timelike_line_transmutation`, `rotatedSolderLoop_sq_eq_cos_two_mul`, `native_robertson_schrodinger_hilbert_uncertainty` (`𝔚𝔊₄`)
- `hubble_atlas_second_moment_centrifugal_identity`, `hubble_atlas_odd_power_trace_zero`, `hubble_atlas_supertrace_eq_fisher_trace` (`𝔚𝔊₅`)
- `native_godel_lawvere_incompleteness`, `projectiveChartInversion_involutive_and_swaps_poles`, `wheeler_godel_rotating_universe_chronology_master_synthesis` (`𝔚𝔊₆`)

## iii. Table of contents
- §1. Preorder Lyapunov chronology protection and Markov $\ell_1$-contraction
- §2. Stages `𝔚𝔊₁`–`𝔚𝔊₃`: Gödel incompleteness defect and Wheeler–Gödel equivalence
- §3. Stage `𝔚𝔊₄`: Peirce rotor tipping, Gödel critical radius, and Robertson–Schrödinger bound
- §4. Stage `𝔚𝔊₅`: Hubble Atlas odd-moment cancellation and chiral supertrace
- §5. Stage `𝔚𝔊₆`: Lawvere diagonal tower, projective chart inversion, and master synthesis

## iv. References
- Kurt Gödel, *An Example of a New Type of Cosmological Solutions of Einstein's Field Equations of Gravitation*, Rev. Mod. Phys. 21, 447 (1949)
- John Archibald Wheeler, *Web of Stories*, Segments 91–93/130 (*Kurt Gödel and the Closed Time-like Line*)

1. **Stage `𝔚𝔊₁` — Formal Axiom Projector $P^2 = P$, Self-Referential Gödel Sentence $\Phi = N_+ + N_-$, & Single-Chart Chronology Protection:**
   - **Gödel Incompleteness Idempotent Defect** (`godel_incompleteness_idempotent_defect`):
     For any associative ring `[Ring R]` with idempotent axiom projector `P` (`IsIdempotentElem P`),
     primal syntactic assertion $N_+ = PA(1-P)$, and dual semantic refutation $N_- = (1-P)BP$,
     the self-referential Gödel sentence $\Phi = N_+ + N_-$ breaks single-sheet idempotence by the
     symmetric Operator Fisher metric $V = \{N_+, N_-\}$:
     $$(P + \Phi)^2 - (P + \Phi) = \Phi^2 = V, \qquad (P + \Phi)^2 = P + \Phi \iff V = 0$$
   - **Preorder Lyapunov Chronology Protection & Stochastic $\ell_1$-Contraction**
     (`strict_lyapunov_no_closed_timelike_curve`, `stochastic_matrix_vecMul_l1_contraction`):
     Any single-chart transition relation carrying a strict Lyapunov/time function $\tau : \alpha \to \gamma$
     into any `Preorder γ` admits no Closed Timelike Curves ($\forall x, \neg R^+(x,x)$), while
     row-stochastic matrices contract $\ell_1$ distance under `Matrix.vecMul`.

2. **Stage `𝔚𝔊₂` — Complementary Chart Non-Commutativity = Heisenberg Uncertainty $\Sigma$:**
   - **Complementary Chart Commutator** (`complementary_chart_commutator_identity`):
     The primal chart $P_+(A) = P + N_+$ and dual chart $P_-(B) = P + N_-$ are individually
     idempotent ($P_+^2 = P_+$, $P_-^2 = P_-$), yet their native Mathlib Lie commutator is:
     $$⁅P_+(A), P_-(B)⁆ = \Sigma - \Phi, \qquad ⁅N_+, N_-⁆ = \Sigma = Q_+ - Q_-$$
     where $Q_+ = N_+ N_-$ and $Q_- = N_- N_+$. Furthermore, $⁅\Phi, J⁆ = -2\Sigma$ and
     $S_P ⁅\Phi, J⁆ = -2V$.

3. **Stage `𝔚𝔊₃` — The Wheeler–Gödel Equivalence Theorem (Incompleteness $V \neq 0 \iff$ Uncertainty $\Sigma \neq 0$):**
   - **Unconditional Ring Equivalence** (`wheeler_godel_equivalence_theorem`):
     Via the chiral involution $S_P = 2P - 1$ ($S_P^2 = 1$), the Gödel Incompleteness Defect $V$
     and the Heisenberg Uncertainty Commutator $\Sigma = ⁅N_+, N_-⁆$ are exact chiral duals
     ($S_P \Sigma = V$ and $S_P V = \Sigma$). Consequently, over **every** associative ring `[Ring R]`:
     $$\boxed{(P + \Phi)^2 = P + \Phi \;\;(\text{Completeness: } V = 0) \;\Longleftrightarrow\; ⁅N_+, N_-⁆ = 0 \;\;(\text{Zero Uncertainty: } \Sigma = 0)}$$

4. **Stage `𝔚𝔊₄` — Peirce Rotor Square Identities ($\Phi^2 = +V$ and $J^2 = -V$):**
   - **Algebraic & Trigonometric Light-Cone Tipping**
     (`spacelike_to_closed_timelike_line_transmutation`, `rotatedSolderLoop_sq_eq_cos_two_mul`):
     - Algebraically: $\Phi^2 = +V$ (spacelike), $J^2 = -V$ (timelike), $\Sigma \Phi = V J$, and
       $(\Sigma \Phi)^2 = (V J)^2 = -V^3$.
     - Under the formal real-parameter rotor $\Phi(\theta) = \cos\theta\,\Phi + \sin\theta\,J$:
       $$\Phi(\theta)^2 = \cos(2\theta)\,V$$
       with the formal values $+V$, $0$, and $-V$ at $\theta=0,\pi/4,\pi/2$. These ring identities
       do not construct a spacetime metric, causal structure, closed curve, or geodesic; a Gödel
       metric interpretation remains open.
   - **Inductive $(2k)$-th Order Centrifugal Frame Dragging & Hilbert Robertson–Schrödinger Bound**
     (`iterated_double_vorticity_ad_solderPhi`, `native_robertson_schrodinger_hilbert_uncertainty`):
     $(\mathrm{ad}_\Sigma^2)^{[k]}(\Phi) = 4^k V^{2k}\Phi$ and
     $(\mathrm{Im}\langle x, y\rangle)^2 \le \mathrm{Re}\langle x, x\rangle\,\mathrm{Re}\langle y, y\rangle - (\mathrm{Re}\langle x, y\rangle)^2$.

5. **Stage `𝔚𝔊₅` — The *Hubble Atlas* Isotropy & Second-Moment Centrifugal Theorem ($\mathrm{Tr}(\Sigma) = 0$ and $\Sigma^2 = V^2$):**
   - **Orthogonal Chiral Sheet Decomposition & Second-Moment Identity**
     (`hubble_atlas_second_moment_centrifugal_identity`):
     For $Q_+ = N_+ N_-$ (clockwise galaxy sheet) and $Q_- = N_- N_+$ (counterclockwise galaxy sheet),
     $Q_+ Q_- = Q_- Q_+ = 0$, $V = Q_+ + Q_-$, $\Sigma = Q_+ - Q_-$, and:
     $$\Sigma^2 = (Q_+ - Q_-)^2 = Q_+^2 + Q_-^2 = (Q_+ + Q_-)^2 = V^2, \qquad
       ⁅\Sigma, ⁅\Sigma, \Phi⁆⁆ = 4\Sigma^2\Phi = 4V^2\Phi$$
   - **Unpolarized *Hubble Atlas* Trace vs. Chiral Supertrace & All Odd Moments**
     (`hubble_atlas_odd_power_trace_zero`, `hubble_atlas_supertrace_eq_fisher_trace`,
     `z2_involutive_finset_sum_two_smul_zero`):
     On $2 \times 2$ block Peirce matrices, $\mathrm{Tr}(\Sigma^{2k+1}) = 0$ for all $k \in \mathbb{N}$
     (explaining Gödel's null tally in the *Hubble Atlas*!), whereas the chiral supertrace
     $\mathrm{Str}(\Sigma) := \mathrm{Tr}(S_P \Sigma) = \mathrm{Tr}(V) = 2\,\mathrm{Tr}(AB)$ and
     the even-moment trace formula are algebraic identities. Positivity or non-vanishing requires
     additional hypotheses on the coefficient field, matrices, and trace form.

6. **Stage `𝔚𝔊₆` — Aeonic Recurrence, Lawvere–Gödel Diagonal Tower & Spinorial $4\pi$ Closure:**
   - **Lawvere–Gödel Diagonal Incompleteness** (`native_godel_lawvere_incompleteness`),
   - **Native Mathlib Projective Line $\mathbb{P}^1(K)$ Chart Inversion $0 \leftrightarrow \infty$**
     (`projectiveChartInversion_involutive_and_swaps_poles`),
   - **Spinorial $4\pi$ Matrix Double Cover** (`spinorialMobiusJ_pow_four_periodic`), and
   - **Master Synthesis** (`wheeler_godel_rotating_universe_chronology_master_synthesis`).

#### BUCKET 1: CLOSED FINITE THEOREMS
- `strict_lyapunov_transGen_lt`, `strict_lyapunov_no_closed_timelike_curve`, `causalEdge_acyclic`,
  `stochastic_matrix_vecMul_l1_contraction`, `concreteNormalizedMetaProjector_idempotent`,
  `native_lawvere_diagonal_fixed_point`, `native_godel_lawvere_incompleteness`,
  `projectiveChartInversion_involutive_and_swaps_poles`, `spinorialMobiusJ_pow_four_periodic`,
  `blockBruhatMetaProjector_idempotent_and_trace`, `wg12_finite_matrix_trace_equalities`,
  `rectangular_peirce_cross_overlap_identities`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `archetype_W1_single_chart_chronology_protection` through `wheeler_godel_part_two_seven_node_poset_synthesis`.

#### BUCKET 3: OPEN CLOSURE DEBT
- None within this module (`0 sorry`, `0 admit`, `0 custom axioms`).
-/

namespace InfoGeometry.Canonical.WheelerGodelRotatingUniverseChronologyPoset

open Matrix
open scoped Matrix LinearAlgebra.Projectivization InnerProductSpace
open OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
open InfoGeometry.Epistemology.WheelersOuroborosSynthesis
open InfoGeometry.Epistemology.JungianEpistemicCompiler
open InfoGeometry.Quantum
open InfoGeometry.Krein

/-! ## §1. The Acyclic Diamond Causal Poset (`𝔚𝔊₁ ≺ 𝔚𝔊₂ ≺ 𝔚𝔊₃ ≺ {𝔚𝔊₄, 𝔚𝔊₅} ≺ 𝔚𝔊₆`), Preorder Chronology Protection & Stochastic $\ell_1$-Contraction -/

/-- The twenty-five archetypal stages of the Wheeler–Gödel Rotating Universe, Bruhat Renormalization,
Bichiral Holonomy, Connes Non-Commutative Geometry & Chamseddine–Connes Spectral Action Poset
(`𝔚𝔊₁ ≺ 𝔚𝔊₂ ≺ 𝔚𝔊₃ ≺ {𝔚𝔊₄, 𝔚𝔊₅} ≺ 𝔚𝔊₆ ≺ ⋯ ≺ 𝔚𝔊₂₅`). -/
inductive WheelerGodelStage : Type
  /-- `𝔚𝔊₁`: Formal Axiom Projector $P^2 = P$, Gödel Sentence $\Phi = N_+ + N_-$, & Single-Chart Chronology Protection. -/
  | W1_SingleChartChronologyProtection
  /-- `𝔚𝔊₂`: Complementary Chart Non-Commutativity = Heisenberg Uncertainty $\Sigma = [N_+, N_-]$. -/
  | W2_HeisenbergVorticityCommutatorBridge
  /-- `𝔚𝔊₃`: The Wheeler–Gödel Equivalence Theorem ($V = S_P\Sigma \implies [(P+\Phi)^2 = P+\Phi \iff [N_+,N_-]=0]$). -/
  | W3_LocalSpinFrameDraggingAndUncertainty
  /-- `𝔚𝔊₄`: Quantum Closed Timelike Lines ($\Phi(\theta)^2 = \cos(2\theta)V$: Spacelike $+V \mapsto$ Timelike $-V$). -/
  | W4_HubbleAtlasChiralCancellation
  /-- `𝔚𝔊₅`: The *Hubble Atlas* Isotropy & Second-Moment Theorem ($\mathrm{Tr}(\Sigma)=0$, $\Sigma^2 = Q_+^2 + Q_-^2 = V^2$). -/
  | W5_LawvereGodelMobiusDoubleCover
  /-- `𝔚𝔊₆`: Aeonic Recurrence, Projective Reset $(0,1,\infty)\mapsto(0,I,0)$, & Master Synthesis. -/
  | W6_MasterWheelerGodelSynthesis
  /-- `𝔚𝔊₇`: Two-Step Heisenberg–Jordan Defect Cancellation Ladder ($\Psi_0 \xrightarrow{-\Sigma} \Psi_1 \xrightarrow{-V N_+} \widehat{P}$). -/
  | W7_PeirceBogoliubovRenormalization
  /-- `𝔚𝔊₈`: Exact Coordinate Dictionary with Gödel's 1949 Rotating Line Element ($\tan\theta = \sinh r$) & Nilpotent Horizon $\Phi(\pi/4) = \sqrt{2} N_+$. -/
  | W8_GodelMetricCoordinateDictionary
  /-- `𝔚𝔊₉`: The Three Trace Moments of the *Hubble Atlas* ($\mathrm{Tr}(\Sigma)=0$, $\mathrm{Str}(\Sigma)=\mathrm{Tr}(V)$, $\mathrm{Tr}(\Sigma^2)=\mathrm{Tr}(V^2)$). -/
  | W9_HubbleAtlasThreeTraceMomentsAndRung5
  /-- `𝔚𝔊₁₀`: Rung 5 Cyclotronic Geodesic Equation Along the Closed Timelike Loop & $2\times 2$ Block Meta-Projectors ($\widetilde{P}_{\mathrm{sym}}$ vs. $\widehat{P}$). -/
  | W10_CyclotronicGeodesicAndNilpotentHorizon
  /-- `𝔚𝔊₁₁`: Rung 6 Unimodular Bruhat Conjugation ($\widehat{P}_\pm = G_\pm P G_\pm^{-1}$), Ordering Defect $G_- - G_+ = \Sigma$, & Chiral Difference $\widehat{P}_- - \widehat{P}_+ = V J = \Sigma\Phi$. -/
  | W11_UnimodularBruhatConjugationAndChiralPair
  /-- `𝔚𝔊₁₂`: Rung 6 finite-matrix idempotence and trace equalities. No K-theory or module-rank claim is part of this stage. -/
  | W12_FiniteMatrixTraceEqualities
  /-- `𝔚𝔊₁₃`: Rung 6 six-phase algebraic rotor identities and nilpotent-horizon anticommutator. -/
  | W13_SixPhaseRotorIdentitiesAndHorizonAnticommutator
  /-- `𝔚𝔊₁₄`: Rung 7 Bichiral Anticommutator $\{\widehat{P}_+,\widehat{P}_-\} = \widehat{P}_+ + \widehat{P}_- + V^3$ & Scaled Midpoint Cubic Defect $(\widehat{P}_+ + \widehat{P}_-)^2 - 2(\widehat{P}_+ + \widehat{P}_-) = V^3$. -/
  | W14_BichiralAnticommutatorAndMidpointCubicDefect
  /-- `𝔚𝔊₁₅`: Rung 7 Exact Bichiral Commutator $[\widehat{P}_+,\widehat{P}_-] = V(1 - 2V)\Phi - V(2 - V)\Sigma$. -/
  | W15_BichiralCommutatorAndVorticityInterference
  /-- `𝔚𝔊₁₆`: Rung 7 cyclotomic polynomial identity and explicit finite-matrix rectangular overlap products. -/
  | W16_CyclotomicPolynomialAndRectangularOverlapIdentities
  /-- `𝔚𝔊₁₇`: Rung 7 rectangular cross-overlap factorization $(R_+ L_-)(R_- L_+) = (1 + AC)(1 - AC + (AC)^2) = 1 + (AC)^3$. -/
  | W17_RectangularMoritaCrossOverlapIdentities
  /-- `𝔚𝔊₁₈`: Rung 8 Even Connes Spectral Triple $(\mathcal{A}, \mathcal{H}, \mathcal{D} = \Phi, \gamma = S_P)$ with $\{\mathcal{D}, \gamma\} = 0$ & $\mathcal{D}^2 = V$. -/
  | W18_EvenConnesSpectralTriple
  /-- `𝔚𝔊₁₉`: Rung 8 Connes 1-Form $d_{\mathcal{D}} P = [\Phi, P] = -J$, $(d_{\mathcal{D}} P)^2 = -V$, & Clifford Uncertainty Factorization $\mathcal{D}(d_{\mathcal{D}} P) = \Sigma$. -/
  | W19_ConnesOneFormCalculusAndUncertaintyBivector
  /-- `𝔚𝔊₂₀`: Rung 8 Inter-Sheet Connes Spectral Distance $d_{\mathcal{D}}(\lambda) = 1/\sqrt{\lambda} = \sqrt{2/(2\lambda)}$ & Cubic Bruhat Scaling. -/
  | W20_InterSheetConnesSpectralDistance
  /-- `𝔚𝔊₂₁`: Rung 8 Lorentzian Krein–Connes Horizon Signature Flip $-[\Phi(\theta), P]^2 = \cos(2\theta)V$ & Connes–Chern Cyclic Trace Identity $S_P \Phi[\Phi, P] = V$. -/
  | W21_LorentzianKreinConnesHorizonFlipAndChernIndex
  /-- `𝔚𝔊₂₂`: Ring-level anticommutation of the Peirce triad and its algebraic square identity. -/
  | W22_OrthogonalCliffordTriadAndLichnerowiczSquare
  /-- `𝔚𝔊₂₃`: Finite block trace-moment identities; no analytic spectral action or Nieh–Yan functional is constructed. -/
  | W23_ChamseddineConnesBosonicActionAndNiehYanDuality
  /-- `𝔚𝔊₂₄`: Conditional stationary-point identities for a defined quartic real potential; not a derivation of Einstein's field equations. -/
  | W24_Godel1949CosmologicalConstantVariationalLaw
  /-- `𝔚𝔊₂₅`: Algebraic horizon block identities and a conditional Schur-complement formula from an assumed partial-inverse equation. -/
  | W25_FermionicHorizonValveAndSchurComplement
  /-- `𝔚𝔊₂₆`: Rung 10 Centrality of the Incompleteness Metric $V \in Z(\mathcal{M})$ and Modular Uncertainty Derivation $[\Sigma, X] = V[S_P, X]$. -/
  | W26_CentralIncompletenessAndModularUncertaintyDerivation
  /-- `𝔚𝔊₂₇`: Rung 10 Tomita–Takesaki Polar Decomposition, Central Lichnerowicz Factor Cancellation, and Horizon Eigen-Operators $N_\pm$. -/
  | W27_TomitaTakesakiPolarDecompositionAndHorizonEigenOperators
  /-- `𝔚𝔊₂₈`: Rung 10 Connes–Rovelli KMS Thermal Time Orbit, Canonical Commutation Invariance, and Detailed Balance Trace Identity. -/
  | W28_ConnesRovelliKMSThermalTimeAndCyclotronicGeodesic
  /-- `𝔚𝔊₂₉`: Rung 10 Tolman–Hawking–Unruh Horizon Temperature Inversion $\beta_{\mathrm{eff}}(\theta) = \beta\cos(2\theta)$ and Torsion Condensate Peak $\lambda_* > 0$. -/
  | W29_TolmanHawkingUnruhHorizonTemperatureInversionAndTorsionPeak
  deriving DecidableEq, Repr

/-- Strict integer causal rank for the Wheeler–Gödel poset. -/
def stageRank : WheelerGodelStage → ℕ
  | .W1_SingleChartChronologyProtection => 1
  | .W2_HeisenbergVorticityCommutatorBridge => 2
  | .W3_LocalSpinFrameDraggingAndUncertainty => 3
  | .W4_HubbleAtlasChiralCancellation => 4
  | .W5_LawvereGodelMobiusDoubleCover => 5
  | .W6_MasterWheelerGodelSynthesis => 6
  | .W7_PeirceBogoliubovRenormalization => 7
  | .W8_GodelMetricCoordinateDictionary => 8
  | .W9_HubbleAtlasThreeTraceMomentsAndRung5 => 9
  | .W10_CyclotronicGeodesicAndNilpotentHorizon => 10
  | .W11_UnimodularBruhatConjugationAndChiralPair => 11
  | .W12_FiniteMatrixTraceEqualities => 12
  | .W13_SixPhaseRotorIdentitiesAndHorizonAnticommutator => 13
  | .W14_BichiralAnticommutatorAndMidpointCubicDefect => 14
  | .W15_BichiralCommutatorAndVorticityInterference => 15
  | .W16_CyclotomicPolynomialAndRectangularOverlapIdentities => 16
  | .W17_RectangularMoritaCrossOverlapIdentities => 17
  | .W18_EvenConnesSpectralTriple => 18
  | .W19_ConnesOneFormCalculusAndUncertaintyBivector => 19
  | .W20_InterSheetConnesSpectralDistance => 20
  | .W21_LorentzianKreinConnesHorizonFlipAndChernIndex => 21
  | .W22_OrthogonalCliffordTriadAndLichnerowiczSquare => 22
  | .W23_ChamseddineConnesBosonicActionAndNiehYanDuality => 23
  | .W24_Godel1949CosmologicalConstantVariationalLaw => 24
  | .W25_FermionicHorizonValveAndSchurComplement => 25
  | .W26_CentralIncompletenessAndModularUncertaintyDerivation => 26
  | .W27_TomitaTakesakiPolarDecompositionAndHorizonEigenOperators => 27
  | .W28_ConnesRovelliKMSThermalTimeAndCyclotronicGeodesic => 28
  | .W29_TolmanHawkingUnruhHorizonTemperatureInversionAndTorsionPeak => 29

/-- Direct covering edges of the Wheeler–Gödel causal poset: the initial spine
`𝔚𝔊₁ ≺ 𝔚𝔊₂ ≺ 𝔚𝔊₃`, the fork/join
`𝔚𝔊₃ ≺ {𝔚𝔊₄, 𝔚𝔊₅} ≺ 𝔚𝔊₆`, and the higher-order Rungs 5–10 continuation
`𝔚𝔊₆ ≺ ⋯ ≺ 𝔚𝔊₂₉`. Stages `𝔚𝔊₄` and `𝔚𝔊₅` are incomparable. -/
def causalEdge : WheelerGodelStage → WheelerGodelStage → Prop
  | .W1_SingleChartChronologyProtection, .W2_HeisenbergVorticityCommutatorBridge => True
  | .W2_HeisenbergVorticityCommutatorBridge, .W3_LocalSpinFrameDraggingAndUncertainty => True
  | .W3_LocalSpinFrameDraggingAndUncertainty, .W4_HubbleAtlasChiralCancellation => True
  | .W3_LocalSpinFrameDraggingAndUncertainty, .W5_LawvereGodelMobiusDoubleCover => True
  | .W4_HubbleAtlasChiralCancellation, .W6_MasterWheelerGodelSynthesis => True
  | .W5_LawvereGodelMobiusDoubleCover, .W6_MasterWheelerGodelSynthesis => True
  | .W6_MasterWheelerGodelSynthesis, .W7_PeirceBogoliubovRenormalization => True
  | .W7_PeirceBogoliubovRenormalization, .W8_GodelMetricCoordinateDictionary => True
  | .W8_GodelMetricCoordinateDictionary, .W9_HubbleAtlasThreeTraceMomentsAndRung5 => True
  | .W9_HubbleAtlasThreeTraceMomentsAndRung5, .W10_CyclotronicGeodesicAndNilpotentHorizon => True
  | .W10_CyclotronicGeodesicAndNilpotentHorizon, .W11_UnimodularBruhatConjugationAndChiralPair => True
  | .W11_UnimodularBruhatConjugationAndChiralPair, .W12_FiniteMatrixTraceEqualities => True
  | .W12_FiniteMatrixTraceEqualities, .W13_SixPhaseRotorIdentitiesAndHorizonAnticommutator => True
  | .W13_SixPhaseRotorIdentitiesAndHorizonAnticommutator, .W14_BichiralAnticommutatorAndMidpointCubicDefect => True
  | .W14_BichiralAnticommutatorAndMidpointCubicDefect, .W15_BichiralCommutatorAndVorticityInterference => True
  | .W15_BichiralCommutatorAndVorticityInterference, .W16_CyclotomicPolynomialAndRectangularOverlapIdentities => True
  | .W16_CyclotomicPolynomialAndRectangularOverlapIdentities, .W17_RectangularMoritaCrossOverlapIdentities => True
  | .W17_RectangularMoritaCrossOverlapIdentities, .W18_EvenConnesSpectralTriple => True
  | .W18_EvenConnesSpectralTriple, .W19_ConnesOneFormCalculusAndUncertaintyBivector => True
  | .W19_ConnesOneFormCalculusAndUncertaintyBivector, .W20_InterSheetConnesSpectralDistance => True
  | .W20_InterSheetConnesSpectralDistance, .W21_LorentzianKreinConnesHorizonFlipAndChernIndex => True
  | .W21_LorentzianKreinConnesHorizonFlipAndChernIndex, .W22_OrthogonalCliffordTriadAndLichnerowiczSquare => True
  | .W22_OrthogonalCliffordTriadAndLichnerowiczSquare, .W23_ChamseddineConnesBosonicActionAndNiehYanDuality => True
  | .W23_ChamseddineConnesBosonicActionAndNiehYanDuality, .W24_Godel1949CosmologicalConstantVariationalLaw => True
  | .W24_Godel1949CosmologicalConstantVariationalLaw, .W25_FermionicHorizonValveAndSchurComplement => True
  | .W25_FermionicHorizonValveAndSchurComplement, .W26_CentralIncompletenessAndModularUncertaintyDerivation => True
  | .W26_CentralIncompletenessAndModularUncertaintyDerivation, .W27_TomitaTakesakiPolarDecompositionAndHorizonEigenOperators => True
  | .W27_TomitaTakesakiPolarDecompositionAndHorizonEigenOperators, .W28_ConnesRovelliKMSThermalTimeAndCyclotronicGeodesic => True
  | .W28_ConnesRovelliKMSThermalTimeAndCyclotronicGeodesic, .W29_TolmanHawkingUnruhHorizonTemperatureInversionAndTorsionPeak => True
  | _, _ => False

instance : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue trivial | exact isFalse not_false

/-- **Native Mathlib Preorder Lyapunov Monotonicity (`strict_lyapunov_transGen_lt`)**:
In any causal transition relation `R : α → α → Prop` equipped with a strictly increasing
Lyapunov/time function `τ : α → γ` into any `Preorder γ` (`∀ x y, R x y → τ x < τ y`),
every multi-step causal path `Relation.TransGen R x y` strictly increases `τ`. -/
theorem strict_lyapunov_transGen_lt {α γ : Type*} [Preorder γ]
    {R : α → α → Prop} {τ : α → γ}
    (hstep : ∀ x y, R x y → τ x < τ y) {x y : α}
    (hpath : Relation.TransGen R x y) : τ x < τ y := by
  induction hpath with
  | single h => exact hstep _ _ h
  | tail _ hbc ih => exact lt_trans ih (hstep _ _ hbc)

/-- **Native Mathlib Preorder Chronology Protection Theorem (`strict_lyapunov_no_closed_timelike_curve`)**:
Over *any* `Preorder γ` (including `ℝ`, `ℚ`, `ℤ`, `ℕ`), if a single-chart causal relation
`R : α → α → Prop` admits a strict Lyapunov/time function `τ : α → γ` (`∀ x y, R x y → τ x < τ y`),
then no Closed Timelike Curve (`Relation.TransGen R x x`) can exist anywhere in `α`. -/
theorem strict_lyapunov_no_closed_timelike_curve {α γ : Type*} [Preorder γ]
    {R : α → α → Prop} {τ : α → γ}
    (hstep : ∀ x y, R x y → τ x < τ y) (x : α) :
    ¬ Relation.TransGen R x x := by
  intro hcycle
  exact lt_irrefl (τ x) (strict_lyapunov_transGen_lt hstep hcycle)

/-- **Native Mathlib Causal Asymmetry (`strict_lyapunov_transGen_asymm`)**:
Under a strict Lyapunov/time function `τ : α → γ`, no two events can lie on a mutual causal loop
(`Relation.TransGen R x y → ¬ Relation.TransGen R y x`). -/
theorem strict_lyapunov_transGen_asymm {α γ : Type*} [Preorder γ]
    {R : α → α → Prop} {τ : α → γ}
    (hstep : ∀ x y, R x y → τ x < τ y) {x y : α}
    (hxy : Relation.TransGen R x y) :
    ¬ Relation.TransGen R y x := by
  intro hyx
  exact strict_lyapunov_no_closed_timelike_curve hstep x (Relation.TransGen.trans hxy hyx)

/-- **General Integer-Rank Chronology Protection Lemma**: specialization of
`strict_lyapunov_transGen_lt` to `ℕ`. -/
theorem strict_rank_transGen_lt {α : Type*} {R : α → α → Prop} {τ : α → ℕ}
    (hstep : ∀ x y, R x y → τ x < τ y) {x y : α}
    (hpath : Relation.TransGen R x y) : τ x < τ y := by
  induction hpath with
  | single h => exact hstep _ _ h
  | tail _ hbc ih => exact lt_trans ih (hstep _ _ hbc)

/-- **General Integer-Rank Chronology Protection Theorem (No Closed Timelike Curves)**:
specialization of `strict_lyapunov_no_closed_timelike_curve` to `ℕ`. -/
theorem strict_rank_no_closed_timelike_curve {α : Type*} {R : α → α → Prop} {τ : α → ℕ}
    (hstep : ∀ x y, R x y → τ x < τ y) (x : α) :
    ¬ Relation.TransGen R x x := by
  intro hcycle
  exact lt_irrefl (τ x) (strict_rank_transGen_lt hstep hcycle)

/-- **Well-Foundedness of Any Strictly Ranked Causal Relation**:
Any causal relation `R` with a strict rank `τ : α → ℕ` is well-founded. -/
theorem strict_rank_wellFounded {α : Type*} {R : α → α → Prop} {τ : α → ℕ}
    (hstep : ∀ x y, R x y → τ x < τ y) :
    WellFounded R := by
  apply Subrelation.wf (r := InvImage (· < ·) τ)
  · intro x y h
    exact hstep x y h
  · exact InvImage.wf τ Nat.lt_wfRel.wf

/-- Every covering edge in `WheelerGodelStage` strictly increases `stageRank`. -/
theorem causalEdge_strict_rank {a b : WheelerGodelStage} (h : causalEdge a b) :
    stageRank a < stageRank b := by
  cases a <;> cases b <;> first | exact False.elim h | decide

/-- **Chronology Protection for `WheelerGodelStage`**: no stage can loop back to itself. -/
theorem causalEdge_acyclic (a : WheelerGodelStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro hcycle
  exact strict_rank_no_closed_timelike_curve (fun _ _ h => causalEdge_strict_rank h) a hcycle

/-- Reachability from Stage `𝔚𝔊₁` to Stage `𝔚𝔊₆`, plus the diamond fork/join
`𝔚𝔊₃ ≺ 𝔚𝔊₄ ≺ 𝔚𝔊₆` and `𝔚𝔊₃ ≺ 𝔚𝔊₅ ≺ 𝔚𝔊₆`. -/
theorem causalEdge_W1_to_W6 :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W6_MasterWheelerGodelSynthesis := by
  have h12 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W2_HeisenbergVorticityCommutatorBridge :=
    Relation.TransGen.single trivial
  have h13 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W3_LocalSpinFrameDraggingAndUncertainty :=
    Relation.TransGen.tail h12 trivial
  have h14 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W4_HubbleAtlasChiralCancellation :=
    Relation.TransGen.tail h13 trivial
  exact Relation.TransGen.tail h14 trivial

/-- Diamond fork/join witness: Stage `𝔚𝔊₃` branches into both `𝔚𝔊₄` (Quantum CTLs) and `𝔚𝔊₅`
(*Hubble Atlas* Isotropy), which both reconverge at `𝔚𝔊₆`. -/
theorem causalEdge_diamond_fork_join :
    causalEdge .W3_LocalSpinFrameDraggingAndUncertainty .W4_HubbleAtlasChiralCancellation ∧
    causalEdge .W3_LocalSpinFrameDraggingAndUncertainty .W5_LawvereGodelMobiusDoubleCover ∧
    causalEdge .W4_HubbleAtlasChiralCancellation .W6_MasterWheelerGodelSynthesis ∧
    causalEdge .W5_LawvereGodelMobiusDoubleCover .W6_MasterWheelerGodelSynthesis := by
  dsimp [causalEdge]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- The two branches at the Wheeler–Gödel diamond remain incomparable in the
transitive closure: there is no path from `WG₄` to `WG₅` or back. -/
theorem causalEdge_W4_W5_incomparable :
    ¬ Relation.TransGen causalEdge
        .W4_HubbleAtlasChiralCancellation .W5_LawvereGodelMobiusDoubleCover ∧
    ¬ Relation.TransGen causalEdge
        .W5_LawvereGodelMobiusDoubleCover .W4_HubbleAtlasChiralCancellation := by
  constructor
  · intro h
    cases h with
    | single edge =>
        simp [causalEdge] at edge
    | tail path edge =>
        have hpath := strict_rank_transGen_lt
          (fun _ _ h => causalEdge_strict_rank h) path
        have hedge := causalEdge_strict_rank edge
        simp [stageRank] at hpath hedge
        omega
  · intro h
    have hpath := strict_rank_transGen_lt
      (fun _ _ h => causalEdge_strict_rank h) h
    simp [stageRank] at hpath

/-- **Native Mathlib Row-Stochastic Matrix Mass Conservation (`stochastic_matrix_vecMul_sum`)**:
For any row-stochastic matrix `M : Matrix α β R` (`∀ i, ∑ j, M i j = 1`) over a commutative
semiring `R` and any row vector `u : α → R`, pushing `u` forward via `Matrix.vecMul u M`
conserves total mass:
$$\sum_{j \in \beta} (u \,{}_v\!\!* M)_j = \sum_{i \in \alpha} u_i$$ -/
theorem stochastic_matrix_vecMul_sum
    {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R]
    (M : Matrix α β R) (h_stoch : ∀ i : α, (∑ j : β, M i j) = 1) (u : α → R) :
    (∑ j : β, Matrix.vecMul u M j) = ∑ i : α, u i := by
  calc
    (∑ j : β, Matrix.vecMul u M j)
        = ∑ j : β, ∑ i : α, u i * M i j := by
          simp [Matrix.vecMul, dotProduct]
    _ = ∑ i : α, ∑ j : β, u i * M i j := Finset.sum_comm
    _ = ∑ i : α, u i * (∑ j : β, M i j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.mul_sum]
    _ = ∑ i : α, u i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [h_stoch i, mul_one]

/-- **Native Mathlib Row-Stochastic Matrix $\ell_1$-Contraction (`stochastic_matrix_vecMul_l1_contraction`)**:
For any row-stochastic matrix `M : Matrix α β ℝ` (`∀ i j, 0 ≤ M i j` and `∀ i, ∑ j, M i j = 1`)
and any vectors `u v : α → ℝ`, the native Mathlib matrix-vector action `Matrix.vecMul`
monotonically contracts $\ell_1$ distance:
$$\sum_{j \in \beta} |(u \,{}_v\!\!* M)_j - (v \,{}_v\!\!* M)_j| \le \sum_{i \in \alpha} |u_i - v_i|$$ -/
theorem stochastic_matrix_vecMul_l1_contraction
    {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ)
    (h_nonneg : ∀ i j, 0 ≤ M i j)
    (h_stoch : ∀ i : α, (∑ j : β, M i j) = 1)
    (u v : α → ℝ) :
    (∑ j : β, |Matrix.vecMul u M j - Matrix.vecMul v M j|) ≤ ∑ i : α, |u i - v i| := by
  have hpoint : ∀ j : β,
      |Matrix.vecMul u M j - Matrix.vecMul v M j| ≤ ∑ i : α, |u i - v i| * M i j := by
    intro j
    have hsub : Matrix.vecMul u M j - Matrix.vecMul v M j =
        ∑ i : α, (u i - v i) * M i j := by
      simp only [Matrix.vecMul, dotProduct, ← Finset.sum_sub_distrib, sub_mul]
    rw [hsub]
    calc
      |∑ i : α, (u i - v i) * M i j|
          ≤ ∑ i : α, |(u i - v i) * M i j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : α, |u i - v i| * M i j := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [abs_mul, abs_of_nonneg (h_nonneg i j)]
  calc
    (∑ j : β, |Matrix.vecMul u M j - Matrix.vecMul v M j|)
        ≤ ∑ j : β, ∑ i : α, |u i - v i| * M i j :=
          Finset.sum_le_sum (fun j _ => hpoint j)
    _ = ∑ i : α, ∑ j : β, |u i - v i| * M i j := Finset.sum_comm
    _ = ∑ i : α, |u i - v i| * (∑ j : β, M i j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.mul_sum]
    _ = ∑ i : α, |u i - v i| := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [h_stoch i, mul_one]

/-- **Stage `𝔚𝔊₁` Theorem (Single-Chart Thermodynamic Contraction & Chronology Protection)**:
Unifies native Mathlib row-stochastic $\ell_1$-contraction (`stochastic_matrix_vecMul_l1_contraction`),
Pillar I of Wheeler's Ouroboros (`markov_tv_contraction`), and single-chart Chronology Protection
(`causalEdge_acyclic`). -/
theorem archetype_W1_single_chart_chronology_protection
    {A_alph B_alph : Type*} [Fintype A_alph] [Fintype B_alph]
    (K : MarkovKernel A_alph B_alph) (P Q : ProbDist A_alph) :
    distTV (pushforward K P) (pushforward K Q) ≤ distTV P Q ∧
    (∀ u v : A_alph → ℝ,
      (∑ b : B_alph, |Matrix.vecMul u K.T b - Matrix.vecMul v K.T b|) ≤
        ∑ a : A_alph, |u a - v a|) ∧
    (∀ s : WheelerGodelStage, ¬ Relation.TransGen causalEdge s s) := by
  refine ⟨markov_tv_contraction K P Q, ?_, ?_⟩
  · intro u v
    exact stochastic_matrix_vecMul_l1_contraction K.T K.nonneg K.sum_one u v
  · intro s
    exact causalEdge_acyclic s

/-! ## §2. Stages `𝔚𝔊₁`–`𝔚𝔊₃`: Gödel Incompleteness Defect, Complementary Chart Uncertainty & The Wheeler–Gödel Equivalence Theorem -/

section NativeWheelerGodelPeirceRing

variable {R : Type*} [Ring R]

/-- Primal syntactic assertion $N_+(P, A) := P A (1 - P)$ crossing from the unprovable
complement $1 - P$ into the provable interior $P$. -/
abbrev peircePlus (P A : R) : R := conePlus P A

/-- Dual semantic refutation $N_-(P, B) := (1 - P) B P$ crossing from the provable interior $P$
into the unprovable complement $1 - P$. -/
abbrev peirceMinus (P B : R) : R := coneMinus P B

/-- Self-referential **Gödel Diagonalization Sentence** $\Phi(P, A, B) := N_+(P, A) + N_-(P, B)$
(the symmetric Maurer–Cartan solder form). -/
abbrev solderPhi (P A B : R) : R := genPhi P A B

/-- Timelike worldline solder form $J(P, A, B) := N_+(P, A) - N_-(P, B)$. -/
abbrev solderJ (P A B : R) : R := genJ P A B

/-- Chiral grading involution $S_P := 2P - 1$. -/
abbrev chiralInv (P : R) : R := invS P

/-- **Heisenberg Uncertainty / Cosmic Spin-Rotation Commutator**
$\Sigma(P, A, B) := [N_+(P, A), N_-(P, B)] = Q_+ - Q_-$. -/
abbrev spinVorticity (P A B : R) : R := genSig P A B

/-- **Gödel Incompleteness Defect / Operator Fisher Metric**
$V(P, A, B) := \{N_+(P, A), N_-(P, B)\} = Q_+ + Q_-$. -/
abbrev fisherMetricOp (P A B : R) : R := genV P A B

/-- Clockwise chiral galaxy sheet operator $Q_+(P, A, B) := N_+(P, A) N_-(P, B)$. -/
def sheetPlus (P A B : R) : R := peircePlus P A * peirceMinus P B

/-- Counterclockwise chiral galaxy sheet operator $Q_-(P, A, B) := N_-(P, B) N_+(P, A)$. -/
def sheetMinus (P A B : R) : R := peirceMinus P B * peircePlus P A

/-- Primal syntactic chart projector $P_+(P, A) := P + N_+(P, A)$. -/
def primalChart (P A : R) : R := P + peircePlus P A

/-- Dual semantic chart projector $P_-(P, B) := P + N_-(P, B)$. -/
def dualChart (P B : R) : R := P + peirceMinus P B

/-- **Nilpotency of the Chiral Peirce Shifts (`peircePlus_and_peirceMinus_sq_zero`)**:
For any `IsIdempotentElem P` (`P * P = P`), $N_+^2 = 0$ and $N_-^2 = 0$. -/
theorem peircePlus_and_peirceMinus_sq_zero {P : R} (hP : IsIdempotentElem P) (A B : R) :
    peircePlus P A * peircePlus P A = 0 ∧
    peirceMinus P B * peirceMinus P B = 0 := by
  have hP2 : P * P = P := hP
  exact ⟨by peirce_nf hP2, by peirce_nf hP2⟩

/-- **Stage `𝔚𝔊₁` Core Theorem — The Gödel Incompleteness Idempotent Defect (`godel_incompleteness_idempotent_defect`)**:
Attempting to annex the self-referential Gödel sentence $\Phi = N_+ + N_-$ to the consistent
idempotent axiom system $P^2 = P$ yields the irreducible **Incompleteness Defect** $V = \{N_+, N_-\}$:
1. $P\Phi + \Phi P = \Phi$,
2. $(P + \Phi)^2 - (P + \Phi) = \Phi^2 = V$,
3. **Completeness Criterion**: $(P + \Phi)^2 = P + \Phi \iff V = 0$. -/
theorem godel_incompleteness_idempotent_defect {P : R} (hP : IsIdempotentElem P) (A B : R) :
    P * solderPhi P A B + solderPhi P A B * P = solderPhi P A B ∧
    (P + solderPhi P A B) * (P + solderPhi P A B) - (P + solderPhi P A B) =
      solderPhi P A B * solderPhi P A B ∧
    (P + solderPhi P A B) * (P + solderPhi P A B) - (P + solderPhi P A B) =
      fisherMetricOp P A B ∧
    ((P + solderPhi P A B) * (P + solderPhi P A B) = P + solderPhi P A B ↔
      fisherMetricOp P A B = 0) := by
  have hP2 : P * P = P := hP
  have h1 : P * solderPhi P A B + solderPhi P A B * P = solderPhi P A B := by peirce_nf hP2
  have h2 : (P + solderPhi P A B) * (P + solderPhi P A B) - (P + solderPhi P A B) =
      solderPhi P A B * solderPhi P A B := by peirce_nf hP2
  have h3 : (P + solderPhi P A B) * (P + solderPhi P A B) - (P + solderPhi P A B) =
      fisherMetricOp P A B := by peirce_nf hP2
  refine ⟨h1, h2, h3, ?_⟩
  rw [← sub_eq_zero, h3]

/-- Counterterm-dressed Gödel state. The subtraction uses the same ring
operations and Peirce data as `solderPhi` and `spinVorticity`; no analytic
normalization or square root is part of this definition. -/
def uncertaintyDressedGodelState (P A B : R) : R :=
  P + solderPhi P A B - spinVorticity P A B

/-- The associative ring Lie bracket `⁅x, y⁆` coincides with the Peirce commutator `comm x y`. -/
lemma lie_eq_peirce_comm (x y : R) : ⁅x, y⁆ = comm x y := by
  rw [Ring.lie_def, OperatorAlgebra.PeirceSpine.comm]

/-- The spin-vorticity element `spinVorticity P A B` is the Lie bracket of the off-diagonal
Peirce corners `peircePlus P A` and `peirceMinus P B`. -/
lemma spinVorticity_eq_lie (P A B : R) :
    spinVorticity P A B = ⁅peircePlus P A, peirceMinus P B⁆ := by
  rw [spinVorticity, genSig, lie_eq_peirce_comm, peircePlus, peirceMinus]

/-- **Peirce counterterm identity (higher-order Wheeler–Gödel continuation).**
For an idempotent `P`, the vorticity `Σ` anticommutes with the solder form `Φ`,
its Jordan defect against `P` is the Fisher defect `V`, and subtracting `Σ`
from the incomplete state `P + Φ` leaves precisely the quadratic residual
`Σ² = V²`:

`{Σ, Φ} = 0`, `{P, Σ} - Σ = V`, and
`(P + Φ - Σ)² - (P + Φ - Σ) = Σ² = V²`.

This is an associative-ring identity. It does not assert that the dressed
state is idempotent unless the additional condition `V² = 0` holds. -/
theorem heisenberg_counterterm_idempotent_defect
    {P : R} (hP : IsIdempotentElem P) (A B : R) :
    spinVorticity P A B * solderPhi P A B +
        solderPhi P A B * spinVorticity P A B = 0 ∧
    P * spinVorticity P A B + spinVorticity P A B * P -
        spinVorticity P A B = fisherMetricOp P A B ∧
    uncertaintyDressedGodelState P A B * uncertaintyDressedGodelState P A B -
        uncertaintyDressedGodelState P A B =
      spinVorticity P A B * spinVorticity P A B ∧
    spinVorticity P A B * spinVorticity P A B =
      fisherMetricOp P A B * fisherMetricOp P A B := by
  have hP2 : P * P = P := hP
  refine ⟨by peirce_nf hP2, by peirce_nf hP2, ?_, by peirce_nf hP2⟩
  dsimp [uncertaintyDressedGodelState]
  peirce_nf hP2

/-! ### A concrete normalized meta-projector example

The proposed expression involving `(1 + 4V)⁻¹/²` is not a theorem in an arbitrary ring:
the inverse square root requires extra scalar/analytic structure, and idempotency also
requires the relevant commutation laws. The following finite-dimensional real matrix
example records exactly one valid instance, with `A = B = 1`, for which `V = I` and
`(S_P + 2Φ)^2 = 5I`. It is not an all-orders construction of an inductive algebra tower. -/

/-- Concrete `2 × 2` real normalized meta-projector `½(I + (S_P + 2Φ)/√5)` for `A = B = 1`. -/
noncomputable def concreteNormalizedMetaProjector : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ (1 + 1 / Real.sqrt 5) / 2, 1 / Real.sqrt 5;
     1 / Real.sqrt 5, (1 - 1 / Real.sqrt 5) / 2 ]

/-- The displayed real `2 × 2` normalized matrix is idempotent. This is a concrete
finite-matrix witness, not a general normalization theorem for Peirce rings. -/
theorem concreteNormalizedMetaProjector_idempotent :
    concreteNormalizedMetaProjector * concreteNormalizedMetaProjector =
      concreteNormalizedMetaProjector := by
  have hs : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [concreteNormalizedMetaProjector, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp [hs0] <;> nlinarith [hs]

/-- The counterterm-dressed state is idempotent exactly when its residual
second-order defect vanishes. This equivalence makes explicit the extra
condition needed for an actual meta-projector; the counterterm alone does not
guarantee idempotence. -/
theorem uncertaintyDressedGodelState_idempotent_iff
    {P : R} (hP : IsIdempotentElem P) (A B : R) :
    IsIdempotentElem (uncertaintyDressedGodelState P A B) ↔
      fisherMetricOp P A B * fisherMetricOp P A B = 0 := by
  have hdef := (heisenberg_counterterm_idempotent_defect hP A B).2.2.1
  have hsq := (heisenberg_counterterm_idempotent_defect hP A B).2.2.2
  change uncertaintyDressedGodelState P A B * uncertaintyDressedGodelState P A B =
    uncertaintyDressedGodelState P A B ↔ _
  rw [← sub_eq_zero, hdef, hsq]

/-- The chiral Jordan-triple correction `V * N₊` applied after the first
Heisenberg correction. -/
def bruhatRenormalizedGodelState (P A B : R) : R :=
  uncertaintyDressedGodelState P A B - fisherMetricOp P A B * peircePlus P A

/-- Exact second-step Peirce renormalization. The square-zero chiral correction
`T = V N₊` has zero relative Peirce defect, anticommutes with `Σ`, and has
anticommutator `V²` with `Φ`; it therefore cancels the residual defect of the
Heisenberg-dressed state and yields an idempotent over an arbitrary ring. -/
theorem jordan_triple_counterterm_idempotent
    {P : R} (hP : IsIdempotentElem P) (A B : R) :
    (fisherMetricOp P A B * peircePlus P A) *
        (fisherMetricOp P A B * peircePlus P A) = 0 ∧
    P * (fisherMetricOp P A B * peircePlus P A) +
        (fisherMetricOp P A B * peircePlus P A) * P -
        (fisherMetricOp P A B * peircePlus P A) = 0 ∧
    spinVorticity P A B * (fisherMetricOp P A B * peircePlus P A) +
        (fisherMetricOp P A B * peircePlus P A) * spinVorticity P A B = 0 ∧
    solderPhi P A B * (fisherMetricOp P A B * peircePlus P A) +
        (fisherMetricOp P A B * peircePlus P A) * solderPhi P A B =
      fisherMetricOp P A B * fisherMetricOp P A B ∧
    bruhatRenormalizedGodelState P A B * bruhatRenormalizedGodelState P A B =
      bruhatRenormalizedGodelState P A B := by
  have hP2 : P * P = P := hP
  refine ⟨by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2,
    by peirce_nf hP2, ?_⟩
  dsimp [bruhatRenormalizedGodelState, uncertaintyDressedGodelState]
  peirce_nf hP2

/-- Opposite-order unipotent Peirce gates. Their polynomial inverses are
recorded separately below; no determinant or scalar division is used. -/
def bruhatGaugePlus (P A B : R) : R :=
  (1 - peircePlus P A) * (1 + peirceMinus P B)

/-- Lower-first unipotent Bruhat gauge factor `(1 + N₋)(1 - N₊)`. -/
def bruhatGaugeMinus (P A B : R) : R :=
  (1 + peirceMinus P B) * (1 - peircePlus P A)

/-- Two-sided polynomial inverse `(1 - N₋)(1 + N₊)` of `bruhatGaugePlus`. -/
def bruhatGaugePlusInv (P A B : R) : R :=
  (1 - peirceMinus P B) * (1 + peircePlus P A)

/-- Two-sided polynomial inverse `(1 + N₊)(1 - N₋)` of `bruhatGaugeMinus`. -/
def bruhatGaugeMinusInv (P A B : R) : R :=
  (1 + peircePlus P A) * (1 - peirceMinus P B)

/-- The opposite chiral cubic correction `V N₋`. -/
def bruhatRenormalizedGodelStateMinus (P A B : R) : R :=
  uncertaintyDressedGodelState P A B - fisherMetricOp P A B * peirceMinus P B

/-- **Bruhat conjugation theorem (Rung 6, `WG₁₁`).**

For any idempotent in an associative ring, the two opposite-order products of
Peirce transvections have explicit two-sided polynomial inverses. Conjugating
the idempotent by them yields the two cubic-corrected states; both are
idempotent and their difference is `V J`. This proves algebraic invertibility,
not a determinant-one or K-theoretic statement on an arbitrary ring. -/
theorem bruhat_conjugation_chiral_pair
    {P : R} (hP : IsIdempotentElem P) (A B : R) :
    bruhatGaugePlus P A B * bruhatGaugePlusInv P A B = 1 ∧
    bruhatGaugePlusInv P A B * bruhatGaugePlus P A B = 1 ∧
    bruhatGaugeMinus P A B * bruhatGaugeMinusInv P A B = 1 ∧
    bruhatGaugeMinusInv P A B * bruhatGaugeMinus P A B = 1 ∧
    bruhatGaugePlus P A B * P * bruhatGaugePlusInv P A B =
      bruhatRenormalizedGodelState P A B ∧
    bruhatGaugeMinus P A B * P * bruhatGaugeMinusInv P A B =
      bruhatRenormalizedGodelStateMinus P A B ∧
    IsIdempotentElem (bruhatRenormalizedGodelState P A B) ∧
    IsIdempotentElem (bruhatRenormalizedGodelStateMinus P A B) := by
  have hP2 : P * P = P := hP
  have hconjMinus : bruhatGaugeMinus P A B * P * bruhatGaugeMinusInv P A B =
      bruhatRenormalizedGodelStateMinus P A B := by
    dsimp [bruhatGaugeMinus, bruhatGaugeMinusInv, bruhatRenormalizedGodelStateMinus,
      uncertaintyDressedGodelState]
    peirce_nf hP2
  have hminusRight : bruhatGaugeMinusInv P A B * bruhatGaugeMinus P A B = 1 := by
    dsimp [bruhatGaugeMinus, bruhatGaugeMinusInv]
    peirce_nf hP2
  have hminusIdem : IsIdempotentElem (bruhatRenormalizedGodelStateMinus P A B) := by
    change bruhatRenormalizedGodelStateMinus P A B *
      bruhatRenormalizedGodelStateMinus P A B = bruhatRenormalizedGodelStateMinus P A B
    calc
      bruhatRenormalizedGodelStateMinus P A B * bruhatRenormalizedGodelStateMinus P A B =
          (bruhatGaugeMinus P A B * P * bruhatGaugeMinusInv P A B) *
            (bruhatGaugeMinus P A B * P * bruhatGaugeMinusInv P A B) := by rw [hconjMinus]
      _ = bruhatGaugeMinus P A B * P *
            (bruhatGaugeMinusInv P A B * bruhatGaugeMinus P A B) * P *
              bruhatGaugeMinusInv P A B := by noncomm_ring
      _ = bruhatGaugeMinus P A B * P * P * bruhatGaugeMinusInv P A B := by
        rw [hminusRight]
        simp only [mul_one]
      _ = bruhatGaugeMinus P A B * P * bruhatGaugeMinusInv P A B := by
        calc
          bruhatGaugeMinus P A B * P * P * bruhatGaugeMinusInv P A B =
              bruhatGaugeMinus P A B * (P * P) * bruhatGaugeMinusInv P A B := by noncomm_ring
          _ = bruhatGaugeMinus P A B * P * bruhatGaugeMinusInv P A B := by rw [hP2]
      _ = bruhatRenormalizedGodelStateMinus P A B := hconjMinus
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [bruhatGaugePlus, bruhatGaugePlusInv]
    peirce_nf hP2
  · dsimp [bruhatGaugePlus, bruhatGaugePlusInv]
    peirce_nf hP2
  · dsimp [bruhatGaugeMinus, bruhatGaugeMinusInv]
    peirce_nf hP2
  · dsimp [bruhatGaugeMinus, bruhatGaugeMinusInv]
    peirce_nf hP2
  · dsimp [bruhatGaugePlus, bruhatGaugePlusInv, bruhatRenormalizedGodelState,
      uncertaintyDressedGodelState]
    peirce_nf hP2
  · exact hconjMinus
  · change bruhatRenormalizedGodelState P A B * bruhatRenormalizedGodelState P A B =
      bruhatRenormalizedGodelState P A B
    exact (jordan_triple_counterterm_idempotent hP A B).2.2.2.2
  · exact hminusIdem

/-- **Stage `𝔚𝔊₂` Core Theorem — Complementary Chart Non-Commutativity (`complementary_chart_commutator_identity`)**:
1. The primal chart $P_+(A) = P + N_+$ and dual chart $P_-(B) = P + N_-$ are individually
   consistent idempotent projections: $P_+^2 = P_+$ and $P_-^2 = P_-$,
2. Their native Mathlib Lie commutator is:
   $$⁅P_+(A), P_-(B)⁆ = \Sigma - \Phi$$
3. And the commutator of the off-diagonal assertions is the Heisenberg uncertainty operator:
   $$⁅N_+, N_-⁆ = \Sigma = Q_+ - Q_-$$ -/
theorem complementary_chart_commutator_identity {P : R} (hP : IsIdempotentElem P) (A B : R) :
    primalChart P A * primalChart P A = primalChart P A ∧
    dualChart P B * dualChart P B = dualChart P B ∧
    ⁅primalChart P A, dualChart P B⁆ = spinVorticity P A B - solderPhi P A B ∧
    ⁅peircePlus P A, peirceMinus P B⁆ = sheetPlus P A B - sheetMinus P A B := by
  have hP2 : P * P = P := hP
  dsimp [primalChart, dualChart, sheetPlus, sheetMinus]
  rw [lie_eq_peirce_comm, lie_eq_peirce_comm]
  refine ⟨by peirce_nf hP2, by peirce_nf hP2,
    by peirce_nf hP2, rfl⟩

/-- **Theorem 1 (`wheeler_godel_equivalence_theorem` — Stage `𝔚𝔊₃`):
The Exact Wheeler–Gödel Equivalence Theorem (Incompleteness $\Longleftrightarrow$ Uncertainty)**:
Over **every** associative ring `[Ring R]` with idempotent axiom projector `hP : IsIdempotentElem P`:
1. **Para-Kähler Creation Lock**:
   $$S_P\,\Sigma = V, \qquad S_P\,V = \Sigma$$
2. **Defect–Uncertainty Equivalence**:
   $$V = 0 \;\Longleftrightarrow\; \Sigma = 0$$
3. **Wheeler's Question Answered (`Completeness ⟺ Determinism`)**:
   The extended Gödel system $P + \Phi$ is idempotently complete ($(P + \Phi)^2 = P + \Phi$)
   **if and only if** the complementary chiral shifts commute ($⁅N_+, N_-⁆ = 0$):
   $$\boxed{(P + \Phi) * (P + \Phi) = P + \Phi \;\Longleftrightarrow\; ⁅N_+, N_-⁆ = 0}$$ -/
theorem wheeler_godel_equivalence_theorem {P : R} (hP : IsIdempotentElem P) (A B : R) :
    chiralInv P * spinVorticity P A B = fisherMetricOp P A B ∧
    chiralInv P * fisherMetricOp P A B = spinVorticity P A B ∧
    (fisherMetricOp P A B = 0 ↔ spinVorticity P A B = 0) ∧
    ((P + solderPhi P A B) * (P + solderPhi P A B) = P + solderPhi P A B ↔
      ⁅peircePlus P A, peirceMinus P B⁆ = 0) := by
  have hP2 : P * P = P := hP
  have hE3 := archetype_E3_para_kahler_lock_and_levi_civita_aporia hP2 A B
  have hDef := (godel_incompleteness_idempotent_defect hP A B).2.2.2
  have hVSig : fisherMetricOp P A B = 0 ↔ spinVorticity P A B = 0 := hE3.2.2.2.2.1.symm
  refine ⟨hE3.1, hE3.2.2.1, hVSig, ?_⟩
  rw [hDef, hVSig, spinVorticity_eq_lie]

/-- **Native Mathlib Lie-Bracket Identity for Conjugate Solder Forms**:
1. `⁅solderPhi P A B, solderJ P A B⁆ = -((2 : ℤ) • spinVorticity P A B)`,
2. `chiralInv P * ⁅solderPhi P A B, solderJ P A B⁆ = -((2 : ℤ) • fisherMetricOp P A B)`. -/
theorem native_heisenberg_vorticity_lie_bracket {P : R} (hP : IsIdempotentElem P) (A B : R) :
    ⁅solderPhi P A B, solderJ P A B⁆ = -((2 : ℤ) • spinVorticity P A B) ∧
    chiralInv P * ⁅solderPhi P A B, solderJ P A B⁆ = -((2 : ℤ) • fisherMetricOp P A B) := by
  have hP2 : P * P = P := hP
  rw [lie_eq_peirce_comm]
  exact ⟨by peirce_nf hP2, by peirce_nf hP2⟩

/-- **Stage `𝔚𝔊₂`–`𝔚𝔊₃` Bridge Theorem (`archetype_W2_wheeler_godel_heisenberg_commutator_bridge`)**:
Combines the conjugate solder commutator $[\Phi, J] = -2\Sigma$, the Chiral Einstein Anomaly
$S_P[\Phi, J] = -2V$, the Levi-Civita commutativity aporia, and the unconditional
Wheeler–Gödel equivalence $(P + \Phi)^2 = P + \Phi \iff ⁅N_+, N_-⁆ = 0$. -/
theorem archetype_W2_wheeler_godel_heisenberg_commutator_bridge
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) :
    OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) =
      -((2 : ℤ) • genSig P A C) ∧
    chiralEinsteinAnomaly P A C = -((2 : ℤ) • genV P A C) ∧
    (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) = 0 →
      (2 : ℤ) • genSig P A C = 0 ∧ (2 : ℤ) • genV P A C = 0) ∧
    ⁅solderPhi P A C, solderJ P A C⁆ = -((2 : ℤ) • spinVorticity P A C) ∧
    ((P + solderPhi P A C) * (P + solderPhi P A C) = P + solderPhi P A C ↔
      ⁅peircePlus P A, peirceMinus P C⁆ = 0) := by
  have hE3 := archetype_E3_para_kahler_lock_and_levi_civita_aporia hP A C
  have hE4 := archetype_E4_chiral_einstein_anomaly_cocycle hP A C
  have hNat := (native_heisenberg_vorticity_lie_bracket (P := P) hP A C).1
  have hWG3 := (wheeler_godel_equivalence_theorem (P := P) hP A C).2.2.2
  exact ⟨hE4.1, hE4.2.1, hE3.2.2.2.2.2.2, hNat, hWG3⟩

/-- **Corollary (Non-Zero Gödel Rotation Forces Heisenberg Non-Commutativity)**:
Whenever $(2 : \mathbb{Z}) \bullet \mathrm{genSig}\;P\;A\;C \neq 0$, the conjugate solder forms
cannot commute. -/
theorem godel_vorticity_forces_heisenberg_noncommutativity
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)
    (hrot : (2 : ℤ) • genSig P A C ≠ 0) :
    OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) ≠ 0 := by
  intro hcomm
  have hkill := (archetype_W2_wheeler_godel_heisenberg_commutator_bridge hP A C).2.2.1 hcomm
  exact hrot hkill.1

/-! ## §3. Stage `𝔚𝔊₄`: Quantum Closed Timelike Lines ($\Phi(\theta)^2 = \cos(2\theta)V$), Inductive Frame Dragging & Robertson–Schrödinger Uncertainty -/

/-- **Algebraic Transmutation of a Spacelike Loop into a Closed Timelike Line
(`spacelike_to_closed_timelike_line_algebraic`)**:
Over any associative ring `[Ring R]` with `IsIdempotentElem P`:
1. **Spacelike Coordinate Circle**: $\Phi^2 = +V$,
2. **Timelike Worldline**: $J^2 = -V$,
3. **Orthogonality**: $\Phi J + J \Phi = 0$,
4. **Spin-Rotation Action**: $\Sigma \Phi = V J$,
5. **Closed Timelike Line Square**:
   $$(\Sigma \Phi)^2 = (V J)^2 = -(V^3)$$ -/
theorem spacelike_to_closed_timelike_line_algebraic {P : R} (hP : IsIdempotentElem P) (A B : R) :
    solderPhi P A B * solderPhi P A B = fisherMetricOp P A B ∧
    solderJ P A B * solderJ P A B = -fisherMetricOp P A B ∧
    solderPhi P A B * solderJ P A B + solderJ P A B * solderPhi P A B = 0 ∧
    spinVorticity P A B * solderPhi P A B = fisherMetricOp P A B * solderJ P A B ∧
    (spinVorticity P A B * solderPhi P A B) * (spinVorticity P A B * solderPhi P A B) =
      -(fisherMetricOp P A B * fisherMetricOp P A B * fisherMetricOp P A B) := by
  have hP2 : P * P = P := hP
  refine ⟨by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2,
          gemSpinMulPhi_eq hP2 A B, gemNilpotentCollapse hP2 A B⟩

/-- **Continuous Spin-Rotated Solder Loop $\Phi(\theta) := \cos\theta\,\Phi + \sin\theta\,J$**:
Over any real operator algebra `[Ring R] [Module ℝ R]`, rotates the spacelike loop $\Phi$ into
the timelike loop $J$ as $\theta$ varies from $0$ to $\pi/2$. -/
noncomputable def rotatedSolderLoop [Module ℝ R] (P A B : R) (θ : ℝ) : R :=
  Real.cos θ • solderPhi P A B + Real.sin θ • solderJ P A B

/-- **Chiral Spin Rotor $R(\theta) := \cos\theta\,I + \sin\theta\,S_P$**. -/
noncomputable def chiralSpinRotor [Module ℝ R] (P : R) (θ : ℝ) : R :=
  Real.cos θ • (1 : R) + Real.sin θ • chiralInv P

/-- **Theorem 2a (`rotatedSolderLoop_sq_and_critical_angles` — Stage `𝔚𝔊₄`):
Continuous Transmutation of a Spacelike Circle into a Closed Timelike Line**:
Over any real algebra `[Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]`
with `IsIdempotentElem P`:
1. **Rotor Action**: $R(\theta)\,\Phi = \Phi(\theta) = \cos\theta\,\Phi + \sin\theta\,J$,
2. **Exact Cosine-Double-Angle Metric Law**:
   $$\boxed{\Phi(\theta) * \Phi(\theta) = \cos(2\theta) \bullet V}$$
3. **At $\theta = 0$ (Spacelike Circle)**:
   $\Phi(0) = \Phi$ and $\Phi(0)^2 = +V$,
4. **At $\theta = \pi / 4$ (Critical Gödel Null Horizon)**:
   $\Phi(\pi / 4)^2 = 0$,
5. **At $\theta = \pi / 2$ (Closed Timelike Line)**:
   $\Phi(\pi / 2) = J$ and $\Phi(\pi / 2)^2 = -V$. -/
theorem rotatedSolderLoop_sq_and_critical_angles
    [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) (θ : ℝ) :
    chiralSpinRotor P θ * solderPhi P A B = rotatedSolderLoop P A B θ ∧
    rotatedSolderLoop P A B θ * rotatedSolderLoop P A B θ =
      Real.cos (2 * θ) • fisherMetricOp P A B ∧
    rotatedSolderLoop P A B 0 = solderPhi P A B ∧
    rotatedSolderLoop P A B 0 * rotatedSolderLoop P A B 0 = fisherMetricOp P A B ∧
    rotatedSolderLoop P A B (Real.pi / 4) * rotatedSolderLoop P A B (Real.pi / 4) = 0 ∧
    rotatedSolderLoop P A B (Real.pi / 2) = solderJ P A B ∧
    rotatedSolderLoop P A B (Real.pi / 2) * rotatedSolderLoop P A B (Real.pi / 2) =
      -fisherMetricOp P A B := by
  have hP2 : P * P = P := hP
  have hAlg := spacelike_to_closed_timelike_line_algebraic hP A B
  have hSP_Phi : chiralInv P * solderPhi P A B = solderJ P A B := by peirce_nf hP2
  have hRotor : chiralSpinRotor P θ * solderPhi P A B = rotatedSolderLoop P A B θ := by
    dsimp [chiralSpinRotor, rotatedSolderLoop]
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hSP_Phi]
  have hSqAll (θ' : ℝ) : rotatedSolderLoop P A B θ' * rotatedSolderLoop P A B θ' =
      Real.cos (2 * θ') • fisherMetricOp P A B := by
    dsimp [rotatedSolderLoop]
    rw [add_mul, mul_add, mul_add,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      hAlg.1, hAlg.2.1, mul_comm (Real.sin θ') (Real.cos θ'),
      ← add_assoc, add_assoc ((Real.cos θ' * Real.cos θ') • fisherMetricOp P A B),
      ← smul_add, hAlg.2.2.1, smul_zero, add_zero,
      smul_neg, ← sub_eq_add_neg, ← sub_smul,
      ← sq, ← sq, ← Real.cos_two_mul']
  have hSq := hSqAll θ
  have h0_loop : rotatedSolderLoop P A B 0 = solderPhi P A B := by
    simp [rotatedSolderLoop]
  have h0_sq : rotatedSolderLoop P A B 0 * rotatedSolderLoop P A B 0 = fisherMetricOp P A B := by
    rw [h0_loop, hAlg.1]
  have hpi4_sq : rotatedSolderLoop P A B (Real.pi / 4) * rotatedSolderLoop P A B (Real.pi / 4) = 0 := by
    rw [hSqAll, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
      Real.cos_pi_div_two, zero_smul]
  have hpi2_loop : rotatedSolderLoop P A B (Real.pi / 2) = solderJ P A B := by
    simp [rotatedSolderLoop]
  have hpi2_sq : rotatedSolderLoop P A B (Real.pi / 2) * rotatedSolderLoop P A B (Real.pi / 2) =
      -fisherMetricOp P A B := by
    rw [hpi2_loop, hAlg.2.1]
  exact ⟨hRotor, hSq, h0_loop, h0_sq, hpi4_sq, hpi2_loop, hpi2_sq⟩

/-- The angular coefficient in the scale-one Gödel rotating metric, using the
convention `ds² = ... + godelAzimuthalCoefficient r * dφ² + ...`. -/
noncomputable def godelAzimuthalCoefficient (r : ℝ) : ℝ :=
  Real.sinh r ^ 2 * (1 - Real.sinh r ^ 2)

/-- The positive Gödel chronology radius, defined as the inverse hyperbolic
sine of `1`. -/
noncomputable def godelCriticalRadius : ℝ := Real.arsinh 1

/-- The hyperbolic sine of the critical Gödel chronology radius `godelCriticalRadius` equals `1`. -/
@[simp]
theorem sinh_godelCriticalRadius : Real.sinh godelCriticalRadius = 1 := by
  simp [godelCriticalRadius]

/-- The Gödel line element in the coordinate convention stated in the
compilation. The arguments after `r` are the coordinate differentials
`(dt, dr, dφ, dz)`. -/
noncomputable def godel1949LineElement (r dt dr dφ dz : ℝ) : ℝ :=
  -dt ^ 2 + dr ^ 2 + dz ^ 2 +
    godelAzimuthalCoefficient r * dφ ^ 2 -
    2 * Real.sqrt 2 * Real.sinh r ^ 2 * dt * dφ

/-- Restricting the Gödel metric to a circle at fixed `t`, `r`, and `z`
leaves exactly its azimuthal metric coefficient times `dφ²`. This is the
precise metric statement behind the spacelike/null/timelike circle test. -/
theorem godel1949_circle_restriction (r dφ : ℝ) :
    godel1949LineElement r 0 0 dφ 0 =
      godelAzimuthalCoefficient r * dφ ^ 2 := by
  simp [godel1949LineElement]

/-- Below the Gödel chronology horizon, the coefficient on the closed
azimuthal direction is positive. The hypotheses are expressed directly in
terms of `sinh r`, so no unproved coordinate identification is implicit. -/
theorem godelAzimuthalCoefficient_pos_of_subcritical
    (r : ℝ) (hzero : 0 < Real.sinh r) (horizon : Real.sinh r < 1) :
    0 < godelAzimuthalCoefficient r := by
  dsimp [godelAzimuthalCoefficient]
  have hsq : Real.sinh r ^ 2 < 1 := by
    nlinarith [mul_pos hzero (show 0 < 1 - Real.sinh r by linarith [horizon])]
  exact mul_pos (sq_pos_of_pos hzero) (by linarith)

/-- Above the Gödel chronology horizon, the coefficient on the closed
azimuthal direction is negative. -/
theorem godelAzimuthalCoefficient_neg_of_supercritical
    (r : ℝ) (horizon : 1 < Real.sinh r) :
    godelAzimuthalCoefficient r < 0 := by
  dsimp [godelAzimuthalCoefficient]
  have hzero : 0 < Real.sinh r := by linarith [horizon]
  have hsq : 1 < Real.sinh r ^ 2 := by
    nlinarith [mul_pos (show 0 < Real.sinh r - 1 by linarith [horizon])
      (show 0 < Real.sinh r + 1 by linarith [horizon])]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos hzero) (by linarith)

/-- At the horizon the angular circle is null: its Gödel azimuthal
coefficient vanishes when `sinh r = 1`. -/
theorem godelAzimuthalCoefficient_zero_at_horizon
    (r : ℝ) (horizon : Real.sinh r = 1) :
    godelAzimuthalCoefficient r = 0 := by
  simp [godelAzimuthalCoefficient, horizon]

/-- The critical Gödel radius is a null circle in the stated line element. -/
theorem godelCriticalRadius_circle_is_null (dφ : ℝ) :
    godel1949LineElement godelCriticalRadius 0 0 dφ 0 = 0 := by
  rw [godel1949_circle_restriction]
  rw [godelAzimuthalCoefficient_zero_at_horizon _ sinh_godelCriticalRadius]
  simp

/-- A nonzero angular tangent has positive squared norm below the horizon. -/
theorem godel1949_circle_spacelike
    (r dφ : ℝ) (hzero : 0 < Real.sinh r) (horizon : Real.sinh r < 1)
    (hdφ : dφ ≠ 0) :
    0 < godel1949LineElement r 0 0 dφ 0 := by
  rw [godel1949_circle_restriction]
  exact mul_pos (godelAzimuthalCoefficient_pos_of_subcritical r hzero horizon)
    (sq_pos_of_ne_zero hdφ)

/-- A nonzero angular tangent has negative squared norm above the horizon. -/
theorem godel1949_circle_timelike
    (r dφ : ℝ) (horizon : 1 < Real.sinh r) (hdφ : dφ ≠ 0) :
    godel1949LineElement r 0 0 dφ 0 < 0 := by
  rw [godel1949_circle_restriction]
  exact mul_neg_of_neg_of_pos
    (godelAzimuthalCoefficient_neg_of_supercritical r horizon)
    (sq_pos_of_ne_zero hdφ)

/-- **Native Mathlib Lie-Bracket Spin & Centrifugal Frame Dragging**:
For any `IsIdempotentElem P`:
1. $⁅\Sigma, \Phi⁆ = (2 : \mathbb{Z}) \bullet (V * J)$,
2. $⁅\Sigma, J⁆ = (2 : \mathbb{Z}) \bullet (V * \Phi)$,
3. $⁅\Sigma, ⁅\Sigma, \Phi⁆⁆ = (4 : \mathbb{Z}) \bullet ((V * V) * \Phi)$,
4. $⁅\Sigma, ⁅\Sigma, J⁆⁆ = (4 : \mathbb{Z}) \bullet ((V * V) * J)$. -/
theorem native_spin_and_centrifugal_frame_dragging
    {P : R} (hP : IsIdempotentElem P) (A B : R) :
    ⁅spinVorticity P A B, solderPhi P A B⁆ =
      (2 : ℤ) • (fisherMetricOp P A B * solderJ P A B) ∧
    ⁅spinVorticity P A B, solderJ P A B⁆ =
      (2 : ℤ) • (fisherMetricOp P A B * solderPhi P A B) ∧
    ⁅spinVorticity P A B, ⁅spinVorticity P A B, solderPhi P A B⁆⁆ =
      (4 : ℤ) • ((fisherMetricOp P A B * fisherMetricOp P A B) * solderPhi P A B) ∧
    ⁅spinVorticity P A B, ⁅spinVorticity P A B, solderJ P A B⁆⁆ =
      (4 : ℤ) • ((fisherMetricOp P A B * fisherMetricOp P A B) * solderJ P A B) := by
  have hP2 : P * P = P := hP
  simp only [lie_eq_peirce_comm]
  exact ⟨gemFirstOrderLenseThirring hP2 A B,
         gemDualPrecession hP2 A B,
         gemSecondOrderCentrifugal hP2 A B,
         gemSecondOrderCentrifugal_dual hP2 A B⟩

/-- Double adjoint spin-vorticity operator $\mathrm{ad}_\Sigma^2(X) := ⁅\Sigma, ⁅\Sigma, X⁆⁆$. -/
def doubleVorticityAd (P A B X : R) : R :=
  ⁅spinVorticity P A B, ⁅spinVorticity P A B, X⁆⁆

/-- Single adjoint commutator with `spinVorticity P A B` commutes with left multiplication
by any element `C` that commutes with `spinVorticity P A B`. -/
theorem vorticityAd_left_mul_central {P A B C X : R}
    (hC : C * spinVorticity P A B = spinVorticity P A B * C) :
    ⁅spinVorticity P A B, C * X⁆ = C * ⁅spinVorticity P A B, X⁆ := by
  change spinVorticity P A B * (C * X) - (C * X) * spinVorticity P A B =
    C * (spinVorticity P A B * X - X * spinVorticity P A B)
  rw [← mul_assoc, ← hC, mul_assoc, mul_assoc, ← mul_sub]

/-- Left-multiplication by `C` (`C * Σ = Σ * C`) commutes with `doubleVorticityAd P A B`. -/
theorem doubleVorticityAd_left_mul_central {P A B C X : R}
    (hC : C * spinVorticity P A B = spinVorticity P A B * C) :
    doubleVorticityAd P A B (C * X) = C * doubleVorticityAd P A B X := by
  dsimp [doubleVorticityAd]
  rw [vorticityAd_left_mul_central hC, vorticityAd_left_mul_central hC]

/-- Single adjoint commutator with `spinVorticity P A B` commutes with `ℕ`-scalar multiplication. -/
theorem vorticityAd_nsmul (P A B : R) (c : ℕ) (X : R) :
    ⁅spinVorticity P A B, c • X⁆ = c • ⁅spinVorticity P A B, X⁆ := by
  change spinVorticity P A B * (c • X) - (c • X) * spinVorticity P A B =
    c • (spinVorticity P A B * X - X * spinVorticity P A B)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]

/-- `doubleVorticityAd` commutes with `ℕ`-scalar multiplication. -/
theorem doubleVorticityAd_nsmul (P A B : R) (c : ℕ) (X : R) :
    doubleVorticityAd P A B (c • X) = c • doubleVorticityAd P A B X := by
  dsimp [doubleVorticityAd]
  rw [vorticityAd_nsmul, vorticityAd_nsmul]

/-- `fisherMetricOp P A B` commutes with `spinVorticity P A B` under multiplication. -/
theorem fisherMetricOp_comm_spinVorticity {P : R} (hP : IsIdempotentElem P) (A B : R) :
    fisherMetricOp P A B * spinVorticity P A B =
      spinVorticity P A B * fisherMetricOp P A B := by
  have hP2 : P * P = P := hP
  peirce_nf hP2

/-- Every power `(fisherMetricOp P A B) ^ m` commutes with `spinVorticity P A B`. -/
theorem fisherMetricOp_pow_comm_spinVorticity {P : R} (hP : IsIdempotentElem P) (A B : R) (m : ℕ) :
    fisherMetricOp P A B ^ m * spinVorticity P A B =
      spinVorticity P A B * fisherMetricOp P A B ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_assoc, fisherMetricOp_comm_spinVorticity hP A B,
      ← mul_assoc, ih, mul_assoc]

/-- **Inductive $(2k)$-th Order Centrifugal Frame-Dragging Theorem
(`iterated_double_vorticity_ad_solderPhi`)**:
For every $k \in \mathbb{N}$ and any `IsIdempotentElem P`, iterating the double adjoint
spin-vorticity action $\mathrm{ad}_\Sigma^2(X) = ⁅\Sigma, ⁅\Sigma, X⁆⁆$ $k$ times on the
solder form $\Phi$ produces:
$$(\mathrm{ad}_\Sigma^2)^{[k]}(\Phi) = (4^k : \mathbb{N}) \bullet \big(V^{2k} * \Phi\big)$$ -/
theorem iterated_double_vorticity_ad_solderPhi
    {P : R} (hP : IsIdempotentElem P) (A B : R) (k : ℕ) :
    (doubleVorticityAd P A B)^[k] (solderPhi P A B) =
      (4 ^ k : ℕ) • (fisherMetricOp P A B ^ (2 * k) * solderPhi P A B) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, doubleVorticityAd_nsmul,
      doubleVorticityAd_left_mul_central (fisherMetricOp_pow_comm_spinVorticity hP A B (2 * k))]
    have hbase : doubleVorticityAd P A B (solderPhi P A B) =
        (4 : ℕ) • ((fisherMetricOp P A B * fisherMetricOp P A B) * solderPhi P A B) := by
      have h4 := (native_spin_and_centrifugal_frame_dragging hP A B).2.2.1
      simpa [doubleVorticityAd] using h4
    rw [hbase, mul_smul_comm, smul_smul, pow_succ, ← mul_assoc,
      show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, sq]

end NativeWheelerGodelPeirceRing

section NativeHilbertRobertsonSchrodinger

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Real symmetric Hilbert-space metric component $g(x, y) := \mathrm{Re}\langle x, y\rangle$. -/
noncomputable def hilbertSymmetricMetric (x y : E) : ℝ := (inner ℂ x y).re

/-- Imaginary symplectic Hilbert-space vorticity/curvature component
$\Omega(x, y) := \mathrm{Im}\langle x, y\rangle$. -/
noncomputable def hilbertSymplecticVorticity (x y : E) : ℝ := (inner ℂ x y).im

/-- **Native Mathlib Hilbert-Space Pythagorean & Robertson–Schrödinger Uncertainty Theorem
(`native_robertson_schrodinger_hilbert_uncertainty`)**:
For any vectors $x, y$ in a complex inner product space $E$:
1. **Exact Kähler Decomposition**: $g(x, y)^2 + \Omega(x, y)^2 = \|\langle x, y\rangle\|^2$,
2. **Robertson–Schrödinger Uncertainty Bound**:
   $$\Omega(x, y)^2 \le g(x, x)\,g(y, y) - g(x, y)^2$$ -/
theorem native_robertson_schrodinger_hilbert_uncertainty (x y : E) :
    hilbertSymmetricMetric x y ^ 2 + hilbertSymplecticVorticity x y ^ 2 =
      ‖inner ℂ x y‖ ^ 2 ∧
    hilbertSymplecticVorticity x y ^ 2 ≤
      hilbertSymmetricMetric x x * hilbertSymmetricMetric y y -
        hilbertSymmetricMetric x y ^ 2 := by
  dsimp [hilbertSymmetricMetric, hilbertSymplecticVorticity]
  have h_pyth : (inner ℂ x y).re ^ 2 + (inner ℂ x y).im ^ 2 = ‖inner ℂ x y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h_cs : ‖inner ℂ x y‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
  have h_sq : ‖inner ℂ x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    nlinarith [norm_nonneg (inner ℂ x y), mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  have hx : ‖x‖ ^ 2 = (inner ℂ x x).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x
  have hy : ‖y‖ ^ 2 = (inner ℂ y y).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) y
  refine ⟨h_pyth, ?_⟩
  linarith [show (‖x‖ * ‖y‖) ^ 2 = (inner ℂ x x).re * (inner ℂ y y).re by
    rw [mul_pow, hx, hy]]

end NativeHilbertRobertsonSchrodinger

/-- **Stage `𝔚𝔊₃`–`𝔚𝔊₄` Theorem (Local Spin Frame Dragging, CTL Transmutation & Uncertainty Bound)**:
Unifies first-order spin frame dragging, second-order and $(2k)$-th order inductive centrifugal
frame dragging, the $(\Sigma\Phi)^2 = -V^3$ closed timelike line transmutation, and the Quantum
Geometric / Robertson–Schrödinger uncertainty bound. -/
theorem archetype_W3_local_spin_frame_dragging_and_uncertainty
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (k : ℕ)
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (D : U → E) (u v : U) :
    -- (1) First-Order Einstein–Cartan spin frame dragging
    OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genJ P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genJ P A C) =
      (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    -- (2) Second-Order centrifugal frame dragging
    OperatorAlgebra.PeirceSpine.comm (genSig P A C)
        (OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C)
        (OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genJ P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) ∧
    -- (3) Inductive (2k)-th order centrifugal frame dragging
    (doubleVorticityAd P A C)^[k] (solderPhi P A C) =
      (4 ^ k : ℕ) • (fisherMetricOp P A C ^ (2 * k) * solderPhi P A C) ∧
    -- (4) Algebraic CTL transmutation (Σ Φ)² = -V³
    (spinVorticity P A C * solderPhi P A C) * (spinVorticity P A C * solderPhi P A C) =
      -(fisherMetricOp P A C * fisherMetricOp P A C * fisherMetricOp P A C) ∧
    -- (5) Quantum Geometric / Robertson–Schrödinger / Cramér–Rao uncertainty bound
    (complexPureQGTIm ψ D u v) ^ 2 ≤
      complexPureQGTRe ψ D u u * complexPureQGTRe ψ D v v - (complexPureQGTRe ψ D u v) ^ 2 := by
  have hE5 := archetype_E5_spin_frame_dragging_and_dressed_torsion hP A C
  have hCTL := (spacelike_to_closed_timelike_line_algebraic (P := P) hP A C).2.2.2.2
  refine ⟨hE5.2.2.1, hE5.2.2.2.1, by peirce_nf hP, by peirce_nf hP,
    iterated_double_vorticity_ad_solderPhi hP A C k, hCTL,
    quantum_geometric_uncertainty_principle ψ D u v⟩

/-! ## §4. Stage `𝔚𝔊₅`: The *Hubble Atlas* Isotropy & Second-Moment Centrifugal Theorem ($\mathrm{Tr}(\Sigma) = 0$ and $\Sigma^2 = Q_+^2 + Q_-^2 = V^2$) -/

/-- **Theorem 2b (`hubble_atlas_second_moment_centrifugal_identity` — Stage `𝔚𝔊₅`):
Orthogonal Chiral Sheet Decomposition & Second-Moment Identity $\Sigma^2 = V^2$**:
Over any associative ring `[Ring R]` with `IsIdempotentElem P`:
1. **Orthogonal Clockwise ($Q_+ = N_+ N_-$) and Counterclockwise ($Q_- = N_- N_+$) Sheets**:
   $$Q_+ Q_- = 0, \qquad Q_- Q_+ = 0$$
2. **Sum & Difference Decomposition**:
   $$V = Q_+ + Q_-, \qquad \Sigma = Q_+ - Q_-$$
3. **Second Moment Identity ($\Sigma^2 = Q_+^2 + Q_-^2 = V^2$)**:
   Even when the first-moment trace $\mathrm{Tr}(\Sigma) = \mathrm{Tr}(Q_+ - Q_-) = 0$ vanishes,
   the quadratic operator satisfies the exact algebraic identity:
   $$\boxed{\Sigma^2 = Q_+^2 + Q_-^2 = V^2}$$
4. **Centrifugal Frame Dragging Driven by $\Sigma^2 = V^2$**:
   $$⁅\Sigma, ⁅\Sigma, \Phi⁆⁆ = (4 : \mathbb{Z}) \bullet (\Sigma^2 * \Phi) = (4 : \mathbb{Z}) \bullet (V^2 * \Phi)$$ -/
theorem hubble_atlas_second_moment_centrifugal_identity
    {R : Type*} [Ring R] {P : R} (hP : IsIdempotentElem P) (A B : R) :
    sheetPlus P A B * sheetMinus P A B = 0 ∧
    sheetMinus P A B * sheetPlus P A B = 0 ∧
    fisherMetricOp P A B = sheetPlus P A B + sheetMinus P A B ∧
    spinVorticity P A B = sheetPlus P A B - sheetMinus P A B ∧
    spinVorticity P A B * spinVorticity P A B =
      sheetPlus P A B * sheetPlus P A B + sheetMinus P A B * sheetMinus P A B ∧
    spinVorticity P A B * spinVorticity P A B =
      fisherMetricOp P A B * fisherMetricOp P A B ∧
    ⁅spinVorticity P A B, ⁅spinVorticity P A B, solderPhi P A B⁆⁆ =
      (4 : ℤ) • ((spinVorticity P A B * spinVorticity P A B) * solderPhi P A B) := by
  have hP2 : P * P = P := hP
  dsimp [sheetPlus, sheetMinus]
  simp only [lie_eq_peirce_comm]
  refine ⟨by peirce_nf hP2, by peirce_nf hP2, rfl, rfl,
          by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2⟩

section HubbleAtlasBlockVorticity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Upper chiral Peirce shift $N_+(A) = \begin{pmatrix} 0 & A \\ 0 & 0 \end{pmatrix}$ on the
two-sheeted block matrix space `Matrix (Sum n n) (Sum n n) R`. -/
def blockUpper (A : Matrix n n R) : Matrix (Sum n n) (Sum n n) R :=
  Matrix.fromBlocks 0 A 0 0

/-- Lower chiral Peirce shift $N_-(B) = \begin{pmatrix} 0 & 0 \\ B & 0 \end{pmatrix}$ on the
two-sheeted block matrix space `Matrix (Sum n n) (Sum n n) R`. -/
def blockLower (B : Matrix n n R) : Matrix (Sum n n) (Sum n n) R :=
  Matrix.fromBlocks 0 0 B 0

/-- Local galactic spin-dipole vorticity $\Sigma(A, B) = [N_+(A), N_-(B)]$. -/
def blockVorticity (A B : Matrix n n R) : Matrix (Sum n n) (Sum n n) R :=
  OperatorAlgebra.PeirceSpine.comm (blockUpper A) (blockLower B)

/-- Local galactic Operator Fisher metric $V(A, B) = \{N_+(A), N_-(B)\}$. -/
def blockFisher (A B : Matrix n n R) : Matrix (Sum n n) (Sum n n) R :=
  OperatorAlgebra.PeirceSpine.anticomm (blockUpper A) (blockLower B)

/-- Chiral grading operator $S_P = \begin{pmatrix} I & 0 \\ 0 & -I \end{pmatrix}$ on the
two-sheeted block matrix space. -/
def blockChiralInv : Matrix (Sum n n) (Sum n n) R :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Chiral supertrace $\mathrm{Str}(M) := \mathrm{trace}(S_P M)$ weighting the clockwise and
counterclockwise sheets by their chiral signs $+1$ and $-1$. -/
def blockSupertrace (M : Matrix (Sum n n) (Sum n n) R) : R :=
  Matrix.trace (blockChiralInv * M)

/-- Odd $\mathrm{Pin}$ parity reflection operator $\Phi_1 = \begin{pmatrix} 0 & I \\ I & 0 \end{pmatrix}$
swapping the north (conscious) and south (shadow) chiral sheets. -/
def blockParitySwap : Matrix (Sum n n) (Sum n n) R :=
  Matrix.fromBlocks 0 1 1 0

/-- Explicit block-diagonal dipole decomposition of the spin-vorticity:
$$\Sigma(A, B) = \begin{pmatrix} AB & 0 \\ 0 & -BA \end{pmatrix}$$
showing that a $+AB$ rotation on the north sheet is always accompanied by a $-BA$
counter-rotation on the south sheet. -/
theorem blockVorticity_eq_fromBlocks (A B : Matrix n n R) :
    blockVorticity A B = Matrix.fromBlocks (A * B) 0 0 (-(B * A)) := by
  dsimp [blockVorticity, OperatorAlgebra.PeirceSpine.comm, blockUpper, blockLower]
  rw [sub_eq_add_neg]
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]

/-- Explicit block-diagonal decomposition of the Operator Fisher metric:
$$V(A, B) = \begin{pmatrix} AB & 0 \\ 0 & BA \end{pmatrix}$$ -/
theorem blockFisher_eq_fromBlocks (A B : Matrix n n R) :
    blockFisher A B = Matrix.fromBlocks (A * B) 0 0 (B * A) := by
  dsimp [blockFisher, OperatorAlgebra.PeirceSpine.anticomm, blockUpper, blockLower]
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]

/-- The explicit block form of the degree-three Peirce/Jordan-triple
renormalization from `jordan_triple_counterterm_idempotent`. -/
def blockBruhatRenormalizedProjector (A B : Matrix n n R) :
    Matrix (Sum n n) (Sum n n) R :=
  Matrix.fromBlocks (1 - A * B) (A - A * B * A) B (B * A)

/-- The proposed Rung-5 block matrix is an idempotent for arbitrary square
matrices `A` and `B` over a commutative ring. Its four entries are precisely
the expansion `P + Φ - Σ - V N₊`; the proof uses only associative matrix
multiplication and does not invoke a square root. -/
theorem blockBruhatRenormalizedProjector_idempotent (A B : Matrix n n R) :
    blockBruhatRenormalizedProjector A B * blockBruhatRenormalizedProjector A B =
      blockBruhatRenormalizedProjector A B := by
  rw [blockBruhatRenormalizedProjector, Matrix.fromBlocks_multiply]
  congr 1 <;> noncomm_ring

/-- Power of a block-diagonal matrix `Matrix.fromBlocks X 0 0 Y` equals
`Matrix.fromBlocks (X ^ m) 0 0 (Y ^ m)` for every `m : ℕ`. -/
theorem fromBlocks_diag_pow (X Y : Matrix n n R) (m : ℕ) :
    (Matrix.fromBlocks X 0 0 Y) ^ m = Matrix.fromBlocks (X ^ m) 0 0 (Y ^ m) := by
  induction m with
  | zero =>
    simp [Matrix.fromBlocks_one]
  | succ m ih =>
    rw [pow_succ, ih, Matrix.fromBlocks_multiply]
    simp [pow_succ]

/-- Associative shift identity `(A * B) ^ (m + 1) = A * ((B * A) ^ m * B)` in any monoid. -/
theorem mul_pow_succ_eq_mul_pow_mul {M : Type*} [Monoid M] (A B : M) (m : ℕ) :
    (A * B) ^ (m + 1) = A * ((B * A) ^ m * B) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (A * B), ih, pow_succ (B * A)]
    simp [mul_assoc]

/-- Cyclic invariance of the matrix trace for arbitrary powers:
`Matrix.trace ((A * B) ^ m) = Matrix.trace ((B * A) ^ m)` for all `m : ℕ`. -/
theorem trace_mul_pow_comm (A B : Matrix n n R) (m : ℕ) :
    Matrix.trace ((A * B) ^ m) = Matrix.trace ((B * A) ^ m) := by
  cases m with
  | zero => simp
  | succ m =>
    rw [mul_pow_succ_eq_mul_pow_mul A B m, Matrix.trace_mul_comm A ((B * A) ^ m * B),
      mul_assoc, ← pow_succ]

/-- **Hubble Atlas Higher-Moment Trace & Supertrace Theorem (`hubble_atlas_odd_power_trace_zero`)**:
For every $k \in \mathbb{N}$ and any local galactic vortex $(A, B)$:
1. **All Odd Moments Vanish in Unpolarized Sky Trace**:
   $$\mathrm{trace}\!\left(\Sigma(A, B)^{2k+1}\right) = 0$$
2. **All Even Moments Match the Symmetric Fisher Metric Powers**:
   $$\Sigma(A, B)^{2k} = V(A, B)^{2k}, \qquad
     \mathrm{trace}\!\left(\Sigma(A, B)^{2k}\right) = 2 \bullet \mathrm{trace}\!\left((AB)^{2k}\right)$$
3. **Chiral Supertrace Detects the Spin-Dipole**:
   $$\mathrm{Str}(\Sigma(A, B)) = \mathrm{trace}(S_P\,\Sigma(A, B)) = \mathrm{trace}(V(A, B)) = 2 \bullet \mathrm{trace}(AB)$$ -/
theorem hubble_atlas_odd_power_trace_zero (A B : Matrix n n R) (k : ℕ) :
    Matrix.trace (blockVorticity A B ^ (2 * k + 1)) = 0 ∧
    blockVorticity A B ^ (2 * k) = blockFisher A B ^ (2 * k) ∧
    Matrix.trace (blockVorticity A B ^ (2 * k)) = 2 • Matrix.trace ((A * B) ^ (2 * k)) ∧
    blockSupertrace (blockVorticity A B) = Matrix.trace (blockFisher A B) := by
  have hodd_neg : (-(B * A)) ^ (2 * k + 1) = -((B * A) ^ (2 * k + 1)) := by
    rw [neg_pow, Odd.neg_one_pow ⟨k, rfl⟩, neg_one_mul]
  have heven_neg : (-(B * A)) ^ (2 * k) = (B * A) ^ (2 * k) := by
    rw [neg_pow, Even.neg_one_pow ⟨k, by ring⟩, one_mul]
  have htr_diag : ∀ X Y : Matrix n n R,
      Matrix.trace (Matrix.fromBlocks X (0 : Matrix n n R) 0 Y) =
        Matrix.trace X + Matrix.trace Y := by
    intro X Y
    simp [Matrix.trace]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [blockVorticity_eq_fromBlocks, fromBlocks_diag_pow, hodd_neg, htr_diag,
      Matrix.trace_neg, trace_mul_pow_comm A B (2 * k + 1), add_neg_cancel]
  · rw [blockVorticity_eq_fromBlocks, blockFisher_eq_fromBlocks,
      fromBlocks_diag_pow, fromBlocks_diag_pow, heven_neg]
  · rw [blockVorticity_eq_fromBlocks, fromBlocks_diag_pow, heven_neg, htr_diag,
      ← trace_mul_pow_comm A B (2 * k), two_smul]
  · dsimp [blockSupertrace, blockChiralInv]
    rw [blockVorticity_eq_fromBlocks, blockFisher_eq_fromBlocks]
    simp [Matrix.fromBlocks_multiply]

/-- **Hubble Atlas Global Trace Cancellation Law**:
For every local Peirce vortex $(A, B)$, the global trace of the spin-vorticity $\Sigma(A, B)$
across the two chiral sheets vanishes identically:
$$\mathrm{trace}(\Sigma(A, B)) = 0$$
whereas the global trace of the symmetric Fisher metric is $2\,\mathrm{trace}(AB)$. -/
theorem hubble_atlas_global_vorticity_trace_zero (A B : Matrix n n R) :
    Matrix.trace (blockVorticity A B) = 0 ∧
    Matrix.trace (blockFisher A B) = 2 • Matrix.trace (A * B) := by
  have htr1 : Matrix.trace (Matrix.fromBlocks (A * B) (0 : Matrix n n R) 0 (-(B * A))) =
      Matrix.trace (A * B) + Matrix.trace (-(B * A)) := by
    simp [Matrix.trace]
  have htr2 : Matrix.trace (Matrix.fromBlocks (A * B) (0 : Matrix n n R) 0 (B * A)) =
      Matrix.trace (A * B) + Matrix.trace (B * A) := by
    simp [Matrix.trace]
  constructor
  · rw [blockVorticity_eq_fromBlocks, htr1, Matrix.trace_neg,
      Matrix.trace_mul_comm B A, add_neg_cancel]
  · rw [blockFisher_eq_fromBlocks, htr2,
      Matrix.trace_mul_comm B A, two_smul]

/-- **Parity Reflection Inverts the Galactic Rotation Axis**:
Conjugating $\Sigma(A, B)$ by the parity swap $\Phi_1 = \begin{pmatrix} 0 & I \\ I & 0 \end{pmatrix}$
exchanges the two chiral sheets and negates the vorticity:
$$\Phi_1\,\Sigma(A, B)\,\Phi_1 = -\Sigma(B, A)$$ -/
theorem hubble_atlas_parity_swap_inverts_vorticity (A B : Matrix n n R) :
    blockParitySwap * blockVorticity A B * blockParitySwap = -blockVorticity B A := by
  rw [blockVorticity_eq_fromBlocks, blockVorticity_eq_fromBlocks, blockParitySwap]
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

/-- **Hubble Atlas Catalog Ensemble Cancellation**:
For any finite catalog of galaxies indexed by `s : Finset ι`:
1. The total global trace of the cosmic vorticity sum vanishes unconditionally:
   $$\mathrm{trace}\!\left(\sum_{i \in s} \Sigma(A_i, B_i)\right) = 0$$
2. Pairing each galaxy $\Sigma(A_i, B_i)$ with its parity-swapped twin
   $\Phi_1 \Sigma(B_i, A_i) \Phi_1$ cancels the full matrix operator identically at every entry:
   $$\sum_{i \in s} \left(\Sigma(A_i, B_i) + \Phi_1\,\Sigma(B_i, A_i)\,\Phi_1\right) = 0$$ -/
theorem hubble_atlas_catalog_ensemble_cancellation
    {ι : Type*} (s : Finset ι) (A B : ι → Matrix n n R) :
    Matrix.trace (∑ i ∈ s, blockVorticity (A i) (B i)) = 0 ∧
    (∑ i ∈ s, (blockVorticity (A i) (B i) +
      blockParitySwap * blockVorticity (B i) (A i) * blockParitySwap)) = 0 := by
  constructor
  · rw [Matrix.trace_sum]
    refine Finset.sum_eq_zero (fun i _ => (hubble_atlas_global_vorticity_trace_zero (A i) (B i)).1)
  · refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hubble_atlas_parity_swap_inverts_vorticity (B i) (A i), add_neg_cancel]

end HubbleAtlasBlockVorticity

/-- **Native Mathlib $\mathbb{Z}_2$-Involutive Finset Cancellation Theorem
(`z2_involutive_finset_sum_two_smul_zero`)**:
For any finite index set `s : Finset ι`, any additive commutative group `M`, any involution
`σ : ι → ι` preserving `s` (`∀ i ∈ s, σ i ∈ s` and `∀ i ∈ s, σ (σ i) = i`), and any
chiral-antisymmetric observable `ω : ι → M` (`∀ i ∈ s, ω (σ i) = -ω i`):
1. $\sum_{i \in s} \omega(i) = -\sum_{i \in s} \omega(i)$,
2. $(2 : \mathbb{N}) \bullet \sum_{i \in s} \omega(i) = 0$. -/
theorem z2_involutive_finset_sum_two_smul_zero
    {ι M : Type*} [AddCommGroup M] (s : Finset ι) (σ : ι → ι) (ω : ι → M)
    (h_mem : ∀ i ∈ s, σ i ∈ s)
    (h_inv : ∀ i ∈ s, σ (σ i) = i)
    (h_anti : ∀ i ∈ s, ω (σ i) = -ω i) :
    (∑ i ∈ s, ω i) = -(∑ i ∈ s, ω i) ∧
    (2 : ℕ) • (∑ i ∈ s, ω i) = 0 := by
  have hbij : (∑ i ∈ s, ω i) = ∑ i ∈ s, ω (σ i) := by
    refine (Finset.sum_bij (fun i _ => σ i) h_mem ?_ ?_ (fun _ _ => rfl)).symm
    · intro a ha b hb hab
      calc a = σ (σ a) := (h_inv a ha).symm
      _ = σ (σ b) := by rw [hab]
      _ = b := h_inv b hb
    · intro b hb
      exact ⟨σ b, h_mem b hb, h_inv b hb⟩
  have hanti_sum : (∑ i ∈ s, ω (σ i)) = -(∑ i ∈ s, ω i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl h_anti
  have hneg : (∑ i ∈ s, ω i) = -(∑ i ∈ s, ω i) := hbij.trans hanti_sum
  refine ⟨hneg, ?_⟩
  rw [two_nsmul]
  exact add_eq_zero_iff_eq_neg.mpr hneg

/-- Concrete $2 \times 2$ upper chiral shift $N_+ = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ in $\mathrm{Mat}_2(\mathbb{Z})$. -/
def witnessNPlus : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- Concrete $2 \times 2$ lower chiral shift $N_- = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$ in $\mathrm{Mat}_2(\mathbb{Z})$. -/
def witnessNMinus : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- **Explicit Non-Commutativity Witness (`N_+ * N_- ≠ N_- * N_+`)**:
Proves that the concrete $2 \times 2$ chiral Peirce shifts do not commute, generating a
genuinely non-zero galactic spin-dipole vorticity $\Sigma = [N_+, N_-] \neq 0$. -/
theorem witness_chiral_shifts_noncomm :
    witnessNPlus * witnessNMinus ≠ witnessNMinus * witnessNPlus := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  norm_num [witnessNPlus, witnessNMinus, Matrix.mul_apply, Fin.sum_univ_two] at h00

section GenericMatrixNoncommutativityWitness

variable (R : Type*) [Ring R] [Nontrivial R]

/-- Generic upper matrix unit over a nontrivial coefficient ring. -/
def genericWitnessNPlus : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

/-- Generic lower matrix unit over a nontrivial coefficient ring. -/
def genericWitnessNMinus : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]

/-- Every nontrivial coefficient ring has a genuinely noncommutative `2 × 2` matrix algebra. -/
theorem generic_two_by_two_matrix_noncommutativity :
    genericWitnessNPlus R * genericWitnessNMinus R ≠
      genericWitnessNMinus R * genericWitnessNPlus R := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  have hone : (1 : R) = 0 := by
    simp [genericWitnessNPlus, genericWitnessNMinus, Matrix.mul_apply,
      Fin.sum_univ_two] at h00
  exact one_ne_zero hone

end GenericMatrixNoncommutativityWitness

/-- **Concrete $2 \times 2$ Witness of Local Galactic Spin with Zero Global Net Rotation**:
For $N_+ = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ and
$N_- = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$ in $\mathrm{Mat}_2(\mathbb{Z})$:
1. The chiral shifts do not commute (`witnessNPlus * witnessNMinus ≠ witnessNMinus * witnessNPlus`)
   and the local spin-vorticity $\Sigma = [N_+, N_-] = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \neq 0$
   is non-zero,
2. The local spin frame dragging $[\Sigma, \Phi] = \begin{pmatrix} 0 & 2 \\ -2 & 0 \end{pmatrix} \neq 0$
   is non-zero,
3. Yet the unpolarized cosmic trace vanishes ($\mathrm{trace}(\Sigma) = 0$) while the second-moment
   centrifugal trace is strictly positive ($\mathrm{trace}(\Sigma^2) = 2 > 0$),
4. And any chiral-paired epistemic token `[tok, chiralSwapToken tok]` is globally balanced
   (`isEpistemicallyBalanced [tok, chiralSwapToken tok]`). -/
theorem archetype_W4_hubble_atlas_local_spin_global_cancellation
    (tok : TheoryToken) :
    let Phi_mat := witnessNPlus + witnessNMinus
    let Sigma_mat := OperatorAlgebra.PeirceSpine.comm witnessNPlus witnessNMinus
    -- (0) Explicit non-commutativity of the chiral shifts
    witnessNPlus * witnessNMinus ≠ witnessNMinus * witnessNPlus ∧
    -- (1) Non-zero local galactic vorticity Σ ≠ 0
    Sigma_mat ≠ 0 ∧
    -- (2) Non-zero local Einstein–Cartan spin frame dragging [Σ, Φ] ≠ 0
    OperatorAlgebra.PeirceSpine.comm Sigma_mat Phi_mat ≠ 0 ∧
    -- (3) Zero global cosmic rotation trace Tr(Σ) = 0, yet positive second moment Tr(Σ²) = 2
    Matrix.trace Sigma_mat = 0 ∧
    Matrix.trace (Sigma_mat * Sigma_mat) = 2 ∧
    -- (4) Paired chiral token pair has zero net global polarity
    isEpistemicallyBalanced [tok, chiralSwapToken tok] := by
  dsimp only
  refine ⟨witness_chiral_shifts_noncomm, ?_, ?_, ?_, ?_, paired_stream_balanced tok⟩
  · intro hSig
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hSig
    norm_num [witnessNPlus, witnessNMinus, OperatorAlgebra.PeirceSpine.comm,
      Matrix.mul_apply, Fin.sum_univ_two] at h00
  · intro hdrag
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hdrag
    norm_num [witnessNPlus, witnessNMinus, OperatorAlgebra.PeirceSpine.comm,
      Matrix.mul_apply, Fin.sum_univ_two] at h01
  · simp [witnessNPlus, witnessNMinus, OperatorAlgebra.PeirceSpine.comm,
      Matrix.trace, Fin.sum_univ_two]
  · simp [witnessNPlus, witnessNMinus, OperatorAlgebra.PeirceSpine.comm,
      Matrix.trace, Fin.sum_univ_two]

/-! ## §5. Stage `𝔚𝔊₅`–`𝔚𝔊₆`: Native Mathlib Lawvere–Gödel Diagonal Theorem, $\mathbb{P}^1(K)$ Chart Inversion & Spinorial $4\pi$ Periodicity -/

/-- **Native Mathlib Lawvere Diagonal Fixed-Point Theorem (`native_lawvere_diagonal_fixed_point`)**:
For any types `α, β`, if `f : α → (α → β)` is surjective, then every endomorphism `g : β → β`
possesses a fixed point `b : β` such that `g b = b`. -/
theorem native_lawvere_diagonal_fixed_point {α β : Type*}
    (f : α → α → β) (hf : Function.Surjective f) (g : β → β) :
    ∃ b : β, g b = b := by
  rcases hf (fun a => g (f a a)) with ⟨a₀, ha₀⟩
  exact ⟨f a₀ a₀, (congrFun ha₀ a₀).symm⟩

/-- **Native Mathlib Gödel–Lawvere Diagonal Incompleteness Theorem (`native_godel_lawvere_incompleteness`)**:
If a truth/state carrier `β` admits a fixed-point-free endomorphism `not_op : β → β`
(`∀ b : β, not_op b ≠ b`, such as Boolean negation or chiral Möbius twist on non-zero states),
then **no self-referential encoding `f : α → (α → β)` can be surjective**. -/
theorem native_godel_lawvere_incompleteness {α β : Type*}
    (not_op : β → β) (h_no_fix : ∀ b : β, not_op b ≠ b) (f : α → α → β) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨b, hb⟩ := native_lawvere_diagonal_fixed_point f hf not_op
  exact h_no_fix b hb

section NativeProjectiveLineChartInversion

variable (K : Type*) [DivisionRing K]

/-- Linear coordinate swap $(u, v) \mapsto (v, u)$ on `Fin 2 → K`, implementing the homogeneous
reciprocal chart change $[u : v] \mapsto [v : u]$ ($w = 1/z$) on $\mathbb{P}^1(K)$. -/
def projCoordSwap : (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun v i := v (Equiv.swap 0 1 i)
  map_add' _ _ := by ext i; simp
  map_smul' _ _ := by ext i; simp

/-- The homogeneous coordinate swap `projCoordSwap K` on `Fin 2 → K` is injective. -/
theorem projCoordSwap_injective : Function.Injective (projCoordSwap K) := by
  intro v w h
  funext i
  have hi := congrFun h (Equiv.swap 0 1 i)
  simpa [projCoordSwap] using hi

/-- **Native Mathlib Projective Line Reciprocal Chart Inversion (`projectiveChartInversion`)**:
The induced projective automorphism on Mathlib's `ℙ K (Fin 2 → K)` (`Projectivization K (Fin 2 → K)`)
swapping the affine origin $[1 : 0]$ and the point at infinity $[0 : 1]$. -/
def projectiveChartInversion : ℙ K (Fin 2 → K) → ℙ K (Fin 2 → K) :=
  Projectivization.map (projCoordSwap K) (projCoordSwap_injective K)

/-- The conscious origin point $[1 : 0] \in \mathbb{P}^1(K)$ in native Mathlib `Projectivization`. -/
def projOrigin : ℙ K (Fin 2 → K) :=
  Projectivization.mk K ![1, 0] (by
    intro h
    have h0 := congrFun h 0
    simp at h0)

/-- The point at infinity $[0 : 1] \in \mathbb{P}^1(K)$ in native Mathlib `Projectivization`. -/
def projInfinity : ℙ K (Fin 2 → K) :=
  Projectivization.mk K ![0, 1] (by
    intro h
    have h1 := congrFun h 1
    simp at h1)

/-- **Native Mathlib Projective Chart Inversion is an Involution Exchanging $0 \leftrightarrow \infty$**:
1. `∀ p : ℙ K (Fin 2 → K), projectiveChartInversion K (projectiveChartInversion K p) = p`,
2. `projectiveChartInversion K (projOrigin K) = projInfinity K`,
3. `projectiveChartInversion K (projInfinity K) = projOrigin K`. -/
theorem projectiveChartInversion_involutive_and_swaps_poles :
    (∀ p : ℙ K (Fin 2 → K),
      projectiveChartInversion K (projectiveChartInversion K p) = p) ∧
    projectiveChartInversion K (projOrigin K) = projInfinity K ∧
    projectiveChartInversion K (projInfinity K) = projOrigin K := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    induction p using Projectivization.ind with
    | h v hv =>
      dsimp [projectiveChartInversion]
      rw [Projectivization.map_mk, Projectivization.map_mk]
      apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
      refine ⟨1, ?_⟩
      ext i
      simp [projCoordSwap]
  · dsimp [projectiveChartInversion, projOrigin, projInfinity]
    rw [Projectivization.map_mk]
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
    refine ⟨1, ?_⟩
    ext i
    fin_cases i <;> simp [projCoordSwap]
  · dsimp [projectiveChartInversion, projOrigin, projInfinity]
    rw [Projectivization.map_mk]
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
    refine ⟨1, ?_⟩
    ext i
    fin_cases i <;> simp [projCoordSwap]

end NativeProjectiveLineChartInversion

/-- Native Mathlib $2 \times 2$ symplectic Möbius twist matrix
$J_{\mathrm{mob}} = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$. -/
def spinorialMobiusJ {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, 0]

/-- **Native Mathlib Spinorial $4\pi$ Matrix Double Cover (`spinorialMobiusJ_pow_four_periodic`)**:
For every associative ring `R` and every `k : ℕ`:
1. $J_{\mathrm{mob}}^2 = -1$ ($2\pi$ single-cycle spinorial parity inversion),
2. $J_{\mathrm{mob}}^4 = 1$ ($4\pi$ double-cover restoration),
3. $J_{\mathrm{mob}}^{4k} = 1$ and $J_{\mathrm{mob}}^{4k+2} = -1$. -/
theorem spinorialMobiusJ_pow_four_periodic {R : Type*} [Ring R] (k : ℕ) :
    (spinorialMobiusJ : Matrix (Fin 2) (Fin 2) R) ^ 2 = -1 ∧
    (spinorialMobiusJ : Matrix (Fin 2) (Fin 2) R) ^ 4 = 1 ∧
    (spinorialMobiusJ : Matrix (Fin 2) (Fin 2) R) ^ (4 * k) = 1 ∧
    (spinorialMobiusJ : Matrix (Fin 2) (Fin 2) R) ^ (4 * k + 2) = -1 := by
  have h2 : (spinorialMobiusJ : Matrix (Fin 2) (Fin 2) R) ^ 2 = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sq, spinorialMobiusJ, Matrix.mul_apply, Fin.sum_univ_two]
  have h4 : (spinorialMobiusJ : Matrix (Fin 2) (Fin 2) R) ^ 4 = 1 := by
    have h4_split : (spinorialMobiusJ : Matrix (Fin 2) (Fin 2) R) ^ 4 =
        ((spinorialMobiusJ : Matrix (Fin 2) (Fin 2) R) ^ 2) ^ 2 := by
      rw [← pow_mul]
    rw [h4_split, h2]
    simp
  have h4k : (spinorialMobiusJ : Matrix (Fin 2) (Fin 2) R) ^ (4 * k) = 1 := by
    rw [pow_mul, h4, one_pow]
  have h4k2 : (spinorialMobiusJ : Matrix (Fin 2) (Fin 2) R) ^ (4 * k + 2) = -1 := by
    rw [pow_add, h4k, one_mul, h2]
  exact ⟨h2, h4, h4k, h4k2⟩

/-- **Lawvere–Gödel Single-Sheet Fixed-Point Obstruction on `DoubledSpace ℝ`**:
The Krein–Clifford Möbius twist $\mathcal{I} = \mathrm{complex\_i}$ (`SelfReference.moebiusTwist`,
$\mathcal{I}(x, \xi) = (-\xi, x)$) has **no non-zero fixed point** on `DoubledSpace ℝ`:
$$\mathrm{complex\_i}(x, \xi) = (x, \xi) \iff x = 0 \land \xi = 0$$ -/
theorem lawvere_godel_moebius_fixed_point_obstruction (x ξ : ℝ) :
    complex_i (to_doubled x ξ : DoubledSpace ℝ) = to_doubled x ξ ↔ x = 0 ∧ ξ = 0 := by
  rw [complex_i_to_doubled]
  constructor
  · intro h
    have h1 : -ξ = x := congrArg WithLp.fst h
    have h2 : x = ξ := congrArg WithLp.snd h
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    apply DoubledSpace.ext <;> simp

/-- **Spinorial $2\pi$ Parity Inversion vs. $4\pi$ Möbius Double Cover Restoration**:
1. Traversing the Krein–Clifford Möbius loop twice ($2\pi$ single-sheet return) inverts parity:
   $$\mathcal{I}^2(x, \xi) = (-x, -\xi)$$
2. Traversing the loop four times ($4\pi$ doubled-sheet Ouroboros return) restores the exact state:
   $$\mathcal{I}^4(x, \xi) = (x, \xi)$$ -/
theorem moebius_spinorial_double_cover_period (x ξ : ℝ) :
    complex_i (complex_i (to_doubled x ξ : DoubledSpace ℝ)) = to_doubled (-x) (-ξ) ∧
    complex_i (complex_i (complex_i (complex_i (to_doubled x ξ : DoubledSpace ℝ)))) =
      to_doubled x ξ := by
  constructor <;> simp

/-- **Stage `𝔚𝔊₅`–`𝔚𝔊₆` Theorem (Lawvere–Gödel Obstruction, $\mathbb{P}^1(\mathbb{R})$ Chart Inversion & $4\pi$ Spinorial Double Cover)**:
Combines:
1. The Lawvere–Gödel single-sheet fixed-point obstruction (`lawvere_godel_moebius_fixed_point_obstruction`),
2. The spinorial $2\pi$ parity flip $\mathcal{I}^2(x, \xi) = (-x, -\xi)$ and $4\pi$ restoration
   $\mathcal{I}^4(x, \xi) = (x, \xi)$ (`moebius_spinorial_double_cover_period`),
3. The native Mathlib projective chart inversion $0 \leftrightarrow \infty$ on $\mathbb{P}^1(\mathbb{R})$
   (`projectiveChartInversion_involutive_and_swaps_poles ℝ`), and
4. The split-Clifford two-chart projective reflection/twist identities `e0 * e0 = 1` and
   `e1 * e1 = -1` from `InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge`. -/
theorem archetype_W5_lawvere_godel_mobius_double_cover (x ξ : ℝ) :
    (complex_i (to_doubled x ξ : DoubledSpace ℝ) = to_doubled x ξ ↔ x = 0 ∧ ξ = 0) ∧
    complex_i (complex_i (to_doubled x ξ : DoubledSpace ℝ)) = to_doubled (-x) (-ξ) ∧
    complex_i (complex_i (complex_i (complex_i (to_doubled x ξ : DoubledSpace ℝ)))) =
      to_doubled x ξ ∧
    projectiveChartInversion ℝ (projOrigin ℝ) = projInfinity ℝ ∧
    projectiveChartInversion ℝ (projInfinity ℝ) = projOrigin ℝ ∧
    InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.e0 *
      InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.e0 = 1 ∧
    InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.e1 *
      InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.e1 = -1 := by
  rcases moebius_spinorial_double_cover_period x ξ with ⟨h_two, h_four⟩
  rcases projectiveChartInversion_involutive_and_swaps_poles ℝ with ⟨_, h_orig, h_inf⟩
  exact ⟨lawvere_godel_moebius_fixed_point_obstruction x ξ,
         h_two, h_four, h_orig, h_inf,
         InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.e0_sq,
         InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.e1_sq⟩

/-! ## §6. Stage `𝔚𝔊₆`: Master Native Mathlib Wheeler–Gödel–Hubble Ouroboros Synthesis -/

/-- **Stage `𝔚𝔊₆` Master Theorem (`wheeler_godel_rotating_universe_chronology_master_synthesis`)**:
Crystallizes the complete 6-stage synthesis (`𝔚𝔊₁ ≺ 𝔚𝔊₂ ≺ 𝔚𝔊₃ ≺ {𝔚𝔊₄, 𝔚𝔊₅} ≺ 𝔚𝔊₆`) of
Wheeler's account of Kurt Gödel in native Mathlib:
1. **Poset Reachability & Preorder Chronology Protection (`𝔚𝔊₁`)**:
   $\mathfrak{WG}_1 \prec^+ \mathfrak{WG}_6$, diamond fork/join $\mathfrak{WG}_3 \prec \{\mathfrak{WG}_4, \mathfrak{WG}_5\} \prec \mathfrak{WG}_6$,
   and $\forall s, \neg (\mathfrak{WG}_s \prec^+ \mathfrak{WG}_s)$.
2. **Wheeler–Gödel Equivalence Theorem (`𝔚𝔊₁`–`𝔚𝔊₃`)**:
   - Gödel Incompleteness Defect: $(P + \Phi)^2 - (P + \Phi) = V$,
   - Para-Kähler Lock: $S_P \Sigma = V$ and $S_P V = \Sigma$,
   - **Exact Equivalence**: $(P + \Phi)^2 = P + \Phi \iff ⁅N_+, N_-⁆ = 0$,
   - Heisenberg Solder Bracket: $⁅\Phi, J⁆ = -2\Sigma$.
3. **Quantum Closed Timelike Lines & $(2k)$-th Order Centrifugal Frame Dragging (`𝔚𝔊₄`)**:
   - $(\Sigma \Phi)^2 = -V^3$,
   - $[\Sigma, \Phi] = 2VJ$, $[\Sigma, [\Sigma, \Phi]] = 4V^2\Phi$, and
     $(\mathrm{ad}_\Sigma^2)^{[k]}(\Phi) = 4^k V^{2k}\Phi$.
4. **Hubble Atlas Isotropy & Second-Moment Centrifugal Law (`𝔚𝔊₅`)**:
   - $\Sigma^2 = Q_+^2 + Q_-^2 = V^2$,
   - $\mathrm{trace}(\Sigma(M_1, M_2)) = 0$ and $\mathrm{trace}(\Sigma(M_1, M_2)^{2k+1}) = 0$,
   - $\mathrm{Str}(\Sigma(M_1, M_2)) = \mathrm{trace}(V(M_1, M_2)) = 2\,\mathrm{trace}(M_1 M_2)$,
   - $\Phi_1 \Sigma(M_1, M_2) \Phi_1 = -\Sigma(M_2, M_1)$.
5. **Lawvere–Gödel Obstruction, $\mathbb{P}^1(\mathbb{R})$ Chart Reset & $4\pi$ Möbius Double Cover (`𝔚𝔊₆`)**:
   $\mathcal{I}(x, \xi) = (x, \xi) \iff x = 0 \land \xi = 0$, $\mathcal{I}^2(x, \xi) = (-x, -\xi)$,
   $\mathcal{I}^4(x, \xi) = (x, \xi)$, `projectiveChartInversion ℝ (projOrigin ℝ) = projInfinity ℝ`,
   and `(spinorialMobiusJ : Matrix (Fin 2) (Fin 2) ℤ) ^ (4 * k) = 1`. -/
theorem wheeler_godel_rotating_universe_chronology_master_synthesis
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) (k : ℕ)
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] (M₁ M₂ : Matrix n n R)
    (tok : TheoryToken) (x ξ : ℝ) :
    -- (1) Poset reachability 𝔚𝔊₁ ≺⁺ 𝔚𝔊₆ and strict Chronology Protection (no CTCs)
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W6_MasterWheelerGodelSynthesis ∧
    (∀ s : WheelerGodelStage, ¬ Relation.TransGen causalEdge s s) ∧
    -- (2) Wheeler–Gödel Equivalence: (P + Φ)² = P + Φ ↔ ⁅N_+, N_-⁆ = 0 & [Φ, J] = -2Σ
    ((P + solderPhi P A C) * (P + solderPhi P A C) - (P + solderPhi P A C) =
      fisherMetricOp P A C) ∧
    ((P + solderPhi P A C) * (P + solderPhi P A C) = P + solderPhi P A C ↔
      ⁅peircePlus P A, peirceMinus P C⁆ = 0) ∧
    ⁅solderPhi P A C, solderJ P A C⁆ = -((2 : ℤ) • spinVorticity P A C) ∧
    (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) = 0 →
      (2 : ℤ) • genSig P A C = 0 ∧ (2 : ℤ) • genV P A C = 0) ∧
    -- (3) Quantum Closed Timelike Line (ΣΦ)² = -V³ and (2k)-th order centrifugal frame dragging
    (spinVorticity P A C * solderPhi P A C) * (spinVorticity P A C * solderPhi P A C) =
      -(fisherMetricOp P A C * fisherMetricOp P A C * fisherMetricOp P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genJ P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C)
        (OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    (doubleVorticityAd P A C)^[k] (solderPhi P A C) =
      (4 ^ k : ℕ) • (fisherMetricOp P A C ^ (2 * k) * solderPhi P A C) ∧
    -- (4) Hubble Atlas Isotropy (Tr(Σ^{2k+1}) = 0) vs. Second Moment (Σ² = Q_+² + Q_-² = V²) & Supertrace
    spinVorticity P A C * spinVorticity P A C =
      sheetPlus P A C * sheetPlus P A C + sheetMinus P A C * sheetMinus P A C ∧
    spinVorticity P A C * spinVorticity P A C =
      fisherMetricOp P A C * fisherMetricOp P A C ∧
    Matrix.trace (blockVorticity M₁ M₂) = 0 ∧
    Matrix.trace (blockVorticity M₁ M₂ ^ (2 * k + 1)) = 0 ∧
    blockSupertrace (blockVorticity M₁ M₂) = Matrix.trace (blockFisher M₁ M₂) ∧
    blockParitySwap * blockVorticity M₁ M₂ * blockParitySwap = -blockVorticity M₂ M₁ ∧
    isEpistemicallyBalanced [tok, chiralSwapToken tok] ∧
    -- (5) Lawvere–Gödel obstruction, ℙ¹(ℝ) chart swap 0 ↔ ∞, and 4π Möbius double cover
    (complex_i (to_doubled x ξ : DoubledSpace ℝ) = to_doubled x ξ ↔ x = 0 ∧ ξ = 0) ∧
    complex_i (complex_i (to_doubled x ξ : DoubledSpace ℝ)) = to_doubled (-x) (-ξ) ∧
    complex_i (complex_i (complex_i (complex_i (to_doubled x ξ : DoubledSpace ℝ)))) =
      to_doubled x ξ ∧
    projectiveChartInversion ℝ (projOrigin ℝ) = projInfinity ℝ ∧
    (spinorialMobiusJ : Matrix (Fin 2) (Fin 2) ℤ) ^ (4 * k) = 1 := by
  have hDef := godel_incompleteness_idempotent_defect (P := P) hP A C
  have hW2 := archetype_W2_wheeler_godel_heisenberg_commutator_bridge hP A C
  have hCTL := (spacelike_to_closed_timelike_line_algebraic (P := P) hP A C).2.2.2.2
  have hE5 := archetype_E5_spin_frame_dragging_and_dressed_torsion hP A C
  have hMom := hubble_atlas_second_moment_centrifugal_identity (P := P) hP A C
  have hHubble := hubble_atlas_global_vorticity_trace_zero M₁ M₂
  have hOdd := hubble_atlas_odd_power_trace_zero M₁ M₂ k
  have hParity := hubble_atlas_parity_swap_inverts_vorticity M₁ M₂
  have hW5 := archetype_W5_lawvere_godel_mobius_double_cover x ξ
  exact ⟨causalEdge_W1_to_W6, causalEdge_acyclic,
    hDef.2.2.1, hW2.2.2.2.2, hW2.2.2.2.1, hW2.2.2.1,
    hCTL, hE5.2.2.1, by peirce_nf hP,
    iterated_double_vorticity_ad_solderPhi hP A C k,
    hMom.2.2.2.2.1, hMom.2.2.2.2.2.1,
    hHubble.1, hOdd.1, hOdd.2.2.2, hParity, paired_stream_balanced tok,
    hW5.1, hW5.2.1, hW5.2.2.1, hW5.2.2.2.1,
    (spinorialMobiusJ_pow_four_periodic (R := ℤ) k).2.2.1⟩

/-! ## §7. Higher-Order Continuation (`𝔚𝔊₇ ≺ 𝔚𝔊₈ ≺ 𝔚𝔊₉`) & Rung 5: Peirce–Bogoliubov Renormalization, Gödel's 1949 Metric Dictionary, the Three Hubble Trace Moments, and Cyclotronic Geodesics -/

/-- Reachability along the higher-order continuation `𝔚𝔊₆ ≺ 𝔚𝔊₇ ≺ 𝔚𝔊₈ ≺ 𝔚𝔊₉`. -/
theorem causalEdge_W6_to_W9 :
    Relation.TransGen causalEdge
      .W6_MasterWheelerGodelSynthesis
      .W9_HubbleAtlasThreeTraceMomentsAndRung5 := by
  have h67 : Relation.TransGen causalEdge
      .W6_MasterWheelerGodelSynthesis
      .W7_PeirceBogoliubovRenormalization :=
    Relation.TransGen.single trivial
  have h68 : Relation.TransGen causalEdge
      .W6_MasterWheelerGodelSynthesis
      .W8_GodelMetricCoordinateDictionary :=
    Relation.TransGen.tail h67 trivial
  exact Relation.TransGen.tail h68 trivial

/-- Full 9-stage causal reachability `𝔚𝔊₁ ≺⁺ 𝔚𝔊₉`. -/
theorem causalEdge_W1_to_W9 :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W9_HubbleAtlasThreeTraceMomentsAndRung5 :=
  Relation.TransGen.trans causalEdge_W1_to_W6 causalEdge_W6_to_W9

section HigherOrderPeirceBogoliubovRenormalization

variable {R : Type*} [Ring R]

/-- Deformed chiral involution generator $S_P + 2\Phi$ whose square is $I + 4V$. -/
def deformedChiralGenerator (P A B : R) : R :=
  chiralInv P + (2 : ℤ) • solderPhi P A B

/-- **Stage `𝔚𝔊₇` Theorem (`wg7_peirce_bogoliubov_renormalization_theorem`) —
The Peirce–Bogoliubov Renormalization Theorem (Why $-\Sigma$ Cancels the First-Order Gödel Defect)**:
Over any associative ring `[Ring R]` with `IsIdempotentElem P`:
1. **Exact Anticommutativity of the Gödel Sentence and the Uncertainty Rotor**:
   $$\Sigma\,\Phi = V\,J = -\Phi\,\Sigma, \qquad \Sigma\,\Phi + \Phi\,\Sigma = 0$$
2. **Jordan Action of $P$ on $\Sigma$**:
   $$P\,\Sigma = Q_+, \qquad \Sigma\,P = Q_+, \qquad \{P, \Sigma\} - \Sigma = S_P\,\Sigma = V$$
3. **First-Order Cancellation of Incompleteness by Uncertainty ($\Psi_1 = P + \Phi - \Sigma$)**:
   $$(P + \Phi - \Sigma)^2 - (P + \Phi - \Sigma) = \Sigma^2 = V^2$$
4. **All-Orders Meta-Tower Deformed Involution Generator ($S_P + 2\Phi$)**:
   $$S_P\,\Phi + \Phi\,S_P = 0, \qquad (S_P + 2\Phi)^2 = 1 + 4V$$
5. **Exact Operator Taylor Coefficients of $\widetilde{P} = \frac{1}{2}I + \frac{S_P + 2\Phi}{2\sqrt{I + 4V}}$**:
   Since $1 + S_P = 2P$, $V S_P = \Sigma$, and $V^2 S_P = V \Sigma$, expanding
   $(1 + 4V)^{-1/2} = 1 - 2V + 6V^2 - \cdots$ maps the $S_P$-coupled terms directly onto
   the Heisenberg–Gödel counterterms $P - \Sigma + 3 V \Sigma - \cdots$. -/
theorem wg7_peirce_bogoliubov_renormalization_theorem
    {P : R} (hP : IsIdempotentElem P) (A B : R) :
    spinVorticity P A B * solderPhi P A B = fisherMetricOp P A B * solderJ P A B ∧
    solderPhi P A B * spinVorticity P A B = -(fisherMetricOp P A B * solderJ P A B) ∧
    spinVorticity P A B * solderPhi P A B + solderPhi P A B * spinVorticity P A B = 0 ∧
    P * spinVorticity P A B = sheetPlus P A B ∧
    spinVorticity P A B * P = sheetPlus P A B ∧
    P * spinVorticity P A B + spinVorticity P A B * P - spinVorticity P A B =
      fisherMetricOp P A B ∧
    uncertaintyDressedGodelState P A B * uncertaintyDressedGodelState P A B -
        uncertaintyDressedGodelState P A B =
      fisherMetricOp P A B * fisherMetricOp P A B ∧
    chiralInv P * solderPhi P A B + solderPhi P A B * chiralInv P = 0 ∧
    deformedChiralGenerator P A B * deformedChiralGenerator P A B =
      1 + (4 : ℤ) • fisherMetricOp P A B ∧
    (1 : R) + chiralInv P = (2 : ℤ) • P ∧
    fisherMetricOp P A B * chiralInv P = spinVorticity P A B ∧
    (fisherMetricOp P A B * fisherMetricOp P A B) * chiralInv P =
      fisherMetricOp P A B * spinVorticity P A B := by
  have hP2 : P * P = P := hP
  have hVS : fisherMetricOp P A B * chiralInv P = spinVorticity P A B := by peirce_nf hP2
  dsimp [sheetPlus, uncertaintyDressedGodelState, deformedChiralGenerator]
  refine ⟨by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2,
          by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2,
          by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2,
          by peirce_nf hP2, hVS, ?_⟩
  rw [mul_assoc, hVS]

end HigherOrderPeirceBogoliubovRenormalization

section Rung5ExplicitBlockMatrixMetaProjector

/-- $2 \times 2$ conscious axiom projector $P = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def matPeirceP : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- $2 \times 2$ chiral involution $S_P = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$. -/
def matChiralS : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- $2 \times 2$ off-diagonal Gödel solder form $\Phi(a, b) = \begin{pmatrix} 0 & a \\ b & 0 \end{pmatrix}$. -/
def matSolderPhi (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, a; b, 0]

/-- $2 \times 2$ deformed involution generator $S_P + 2\Phi(a, b) = \begin{pmatrix} 1 & 2a \\ 2b & -1 \end{pmatrix}$. -/
def matDeformedGenerator (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2 * a; 2 * b, -1]

/-- **Rung 5 — Explicit $2 \times 2$ Block-Matrix Representation of the Renormalized Meta-Projector $\widetilde{P}(a, b)$**:
$$\widetilde{P}(a, b) := \frac{1}{2}\,I_2 + \frac{S_P + 2\Phi(a, b)}{2\sqrt{1 + 4ab}}
  = \begin{pmatrix} \frac{1 + (1 + 4ab)^{-1/2}}{2} & \frac{a}{\sqrt{1 + 4ab}} \\[6pt]
    \frac{b}{\sqrt{1 + 4ab}} & \frac{1 - (1 + 4ab)^{-1/2}}{2} \end{pmatrix}$$ -/
noncomputable def renormalizedMetaProjector2x2 (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ (1 + 1 / Real.sqrt (1 + 4 * a * b)) / 2, a / Real.sqrt (1 + 4 * a * b);
      b / Real.sqrt (1 + 4 * a * b), (1 - 1 / Real.sqrt (1 + 4 * a * b)) / 2 ]

/-- **Rung 5 Theorem A (`rung5_parameterized_meta_projector_2x2_theorem`) —
Exact Idempotence, Unit Trace & Zero-Defect Limit of the $2 \times 2$ Renormalized Meta-Projector $\widetilde{P}(a, b)$**:
For any real coupling amplitudes $a, b \in \mathbb{R}$ with $0 < 1 + 4ab$:
1. $(S_P + 2\Phi(a, b))^2 = (1 + 4ab)\,I_2$,
2. $\widetilde{P}(a, b)^2 = \widetilde{P}(a, b)$ (exact idempotence at all orders in $ab$),
3. $\mathrm{trace}(\widetilde{P}(a, b)) = 1$ (rank-1 projector trace),
4. $\widetilde{P}(0, 0) = P = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and
   $\widetilde{P}(1, 1) = \mathrm{concreteNormalizedMetaProjector}$. -/
theorem rung5_parameterized_meta_projector_2x2_theorem
    (a b : ℝ) (hpos : 0 < 1 + 4 * a * b) :
    matDeformedGenerator a b * matDeformedGenerator a b =
      (1 + 4 * a * b) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    renormalizedMetaProjector2x2 a b * renormalizedMetaProjector2x2 a b =
      renormalizedMetaProjector2x2 a b ∧
    Matrix.trace (renormalizedMetaProjector2x2 a b) = 1 ∧
    renormalizedMetaProjector2x2 0 0 = matPeirceP ∧
    renormalizedMetaProjector2x2 1 1 = concreteNormalizedMetaProjector := by
  have hs : (Real.sqrt (1 + 4 * a * b)) ^ 2 = 1 + 4 * a * b := Real.sq_sqrt (le_of_lt hpos)
  have hs0 : Real.sqrt (1 + 4 * a * b) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hpos' : 0 < 1 + b * 4 * a := by nlinarith [hpos]
  have hs' : (Real.sqrt (1 + b * 4 * a)) ^ 2 = 1 + b * 4 * a :=
    Real.sq_sqrt (le_of_lt hpos')
  have hs0' : Real.sqrt (1 + b * 4 * a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos')
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matDeformedGenerator, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [renormalizedMetaProjector2x2, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp [hs0, hs0'] <;> nlinarith [hs, hs']
  · simp [renormalizedMetaProjector2x2, Matrix.trace, Fin.sum_univ_two]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [renormalizedMetaProjector2x2, matPeirceP]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [renormalizedMetaProjector2x2, concreteNormalizedMetaProjector] <;> norm_num

end Rung5ExplicitBlockMatrixMetaProjector

section StageWG8AndRung5CyclotronicGeodesic

variable {R : Type*} [Ring R]

/-- Radial-to-chiral cosine $\cos\theta(r) := (1 + \sinh^2 r)^{-1/2}$ under $\tan\theta = \sinh r$. -/
noncomputable def godelChiralCos (r : ℝ) : ℝ :=
  1 / Real.sqrt (1 + Real.sinh r ^ 2)

/-- Radial-to-chiral sine $\sin\theta(r) := \sinh r\,(1 + \sinh^2 r)^{-1/2}$ under $\tan\theta = \sinh r$. -/
noncomputable def godelChiralSin (r : ℝ) : ℝ :=
  Real.sinh r / Real.sqrt (1 + Real.sinh r ^ 2)

/-- Radial Gödel solder loop $\Phi_{\mathrm{rad}}(r) := \cos\theta(r)\,\Phi + \sin\theta(r)\,J$. -/
noncomputable def godelRadialSolderLoop [Module ℝ R] (P A B : R) (r : ℝ) : R :=
  godelChiralCos r • solderPhi P A B + godelChiralSin r • solderJ P A B

/-- **Stage `𝔚𝔊₈` Theorem (`wg8_godel_1949_metric_coordinate_dictionary`) —
Exact Coordinate Dictionary with Gödel's 1949 Rotating Line Element**:
Under the radial-to-chiral map $\tan\theta = \sinh r$:
1. $\cos^2\theta(r) + \sin^2\theta(r) = 1$ and $\frac{\sin\theta(r)}{\cos\theta(r)} = \sinh r$,
2. $\cos^2\theta(r) - \sin^2\theta(r) = \frac{1 - \sinh^2 r}{1 + \sinh^2 r}$,
3. **Exact Radial Operator Metric Norm**:
   $$\Phi_{\mathrm{rad}}(r)^2 = \left(\frac{1 - \sinh^2 r}{1 + \sinh^2 r}\right) \bullet V$$
4. **Azimuthal Metric Proportionality**:
   $$g_{\varphi\varphi}(r) = \sinh^2 r\,(1 + \sinh^2 r)\,\big(\cos^2\theta(r) - \sin^2\theta(r)\big)$$ -/
theorem wg8_godel_1949_metric_coordinate_dictionary
    [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) (r : ℝ) :
    godelChiralCos r ^ 2 + godelChiralSin r ^ 2 = 1 ∧
    godelChiralSin r / godelChiralCos r = Real.sinh r ∧
    godelChiralCos r ^ 2 - godelChiralSin r ^ 2 =
      (1 - Real.sinh r ^ 2) / (1 + Real.sinh r ^ 2) ∧
    godelRadialSolderLoop P A B r * godelRadialSolderLoop P A B r =
      ((1 - Real.sinh r ^ 2) / (1 + Real.sinh r ^ 2)) • fisherMetricOp P A B ∧
    godelAzimuthalCoefficient r =
      Real.sinh r ^ 2 * (1 + Real.sinh r ^ 2) *
        (godelChiralCos r ^ 2 - godelChiralSin r ^ 2) := by
  have hpos : 0 < 1 + Real.sinh r ^ 2 := by positivity
  have hne : 1 + Real.sinh r ^ 2 ≠ 0 := ne_of_gt hpos
  have hsqrt_ne : Real.sqrt (1 + Real.sinh r ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hsqrt_sq : Real.sqrt (1 + Real.sinh r ^ 2) ^ 2 = 1 + Real.sinh r ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  have h_sum : godelChiralCos r ^ 2 + godelChiralSin r ^ 2 = 1 := by
    dsimp [godelChiralCos, godelChiralSin]
    rw [div_pow, div_pow, one_pow, ← add_div, hsqrt_sq, div_self hne]
  have h_tan : godelChiralSin r / godelChiralCos r = Real.sinh r := by
    dsimp [godelChiralCos, godelChiralSin]
    field_simp [hsqrt_ne]
  have h_diff : godelChiralCos r ^ 2 - godelChiralSin r ^ 2 =
      (1 - Real.sinh r ^ 2) / (1 + Real.sinh r ^ 2) := by
    dsimp [godelChiralCos, godelChiralSin]
    rw [div_pow, div_pow, one_pow, ← sub_div, hsqrt_sq]
  have hAlg := spacelike_to_closed_timelike_line_algebraic hP A B
  have h_loop_sq : godelRadialSolderLoop P A B r * godelRadialSolderLoop P A B r =
      ((1 - Real.sinh r ^ 2) / (1 + Real.sinh r ^ 2)) • fisherMetricOp P A B := by
    dsimp [godelRadialSolderLoop]
    rw [add_mul, mul_add, mul_add,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      hAlg.1, hAlg.2.1, mul_comm (godelChiralSin r) (godelChiralCos r),
      ← add_assoc, add_assoc ((godelChiralCos r * godelChiralCos r) • fisherMetricOp P A B),
      ← smul_add, hAlg.2.2.1, smul_zero, add_zero,
      smul_neg, ← sub_eq_add_neg, ← sub_smul,
      ← sq, ← sq, h_diff]
  have h_az : godelAzimuthalCoefficient r =
      Real.sinh r ^ 2 * (1 + Real.sinh r ^ 2) *
        (godelChiralCos r ^ 2 - godelChiralSin r ^ 2) := by
    rw [h_diff]
    dsimp [godelAzimuthalCoefficient]
    field_simp [hne]
  exact ⟨h_sum, h_tan, h_diff, h_loop_sq, h_az⟩

/-- Tangential velocity operator $\Phi'(\theta) := -\sin\theta\,\Phi + \cos\theta\,J$ along the
spin-rotated Gödel loop $\Phi(\theta)$. -/
noncomputable def rotatedSolderVelocity [Module ℝ R] (P A B : R) (θ : ℝ) : R :=
  (-Real.sin θ) • solderPhi P A B + Real.cos θ • solderJ P A B

/-- Tangential acceleration operator $\Phi''(\theta) := -\cos\theta\,\Phi - \sin\theta\,J$ along
the spin-rotated Gödel loop $\Phi(\theta)$. -/
noncomputable def rotatedSolderAcceleration [Module ℝ R] (P A B : R) (θ : ℝ) : R :=
  (-Real.cos θ) • solderPhi P A B + (-Real.sin θ) • solderJ P A B

/-- Right $\mathbb{R}$-scalar linearity of the associative Lie bracket `⁅X, c • Y⁆ = c • ⁅X, Y⁆`. -/
theorem lie_real_smul_right [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    (X Y : R) (c : ℝ) : ⁅X, c • Y⁆ = c • ⁅X, Y⁆ := by
  change X * (c • Y) - (c • Y) * X = c • (X * Y - Y * X)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]

/-- Left $\mathbb{R}$-scalar linearity of the associative Lie bracket `⁅c • X, Y⁆ = c • ⁅X, Y⁆`. -/
theorem lie_real_smul_left [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    (X Y : R) (c : ℝ) : ⁅c • X, Y⁆ = c • ⁅X, Y⁆ := by
  change (c • X) * Y - Y * (c • X) = c • (X * Y - Y * X)
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]

/-- `doubleVorticityAd` is additive in its argument. -/
theorem doubleVorticityAd_add (P A B X Y : R) :
    doubleVorticityAd P A B (X + Y) =
      doubleVorticityAd P A B X + doubleVorticityAd P A B Y := by
  change spinVorticity P A B *
      (spinVorticity P A B * (X + Y) - (X + Y) * spinVorticity P A B) -
      (spinVorticity P A B * (X + Y) - (X + Y) * spinVorticity P A B) *
        spinVorticity P A B =
    (spinVorticity P A B * (spinVorticity P A B * X - X * spinVorticity P A B) -
      (spinVorticity P A B * X - X * spinVorticity P A B) * spinVorticity P A B) +
    (spinVorticity P A B * (spinVorticity P A B * Y - Y * spinVorticity P A B) -
      (spinVorticity P A B * Y - Y * spinVorticity P A B) * spinVorticity P A B)
  noncomm_ring

/-- `doubleVorticityAd` commutes with $\mathbb{R}$-scalar multiplication. -/
theorem doubleVorticityAd_real_smul [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    (P A B : R) (c : ℝ) (X : R) :
    doubleVorticityAd P A B (c • X) = c • doubleVorticityAd P A B X := by
  dsimp [doubleVorticityAd]
  rw [lie_real_smul_right, lie_real_smul_right]

/-- **Rung 5 Theorem B (`rung5_cyclotronic_geodesic_along_closed_timelike_loop`) —
Exact Cyclotronic Geodesic & Conserved Symplectic Wronskian along the Closed Timelike Loop $\Phi(\theta)$**:
For every angle $\theta \in \mathbb{R}$ and any `IsIdempotentElem P`:
1. **Quarter-Turn Phase Shift & Harmonic Geodesic Equation**:
   $$\Phi'(\theta) = \Phi(\theta + \pi/2), \qquad \Phi''(\theta) + \Phi(\theta) = 0$$
2. **Velocity Metric Norm & Null Orthogonal Sum**:
   $$\Phi'(\theta)^2 = (-\cos(2\theta)) \bullet V, \qquad \Phi(\theta)^2 + \Phi'(\theta)^2 = 0$$
3. **Exact Cyclotronic Eigenvalue Equation under Spin-Vorticity Frame Dragging**:
   $$\mathrm{ad}_\Sigma^2\big(\Phi(\theta)\big) = ⁅\Sigma, ⁅\Sigma, \Phi(\theta)⁆⁆ = (4 : \mathbb{Z}) \bullet \big((V * V) * \Phi(\theta)\big)$$
4. **Conservation of the Symplectic Wronskian / Spin Angular Momentum along the Loop**:
   $$\boxed{⁅\Phi(\theta), \Phi'(\theta)⁆ = ⁅\Phi, J⁆ = -((2 : \mathbb{Z}) \bullet \Sigma)}$$ -/
theorem rung5_cyclotronic_geodesic_along_closed_timelike_loop
    [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) (θ : ℝ) :
    rotatedSolderVelocity P A B θ = rotatedSolderLoop P A B (θ + Real.pi / 2) ∧
    rotatedSolderAcceleration P A B θ + rotatedSolderLoop P A B θ = 0 ∧
    rotatedSolderVelocity P A B θ * rotatedSolderVelocity P A B θ =
      (-Real.cos (2 * θ)) • fisherMetricOp P A B ∧
    rotatedSolderLoop P A B θ * rotatedSolderLoop P A B θ +
        rotatedSolderVelocity P A B θ * rotatedSolderVelocity P A B θ = 0 ∧
    doubleVorticityAd P A B (rotatedSolderLoop P A B θ) =
      (4 : ℤ) • ((fisherMetricOp P A B * fisherMetricOp P A B) * rotatedSolderLoop P A B θ) ∧
    ⁅rotatedSolderLoop P A B θ, rotatedSolderVelocity P A B θ⁆ =
      ⁅solderPhi P A B, solderJ P A B⁆ ∧
    ⁅rotatedSolderLoop P A B θ, rotatedSolderVelocity P A B θ⁆ =
      -((2 : ℤ) • spinVorticity P A B) := by
  have hShift : rotatedSolderVelocity P A B θ = rotatedSolderLoop P A B (θ + Real.pi / 2) := by
    dsimp [rotatedSolderVelocity, rotatedSolderLoop]
    rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  have hOsc : rotatedSolderAcceleration P A B θ + rotatedSolderLoop P A B θ = 0 := by
    dsimp [rotatedSolderAcceleration, rotatedSolderLoop]
    rw [add_add_add_comm, ← add_smul, ← add_smul]
    simp
  have hLoopSq := (rotatedSolderLoop_sq_and_critical_angles hP A B θ).2.1
  have hVelSq : rotatedSolderVelocity P A B θ * rotatedSolderVelocity P A B θ =
      (-Real.cos (2 * θ)) • fisherMetricOp P A B := by
    rw [hShift, (rotatedSolderLoop_sq_and_critical_angles hP A B (θ + Real.pi / 2)).2.1,
      show 2 * (θ + Real.pi / 2) = 2 * θ + Real.pi by ring, Real.cos_add_pi]
  have hNullSum : rotatedSolderLoop P A B θ * rotatedSolderLoop P A B θ +
      rotatedSolderVelocity P A B θ * rotatedSolderVelocity P A B θ = 0 := by
    rw [hLoopSq, hVelSq, ← add_smul, add_neg_cancel, zero_smul]
  have hDrag := native_spin_and_centrifugal_frame_dragging hP A B
  have hCyc : doubleVorticityAd P A B (rotatedSolderLoop P A B θ) =
      (4 : ℤ) • ((fisherMetricOp P A B * fisherMetricOp P A B) * rotatedSolderLoop P A B θ) := by
    dsimp [rotatedSolderLoop]
    rw [doubleVorticityAd_add, doubleVorticityAd_real_smul, doubleVorticityAd_real_smul]
    change Real.cos θ • ⁅spinVorticity P A B, ⁅spinVorticity P A B, solderPhi P A B⁆⁆ +
        Real.sin θ • ⁅spinVorticity P A B, ⁅spinVorticity P A B, solderJ P A B⁆⁆ =
      (4 : ℤ) • ((fisherMetricOp P A B * fisherMetricOp P A B) *
        (Real.cos θ • solderPhi P A B + Real.sin θ • solderJ P A B))
    rw [hDrag.2.2.1, hDrag.2.2.2, mul_add, mul_smul_comm, mul_smul_comm,
      smul_add, smul_comm (Real.cos θ) (4 : ℤ), smul_comm (Real.sin θ) (4 : ℤ)]
  have hWronskian : ⁅rotatedSolderLoop P A B θ, rotatedSolderVelocity P A B θ⁆ =
      ⁅solderPhi P A B, solderJ P A B⁆ := by
    have h_lie_add (X Y Z : R) : ⁅X, Y + Z⁆ = ⁅X, Y⁆ + ⁅X, Z⁆ := by
      change X * (Y + Z) - (Y + Z) * X = (X * Y - Y * X) + (X * Z - Z * X); noncomm_ring
    have h_add_lie (X Y Z : R) : ⁅X + Y, Z⁆ = ⁅X, Z⁆ + ⁅Y, Z⁆ := by
      change (X + Y) * Z - Z * (X + Y) = (X * Z - Z * X) + (Y * Z - Z * Y); noncomm_ring
    have h_lie_self (X : R) : ⁅X, X⁆ = 0 := sub_self (X * X)
    have h_lie_skew (X Y : R) : ⁅Y, X⁆ = -⁅X, Y⁆ := by
      change Y * X - X * Y = -(X * Y - Y * X); noncomm_ring
    dsimp [rotatedSolderLoop, rotatedSolderVelocity]
    simp only [h_lie_add, h_add_lie, lie_real_smul_left, lie_real_smul_right,
      h_lie_self, smul_zero, zero_add, add_zero, smul_smul]
    rw [h_lie_skew (solderPhi P A B) (solderJ P A B), smul_neg, ← neg_smul, ← add_smul]
    have htrig : -(-Real.sin θ * Real.sin θ) + Real.cos θ * Real.cos θ = 1 := by
      calc -(-Real.sin θ * Real.sin θ) + Real.cos θ * Real.cos θ
        _ = Real.cos θ ^ 2 + Real.sin θ ^ 2 := by ring
        _ = 1 := Real.cos_sq_add_sin_sq θ
    rw [htrig, one_smul]
  have hWronskianSig : ⁅rotatedSolderLoop P A B θ, rotatedSolderVelocity P A B θ⁆ =
      -((2 : ℤ) • spinVorticity P A B) := by
    rw [hWronskian, (native_heisenberg_vorticity_lie_bracket hP A B).1]
  exact ⟨hShift, hOsc, hVelSq, hNullSum, hCyc, hWronskian, hWronskianSig⟩

end StageWG8AndRung5CyclotronicGeodesic

/-- **Stage `𝔚𝔊₉` Theorem (`wg9_hubble_atlas_three_trace_moments_classification`) —
Complete Classification of the Three Trace Moments of the *Hubble Atlas***:
For any two-sheeted galactic Peirce vortex $(A, B)$ in `Matrix n n R`:
1. **1-Point Unpolarized Trace (Gödel's Hubble Tally)**:
   $$\mathrm{trace}(\Sigma(A, B)) = 0$$
2. **1-Point Chiral Supertrace (Wheeler's Quantum Defect)**:
   $$\mathrm{Str}(\Sigma(A, B)) = \mathrm{trace}(S_P\,\Sigma(A, B)) = \mathrm{trace}(V(A, B)) = 2 \bullet \mathrm{trace}(AB)$$
3. **2-Point Quadratic Casimir (Local Light-Cone Tipping Variance)**:
   $$\Sigma(A, B)^2 = V(A, B)^2, \qquad
     \mathrm{trace}(\Sigma(A, B)^2) = \mathrm{trace}(V(A, B)^2) = 2 \bullet \mathrm{trace}((AB)^2)$$ -/
theorem wg9_hubble_atlas_three_trace_moments_classification
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (A B : Matrix n n R) :
    -- (1) 1-Point Unpolarized Trace vanishes identically
    Matrix.trace (blockVorticity A B) = 0 ∧
    -- (2) 1-Point Chiral Supertrace equals the Fisher Defect Trace 2 Tr(AB)
    blockSupertrace (blockVorticity A B) = Matrix.trace (blockFisher A B) ∧
    Matrix.trace (blockFisher A B) = 2 • Matrix.trace (A * B) ∧
    -- (3) 2-Point Quadratic Casimir equals V² with trace 2 Tr((AB)²)
    blockVorticity A B ^ 2 = blockFisher A B ^ 2 ∧
    Matrix.trace (blockVorticity A B ^ 2) = Matrix.trace (blockFisher A B ^ 2) ∧
    Matrix.trace (blockVorticity A B ^ 2) = 2 • Matrix.trace ((A * B) ^ 2) := by
  have h0 := hubble_atlas_global_vorticity_trace_zero A B
  have h1 := hubble_atlas_odd_power_trace_zero A B 1
  have hSq : blockVorticity A B ^ 2 = blockFisher A B ^ 2 :=
    h1.2.1
  have hTrSq : Matrix.trace (blockVorticity A B ^ 2) = 2 • Matrix.trace ((A * B) ^ 2) := by
    exact h1.2.2.1
  exact ⟨h0.1, h1.2.2.2, h0.2, hSq, by rw [hSq], hTrSq⟩

/-- Reachability along the complete higher-order continuation `𝔚𝔊₆ ≺ 𝔚𝔊₇ ≺ 𝔚𝔊₈ ≺ 𝔚𝔊₉ ≺ 𝔚𝔊₁₀`. -/
theorem causalEdge_W6_to_W10 :
    Relation.TransGen causalEdge
      .W6_MasterWheelerGodelSynthesis
      .W10_CyclotronicGeodesicAndNilpotentHorizon := by
  have h69 := causalEdge_W6_to_W9
  exact Relation.TransGen.tail h69 trivial

/-- Full 10-stage causal reachability `𝔚𝔊₁ ≺⁺ 𝔚𝔊₁₀`. -/
theorem causalEdge_W1_to_W10 :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W10_CyclotronicGeodesicAndNilpotentHorizon :=
  Relation.TransGen.trans causalEdge_W1_to_W6 causalEdge_W6_to_W10

/-- Symmetric cubic trial state $\Psi_{\mathrm{sym}, 1} := \Psi_1 - V\Phi = P + \Phi - \Sigma - V\Phi$,
which overshoots the $+V^2$ defect to $-V^2 + V^3$. -/
def symmetricCubicTrialState {R : Type*} [Ring R] (P A B : R) : R :=
  uncertaintyDressedGodelState P A B - fisherMetricOp P A B * solderPhi P A B

/-- **Rung 5 Theorem 1 (`two_step_heisenberg_jordan_defect_cancellation_ladder`) —
The Two-Step Heisenberg–Jordan Defect Cancellation Ladder & Symmetric Overshoot Contrast**:
Over every associative ring `[Ring R]` with `IsIdempotentElem P`:
1. **Stage 0 (Raw Gödel State $\Psi_0 = P + \Phi$)**:
   $$(P + \Phi)^2 - (P + \Phi) = V$$
2. **Stage 1 (Heisenberg Counterterm $-\Sigma$, $\Psi_1 = P + \Phi - \Sigma$)**:
   $$\Psi_1^2 - \Psi_1 = \Sigma^2 = V^2$$
3. **Symmetric Trial Overshoot ($\Psi_{\mathrm{sym}, 1} = \Psi_1 - V\Phi$)**:
   Because $\{\Phi, V\Phi\} = 2V^2$ and $(V\Phi)^2 = V^3$, subtracting the symmetric cubic term
   $-V\Phi$ overshoots $+V^2$ and generates higher-order defect $-V^2 + V^3$:
   $$\Psi_{\mathrm{sym}, 1}^2 - \Psi_{\mathrm{sym}, 1} = -(V^2) + V^3$$
4. **Stage 2 (Asymmetric Chiral Jordan-Triple Counterterm $-V N_+$, $\widehat{P} = \Psi_1 - V N_+$)**:
   Because $(V N_+)^2 = 0$, $\{P, V N_+\} - V N_+ = 0$, $\{\Sigma, V N_+\} = 0$, and
   $\{\Phi, V N_+\} = +V^2$, the division-free polynomial state $\widehat{P}$ is **strictly idempotent**
   at degree 3:
   $$\boxed{\widehat{P}^2 = \widehat{P}}$$ -/
theorem two_step_heisenberg_jordan_defect_cancellation_ladder
    {R : Type*} [Ring R] {P : R} (hP : IsIdempotentElem P) (A B : R) :
    (P + solderPhi P A B) * (P + solderPhi P A B) - (P + solderPhi P A B) =
      fisherMetricOp P A B ∧
    uncertaintyDressedGodelState P A B * uncertaintyDressedGodelState P A B -
        uncertaintyDressedGodelState P A B =
      fisherMetricOp P A B * fisherMetricOp P A B ∧
    symmetricCubicTrialState P A B * symmetricCubicTrialState P A B -
        symmetricCubicTrialState P A B =
      -(fisherMetricOp P A B * fisherMetricOp P A B) +
        fisherMetricOp P A B * fisherMetricOp P A B * fisherMetricOp P A B ∧
    bruhatRenormalizedGodelState P A B * bruhatRenormalizedGodelState P A B =
      bruhatRenormalizedGodelState P A B := by
  have hP2 : P * P = P := hP
  refine ⟨(godel_incompleteness_idempotent_defect hP A B).2.2.1,
    ?_,
    ?_, (jordan_triple_counterterm_idempotent hP A B).2.2.2.2⟩
  · calc
      uncertaintyDressedGodelState P A B * uncertaintyDressedGodelState P A B -
          uncertaintyDressedGodelState P A B =
        spinVorticity P A B * spinVorticity P A B :=
          (heisenberg_counterterm_idempotent_defect hP A B).2.2.1
      _ = fisherMetricOp P A B * fisherMetricOp P A B :=
          (heisenberg_counterterm_idempotent_defect hP A B).2.2.2
  · dsimp [symmetricCubicTrialState, uncertaintyDressedGodelState]
    peirce_nf hP2

/-- **Rung 5 — Explicit $2 \times 2$ Block-Matrix Bruhat Meta-Projector $\widehat{P}_{\mathrm{block}}(A, C)$**:
Over any commutative ring `R`, the two-step Heisenberg–Jordan renormalized state
$\widehat{P} = P + \Phi - \Sigma - V N_+$ has the division-free block matrix form:
$$\widehat{P}_{\mathrm{block}}(A, C) = \begin{pmatrix} 1 - AC & A - ACA \\ C & CA \end{pmatrix}$$ -/
def blockBruhatMetaProjector {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (A C : Matrix n n R) :
    Matrix (Sum n n) (Sum n n) R :=
  Matrix.fromBlocks (1 - A * C) (A - A * C * A) C (C * A)

/-- **Rung 5 Theorem 2 (`blockBruhatMetaProjector_idempotent_and_trace`) —
Exact Idempotence and Rank-Preserving Trace of the $2 \times 2$ Block Bruhat Meta-Projector**:
For any matrices $A, C \in \mathrm{Matrix}_n(R)$:
1. $\widehat{P}_{\mathrm{block}}(A, C)^2 = \widehat{P}_{\mathrm{block}}(A, C)$ (division-free idempotence),
2. $\mathrm{trace}(\widehat{P}_{\mathrm{block}}(A, C)) = \mathrm{trace}(I_n)$ (exact trace preservation $\mathrm{Tr}(1 - AC) + \mathrm{Tr}(CA) = \mathrm{Tr}(1)$). -/
theorem blockBruhatMetaProjector_idempotent_and_trace
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (A C : Matrix n n R) :
    blockBruhatMetaProjector A C * blockBruhatMetaProjector A C =
      blockBruhatMetaProjector A C ∧
    Matrix.trace (blockBruhatMetaProjector A C) =
      Matrix.trace (1 : Matrix n n R) := by
  refine ⟨?_, ?_⟩
  · dsimp [blockBruhatMetaProjector]
    rw [Matrix.fromBlocks_multiply]
    congr 1 <;> noncomm_ring
  · dsimp [blockBruhatMetaProjector]
    have htraceBlocks {X Y Z W : Matrix n n R} :
        Matrix.trace (Matrix.fromBlocks X Y Z W) = Matrix.trace X + Matrix.trace W := by
      simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
    rw [htraceBlocks, Matrix.trace_sub, Matrix.trace_mul_comm A C]
    simp [Matrix.trace_one]

/-- **Stage `𝔚𝔊₁₀` / Rung 5 Theorem 3 (`godel_horizon_nilpotent_chiral_splitting`) —
Nilpotent Light-Cone Splitting at the Critical Gödel Horizon ($\theta_c = \pi / 4$ & $\theta'_c = 3\pi / 4$)**:
At the critical Gödel horizon $\theta_c = \pi / 4$ ($\sinh r_c = 1$), the rotated Gödel sentence
$\Phi(\pi/4)$ and its tangential velocity $\Phi'(\pi/4)$ collapse into the pure upper- and
lower-triangular nilpotent Peirce generators:
$$\Phi(\pi/4) = \sqrt{2} \bullet N_+, \qquad \Phi'(\pi/4) = (-\sqrt{2}) \bullet N_-, \qquad
  \Phi(3\pi/4) = (-\sqrt{2}) \bullet N_-$$
with exact square-zero light-cone nilpotency $\Phi(\pi/4)^2 = \Phi'(\pi/4)^2 = 0$. -/
theorem godel_horizon_nilpotent_chiral_splitting
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) :
    solderPhi P A B + solderJ P A B = (2 : ℝ) • peircePlus P A ∧
    solderJ P A B - solderPhi P A B = (-2 : ℝ) • peirceMinus P B ∧
    rotatedSolderLoop P A B (Real.pi / 4) = Real.sqrt 2 • peircePlus P A ∧
    rotatedSolderVelocity P A B (Real.pi / 4) = (-Real.sqrt 2) • peirceMinus P B ∧
    rotatedSolderLoop P A B (3 * Real.pi / 4) = (-Real.sqrt 2) • peirceMinus P B ∧
    rotatedSolderLoop P A B (Real.pi / 4) * rotatedSolderLoop P A B (Real.pi / 4) = 0 ∧
    rotatedSolderVelocity P A B (Real.pi / 4) * rotatedSolderVelocity P A B (Real.pi / 4) = 0 := by
  have hPlus : solderPhi P A B + solderJ P A B = (2 : ℝ) • peircePlus P A := by
    change conePlus P A + coneMinus P B + (conePlus P A - coneMinus P B) =
      (2 : ℝ) • conePlus P A
    rw [two_smul ℝ (conePlus P A)]
    abel
  have hMinus : solderJ P A B - solderPhi P A B = (-2 : ℝ) • peirceMinus P B := by
    change (conePlus P A - coneMinus P B) -
      (conePlus P A + coneMinus P B) = (-2 : ℝ) • coneMinus P B
    rw [show (-2 : ℝ) • coneMinus P B = -((2 : ℝ) • coneMinus P B) by rw [neg_smul],
      two_smul ℝ (coneMinus P B)]
    abel
  have hsqrt2 : (Real.sqrt 2 / 2 : ℝ) * 2 = Real.sqrt 2 := by ring
  have hsqrt2_neg : (Real.sqrt 2 / 2 : ℝ) * (-2) = -Real.sqrt 2 := by ring
  have hLoopPi4 : rotatedSolderLoop P A B (Real.pi / 4) = Real.sqrt 2 • peircePlus P A := by
    dsimp [rotatedSolderLoop]
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four, ← smul_add, hPlus, smul_smul, hsqrt2]
  have hVelPi4 : rotatedSolderVelocity P A B (Real.pi / 4) = (-Real.sqrt 2) • peirceMinus P B := by
    dsimp [rotatedSolderVelocity]
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four, neg_smul,
      ← sub_eq_neg_add, ← smul_sub, hMinus, smul_smul, hsqrt2_neg]
  have hLoop3Pi4 : rotatedSolderLoop P A B (3 * Real.pi / 4) = (-Real.sqrt 2) • peirceMinus P B := by
    rw [show (3 * Real.pi / 4 : ℝ) = Real.pi / 4 + Real.pi / 2 by ring,
      ← (rung5_cyclotronic_geodesic_along_closed_timelike_loop hP A B (Real.pi / 4)).1, hVelPi4]
  have hSq1 := (rotatedSolderLoop_sq_and_critical_angles hP A B (Real.pi / 4)).2.2.2.2.1
  have hSq2 : rotatedSolderVelocity P A B (Real.pi / 4) * rotatedSolderVelocity P A B (Real.pi / 4) = 0 := by
    rw [(rung5_cyclotronic_geodesic_along_closed_timelike_loop hP A B (Real.pi / 4)).2.2.1,
      show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two, neg_zero, zero_smul]
  exact ⟨hPlus, hMinus, hLoopPi4, hVelPi4, hLoop3Pi4, hSq1, hSq2⟩

/-! ## §8. Bichiral Bruhat midpoint identities (Rung 7 core)

The midpoint formula is first recorded for arbitrary idempotents. This keeps
the geometric interpretation separate from the ring identity: its defect is
exactly the negative square of the separation of the two idempotents. -/

/-- For any two idempotents, the unnormalized midpoint defect is the negative
square of their difference. This is division-free and valid in any ring. -/
theorem idempotent_pair_midpoint_defect {B : Type*} [Ring B]
    (p q : B) (hp : p * p = p) (hq : q * q = q) :
    (p + q) * (p + q) - (p + q + p + q) = -((q - p) * (q - p)) := by
  noncomm_ring [hp, hq]

/-- For an idempotent pair, the anticommutator excess equals the same midpoint
defect and hence equals `-(q-p)^2`. -/
theorem idempotent_pair_anticommutator_excess {B : Type*} [Ring B]
    (p q : B) (hp : p * p = p) (hq : q * q = q) :
    (p * q + q * p) - (p + q) = -((q - p) * (q - p)) := by
  noncomm_ring [hp, hq]

/-- Rung 7 bichiral Bruhat identities. The two cubic-corrected Peirce
operators are idempotents; their difference, midpoint defect, anticommutator
excess, and commutator are recorded without interpreting them as geometric
holonomy or K-theoretic data. -/
theorem wg14_bichiral_bruhat_midpoint_and_commutator
    {R : Type*} [Ring R] {P : R} (hP : IsIdempotentElem P) (A B : R) :
    bruhatRenormalizedGodelStateMinus P A B - bruhatRenormalizedGodelState P A B =
        fisherMetricOp P A B * solderJ P A B ∧
    (bruhatRenormalizedGodelState P A B + bruhatRenormalizedGodelStateMinus P A B) *
        (bruhatRenormalizedGodelState P A B + bruhatRenormalizedGodelStateMinus P A B) -
        (bruhatRenormalizedGodelState P A B + bruhatRenormalizedGodelStateMinus P A B +
          bruhatRenormalizedGodelState P A B + bruhatRenormalizedGodelStateMinus P A B) =
      fisherMetricOp P A B * fisherMetricOp P A B * fisherMetricOp P A B ∧
    (bruhatRenormalizedGodelState P A B * bruhatRenormalizedGodelStateMinus P A B +
        bruhatRenormalizedGodelStateMinus P A B * bruhatRenormalizedGodelState P A B) -
        (bruhatRenormalizedGodelState P A B + bruhatRenormalizedGodelStateMinus P A B) =
      fisherMetricOp P A B * fisherMetricOp P A B * fisherMetricOp P A B ∧
    ⁅bruhatRenormalizedGodelState P A B, bruhatRenormalizedGodelStateMinus P A B⁆ =
      fisherMetricOp P A B * (1 - 2 * fisherMetricOp P A B) * solderPhi P A B -
        fisherMetricOp P A B * (2 - fisherMetricOp P A B) * spinVorticity P A B := by
  have hP2 : P * P = P := hP
  have hp : IsIdempotentElem (bruhatRenormalizedGodelState P A B) :=
    (jordan_triple_counterterm_idempotent hP A B).2.2.2.2
  have hm : IsIdempotentElem (bruhatRenormalizedGodelStateMinus P A B) := by
    exact (bruhat_conjugation_chiral_pair hP A B).2.2.2.2.2.2.2
  have hdiff : bruhatRenormalizedGodelStateMinus P A B -
      bruhatRenormalizedGodelState P A B =
      fisherMetricOp P A B * solderJ P A B := by
    dsimp [bruhatRenormalizedGodelStateMinus, bruhatRenormalizedGodelState,
      uncertaintyDressedGodelState]
    peirce_nf hP2
  have hdiffSq : (bruhatRenormalizedGodelStateMinus P A B -
      bruhatRenormalizedGodelState P A B) *
      (bruhatRenormalizedGodelStateMinus P A B -
        bruhatRenormalizedGodelState P A B) =
      -(fisherMetricOp P A B * fisherMetricOp P A B * fisherMetricOp P A B) := by
    rw [hdiff]
    dsimp [solderJ]
    peirce_nf hP2
  refine ⟨hdiff, ?_, ?_, ?_⟩
  · rw [idempotent_pair_midpoint_defect _ _ hp hm, hdiffSq]
    simp
  · rw [idempotent_pair_anticommutator_excess _ _ hp hm, hdiffSq]
    simp
  · rw [lie_eq_peirce_comm, show (2 : R) = 1 + 1 by norm_num]
    dsimp [bruhatRenormalizedGodelState, bruhatRenormalizedGodelStateMinus,
      uncertaintyDressedGodelState, peircePlus, peirceMinus]
    peirce_nf hP2

/-- **Stage `𝔚𝔊₁₁` / Rung 6 Theorem 1 (`wg11_bruhat_ordering_defect_and_chiral_difference`) —
Bruhat Ordering Defect = Heisenberg Commutator & Chiral Difference Identity**:
For any idempotent `P` (`IsIdempotentElem P`) in an associative ring `R`:
1. **Bruhat Ordering Defect = Heisenberg Uncertainty**:
   $$G_- - G_+ = (1 + N_-)(1 - N_+) - (1 - N_+)(1 + N_-) = [N_+, N_-] = \Sigma$$
2. **Chiral Difference Identity**:
   $$\widehat{P}_- - \widehat{P}_+ = V J = \Sigma \Phi$$ -/
theorem wg11_bruhat_ordering_defect_and_chiral_difference
    {R : Type*} [Ring R] {P : R} (hP : IsIdempotentElem P) (A B : R) :
    bruhatGaugeMinus P A B - bruhatGaugePlus P A B = spinVorticity P A B ∧
    bruhatRenormalizedGodelStateMinus P A B - bruhatRenormalizedGodelState P A B =
      fisherMetricOp P A B * solderJ P A B ∧
    fisherMetricOp P A B * solderJ P A B =
      spinVorticity P A B * solderPhi P A B := by
  have hP2 : P * P = P := hP
  refine ⟨?_, (wg14_bichiral_bruhat_midpoint_and_commutator hP A B).1, by peirce_nf hP2⟩
  dsimp [bruhatGaugeMinus, bruhatGaugePlus]
  peirce_nf hP2

/-- **Rung 6 — Opposite Chiral $2 \times 2$ Block-Matrix Bruhat Meta-Projector
$\widehat{P}_-(A, C)$**:
Over any commutative ring `R`, the opposite chiral Bruhat renormalized state
$\widehat{P}_- = P + \Phi - \Sigma - V N_- = G_- P G_-^{-1}$ has the division-free block matrix form:
$$\widehat{P}_-(A, C) = \begin{pmatrix} 1 - AC & A \\ C - CAC & CA \end{pmatrix}$$ -/
def blockBruhatMetaProjectorMinus {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (A C : Matrix n n R) :
    Matrix (Sum n n) (Sum n n) R :=
  Matrix.fromBlocks (1 - A * C) A (C - C * A * C) (C * A)

/-- **Stage `𝔚𝔊₁₂` / Rung 6 Theorem 2 (`wg12_finite_matrix_trace_equalities`) —
Finite-Matrix Trace Equalities & $2 \times 2$ Chiral Block Idempotence**:
For any matrices $A, C \in \mathrm{Matrix}_n(R)$:
1. $\widehat{P}_-(A, C)^2 = \widehat{P}_-(A, C)$ (division-free idempotence of the opposite chiral partner),
2. $\mathrm{trace}(\widehat{P}_-(A, C)) = \mathrm{trace}(I_n)$,
3. $\mathrm{trace}(\widehat{P}_+(A, C)) = \mathrm{trace}(\widehat{P}_-(A, C))$ (chiral trace equality).
These finite-matrix trace identities do not establish module-rank equality or a K-theory/Fredholm-index statement. -/
theorem wg12_finite_matrix_trace_equalities
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (A C : Matrix n n R) :
    blockBruhatMetaProjectorMinus A C * blockBruhatMetaProjectorMinus A C =
      blockBruhatMetaProjectorMinus A C ∧
    Matrix.trace (blockBruhatMetaProjectorMinus A C) =
      Matrix.trace (1 : Matrix n n R) ∧
    Matrix.trace (blockBruhatMetaProjector A C) =
      Matrix.trace (blockBruhatMetaProjectorMinus A C) := by
  have hIdem : blockBruhatMetaProjectorMinus A C * blockBruhatMetaProjectorMinus A C =
      blockBruhatMetaProjectorMinus A C := by
    dsimp [blockBruhatMetaProjectorMinus]
    rw [Matrix.fromBlocks_multiply]
    congr 1 <;> noncomm_ring
  have hTrMinus : Matrix.trace (blockBruhatMetaProjectorMinus A C) =
      Matrix.trace (1 : Matrix n n R) := by
    dsimp [blockBruhatMetaProjectorMinus]
    have htraceBlocks {X Y Z W : Matrix n n R} :
        Matrix.trace (Matrix.fromBlocks X Y Z W) = Matrix.trace X + Matrix.trace W := by
      simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
    rw [htraceBlocks, Matrix.trace_sub, Matrix.trace_mul_comm A C]
    simp [Matrix.trace_one]
  refine ⟨hIdem, hTrMinus, ?_⟩
  rw [(blockBruhatMetaProjector_idempotent_and_trace A C).2, hTrMinus]

/-- **Stage `𝔚𝔊₁₃` / Rung 6 Theorem 3 (`wg13_six_phase_rotor_identities_and_horizon_anticommutator`) —
Six-Phase Rotor Identities & Nilpotent-Horizon Anticommutator**:
For the algebraic rotor $\Phi(\theta) = \cos\theta\,\Phi + \sin\theta\,J$:
1. The six critical orbital phases $\theta \in \{0, \pi/4, \pi/2, 3\pi/4, \pi, 2\pi\}$ evaluate to
   $\Phi$, $\sqrt{2}\,N_+$, $J$, $-\sqrt{2}\,N_-$, $-\Phi$, and $\Phi$; these identities do not construct a spacetime loop or spinor parallel transport,
2. **Entry/Exit Nilpotent Horizon Anticommutator**:
   $$\{(\Phi + J), -(\Phi - J)\} = -(4 : R) * V, \qquad
     \{\Phi(\pi/4), \Phi(3\pi/4)\} = (-2 : \mathbb{R}) \bullet V$$ -/
theorem wg13_six_phase_rotor_identities_and_horizon_anticommutator
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) :
    rotatedSolderLoop P A B 0 = solderPhi P A B ∧
    rotatedSolderLoop P A B (Real.pi / 4) = Real.sqrt 2 • peircePlus P A ∧
    rotatedSolderLoop P A B (Real.pi / 2) = solderJ P A B ∧
    rotatedSolderLoop P A B (3 * Real.pi / 4) = (-Real.sqrt 2) • peirceMinus P B ∧
    rotatedSolderLoop P A B Real.pi = -solderPhi P A B ∧
    rotatedSolderLoop P A B (2 * Real.pi) = solderPhi P A B ∧
    (solderPhi P A B + solderJ P A B) * (-(solderPhi P A B - solderJ P A B)) +
        (-(solderPhi P A B - solderJ P A B)) * (solderPhi P A B + solderJ P A B) =
      -((4 : ℤ) • fisherMetricOp P A B) ∧
    rotatedSolderLoop P A B (Real.pi / 4) * rotatedSolderLoop P A B (3 * Real.pi / 4) +
        rotatedSolderLoop P A B (3 * Real.pi / 4) * rotatedSolderLoop P A B (Real.pi / 4) =
      (-2 : ℝ) • fisherMetricOp P A B := by
  have hP2 : P * P = P := hP
  have hCrit := rotatedSolderLoop_sq_and_critical_angles hP A B 0
  have hSplit := godel_horizon_nilpotent_chiral_splitting hP A B
  have hTwoPi : rotatedSolderLoop P A B (2 * Real.pi) = solderPhi P A B := by
    dsimp [rotatedSolderLoop]
    rw [Real.cos_two_pi, Real.sin_two_pi, one_smul, zero_smul, add_zero]
  have hPi : rotatedSolderLoop P A B Real.pi = -solderPhi P A B := by
    dsimp [rotatedSolderLoop]
    rw [Real.cos_pi, Real.sin_pi, neg_one_smul, zero_smul, add_zero]
  have hRingAnti :
      (solderPhi P A B + solderJ P A B) * (-(solderPhi P A B - solderJ P A B)) +
        (-(solderPhi P A B - solderJ P A B)) * (solderPhi P A B + solderJ P A B) =
      -((4 : ℤ) • fisherMetricOp P A B) := by
    peirce_nf hP2
  have hProd1 : Real.sqrt 2 * (-Real.sqrt 2) = (-2 : ℝ) := by
    calc
      Real.sqrt 2 * (-Real.sqrt 2) = -(Real.sqrt 2 ^ 2) := by ring
      _ = -2 := by rw [Real.sq_sqrt (by norm_num)]
  have hProd2 : (-Real.sqrt 2) * Real.sqrt 2 = (-2 : ℝ) := by
    calc
      (-Real.sqrt 2) * Real.sqrt 2 = -(Real.sqrt 2 ^ 2) := by ring
      _ = -2 := by rw [Real.sq_sqrt (by norm_num)]
  have hLoopAnti :
      rotatedSolderLoop P A B (Real.pi / 4) * rotatedSolderLoop P A B (3 * Real.pi / 4) +
        rotatedSolderLoop P A B (3 * Real.pi / 4) * rotatedSolderLoop P A B (Real.pi / 4) =
      (-2 : ℝ) • fisherMetricOp P A B := by
    rw [hSplit.2.2.1, hSplit.2.2.2.2.1, smul_mul_smul_comm, smul_mul_smul_comm,
      hProd1, hProd2, ← smul_add]
    rfl
  exact ⟨hCrit.2.2.1, hSplit.2.2.1, hCrit.2.2.2.2.2.1,
    hSplit.2.2.2.2.1, hPi,
    hTwoPi, hRingAnti, hLoopAnti⟩

/-- Rectangular row and column maps on the two-sheeted matrix carrier.
The overlap theorem below proves their inner products and loop product; it
does not assert outer factorizations of the Bruhat projectors. -/
def moritaLPlus {n : Type*} [Fintype n] [DecidableEq n]
    {S : Type*} [Ring S] (A C : Matrix n n S) : Matrix (Sum n n) n S :=
  fun i j => Sum.elim (fun k => (1 - A * C) k j) (fun k => C k j) i

/-- Upper-chiral rectangular row map `[1, A]` on `Sum n n`. -/
def moritaRPlus {n : Type*} [Fintype n] [DecidableEq n]
    {S : Type*} [Ring S] (A : Matrix n n S) : Matrix n (Sum n n) S :=
  fun i j => Sum.elim (fun k => if i = k then 1 else 0) (fun k => A i k) j

/-- Lower-chiral rectangular column map `[1; C]` on `Sum n n`. -/
def moritaLMinus {n : Type*} [Fintype n] [DecidableEq n]
    {S : Type*} [Ring S] (C : Matrix n n S) : Matrix (Sum n n) n S :=
  fun i j => Sum.elim (fun k => if k = j then 1 else 0) (fun k => C k j) i

/-- Lower-chiral rectangular row map `[1 - A C, A]` on `Sum n n`. -/
def moritaRMinus {n : Type*} [Fintype n] [DecidableEq n]
    {S : Type*} [Ring S] (A C : Matrix n n S) : Matrix n (Sum n n) S :=
  fun i j => Sum.elim (fun k => (1 - A * C) i k) (fun k => A i k) j

/-- The four rectangular inner products and their cyclotomic loop product.
These are literal matrix identities; no categorical equivalence or outer
factorization of a Bruhat projector is asserted. -/
theorem rectangular_peirce_cross_overlap_identities
    {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [Ring S]
    (A C : Matrix n n S) :
    moritaRPlus A * moritaLPlus A C = 1 ∧
    moritaRMinus A C * moritaLMinus C = 1 ∧
    moritaRPlus A * moritaLMinus C = 1 + A * C ∧
    moritaRMinus A C * moritaLPlus A C = 1 - A * C + (A * C) * (A * C) ∧
    (moritaRPlus A * moritaLMinus C) * (moritaRMinus A C * moritaLPlus A C) =
      1 + (A * C) * (A * C) * (A * C) := by
  have h₁ : moritaRPlus A * moritaLPlus A C = 1 := by
    ext i j
    simp [Matrix.mul_apply, moritaLPlus, moritaRPlus, Fintype.sum_sum_type,
      Matrix.one_apply]
  have h₂ : moritaRMinus A C * moritaLMinus C = 1 := by
    ext i j
    simp [Matrix.mul_apply, moritaLMinus, moritaRMinus, Fintype.sum_sum_type,
      Matrix.one_apply]
  have h₃ : moritaRPlus A * moritaLMinus C = 1 + A * C := by
    ext i j
    simp [Matrix.mul_apply, moritaRPlus, moritaLMinus, Fintype.sum_sum_type,
      Matrix.one_apply]
  have hpoly : (1 - A * C) * (1 - A * C) + A * C =
      1 - A * C + (A * C) * (A * C) := by noncomm_ring
  have h₄ : moritaRMinus A C * moritaLPlus A C = 1 - A * C + (A * C) * (A * C) := by
    ext i j
    simp only [Matrix.mul_apply, moritaRMinus, moritaLPlus, Sum.elim_inl,
      Sum.elim_inr, Fintype.sum_sum_type]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply]
    exact congrArg (fun M : Matrix n n S => M i j) hpoly
  have h₅ : (1 + A * C) * (1 - A * C + (A * C) * (A * C)) =
      1 + (A * C) * (A * C) * (A * C) := by noncomm_ring
  exact ⟨h₁, h₂, h₃, h₄, by rw [h₃, h₄]; exact h₅⟩

/-- **Stage `𝔚𝔊₁₆` / Rung 7 Theorem 2 (`wg16_cyclotomic_polynomial_and_matrix_overlaps`) —
Cyclotomic Polynomial Identities**:
For $Q_+ = N_+N_-$ (`sheetPlus P A B`), the theorem proves
$(1+Q_+)(1-Q_+ + Q_+^2)=1+Q_+^3$ in an associative ring. Its other conjuncts prove
three polynomial equalities for matrix variables $M_A,M_C$. The matrix equalities are not
identified with rectangular Morita overlaps: this theorem defines no such factors and establishes
no geometric holonomy. -/
theorem wg16_cyclotomic_polynomial_and_matrix_overlaps
    {R : Type*} [Ring R] (P A B : R)
    {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]
    (M_A M_C : Matrix n n S) :
    (1 + sheetPlus P A B) * (1 - sheetPlus P A B + sheetPlus P A B * sheetPlus P A B) =
      1 + sheetPlus P A B * sheetPlus P A B * sheetPlus P A B ∧
    ((1 : Matrix n n S) - M_A * M_C) + M_A * M_C = 1 ∧
    ((1 : Matrix n n S) - M_A * M_C) * ((1 : Matrix n n S) - M_A * M_C) + M_A * M_C =
      1 - M_A * M_C + (M_A * M_C) * (M_A * M_C) ∧
    ((1 : Matrix n n S) + M_A * M_C) *
        (1 - M_A * M_C + (M_A * M_C) * (M_A * M_C)) =
      1 + (M_A * M_C) * (M_A * M_C) * (M_A * M_C) := by
  refine ⟨by noncomm_ring, by noncomm_ring, by noncomm_ring, by noncomm_ring⟩

/-- Reachability from Stage `𝔚𝔊₁` to the terminal Rung 7 Stage `𝔚𝔊₁₆`. -/
theorem causalEdge_W1_to_W16 :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W16_CyclotomicPolynomialAndRectangularOverlapIdentities := by
  have h1_6 := causalEdge_W1_to_W6
  have h1_7 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W7_PeirceBogoliubovRenormalization :=
    Relation.TransGen.tail h1_6 trivial
  have h1_8 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W8_GodelMetricCoordinateDictionary :=
    Relation.TransGen.tail h1_7 trivial
  have h1_9 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W9_HubbleAtlasThreeTraceMomentsAndRung5 :=
    Relation.TransGen.tail h1_8 trivial
  have h1_10 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W10_CyclotronicGeodesicAndNilpotentHorizon :=
    Relation.TransGen.tail h1_9 trivial
  have h1_11 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W11_UnimodularBruhatConjugationAndChiralPair :=
    Relation.TransGen.tail h1_10 trivial
  have h1_12 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W12_FiniteMatrixTraceEqualities :=
    Relation.TransGen.tail h1_11 trivial
  have h1_13 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W13_SixPhaseRotorIdentitiesAndHorizonAnticommutator :=
    Relation.TransGen.tail h1_12 trivial
  have h1_14 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W14_BichiralAnticommutatorAndMidpointCubicDefect :=
    Relation.TransGen.tail h1_13 trivial
  have h1_15 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W15_BichiralCommutatorAndVorticityInterference :=
    Relation.TransGen.tail h1_14 trivial
  exact Relation.TransGen.tail h1_15 trivial

/-- **Selected 16-Stage Wheeler–Gödel–Bruhat Algebraic Summary
(`wheeler_godel_sixteen_stage_master_synthesis`)**:
Collects selected formal results across the 16-stage poset `𝔚𝔊₁ ≺ ⋯ ≺ 𝔚𝔊₁₆`:
1. Full poset reachability `𝔚𝔊₁ ≺⁺ 𝔚𝔊₁₆` and acyclicity across all 16 stages,
2. Rung 5 Two-Step Heisenberg–Jordan Defect Cancellation (`two_step_heisenberg_jordan_defect_cancellation_ladder`),
3. Rung 6 Unimodular Bruhat Conjugation & Chiral Ordering Defect (`bruhat_conjugation_chiral_pair`,
   `wg11_bruhat_ordering_defect_and_chiral_difference`),
4. Rung 6 $2 \times 2$ Chiral Block Idempotence & Finite-Matrix Trace Equalities
   (`wg12_finite_matrix_trace_equalities`),
5. Rung 6 Six-Phase Rotor Identities & Nilpotent-Horizon Anticommutator
   (`wg13_six_phase_rotor_identities_and_horizon_anticommutator`),
6. Rung 7 Bichiral Anticommutator, Scaled Midpoint Cubic Defect $V^3$, & Bichiral Commutator
   (`wg14_bichiral_bruhat_midpoint_and_commutator`),
7. Rung 7 Cyclotomic Polynomial Identity $(1 + Q_+)(1 - Q_+ + Q_+^2) = 1 + Q_+^3$
   (`wg16_cyclotomic_polynomial_and_matrix_overlaps`) and literal rectangular overlap products
   (`rectangular_peirce_cross_overlap_identities`). -/
theorem wheeler_godel_sixteen_stage_master_synthesis
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R)
    {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]
    (M_A M_C : Matrix n n S) :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W16_CyclotomicPolynomialAndRectangularOverlapIdentities ∧
    (∀ s : WheelerGodelStage, ¬ Relation.TransGen causalEdge s s) ∧
    bruhatGaugeMinus P A B - bruhatGaugePlus P A B = spinVorticity P A B ∧
    bruhatGaugePlus P A B * P * bruhatGaugePlusInv P A B =
      bruhatRenormalizedGodelState P A B ∧
    bruhatGaugeMinus P A B * P * bruhatGaugeMinusInv P A B =
      bruhatRenormalizedGodelStateMinus P A B ∧
    Matrix.trace (blockBruhatMetaProjector M_A M_C) =
      Matrix.trace (blockBruhatMetaProjectorMinus M_A M_C) ∧
    rotatedSolderLoop P A B (Real.pi / 4) * rotatedSolderLoop P A B (3 * Real.pi / 4) +
        rotatedSolderLoop P A B (3 * Real.pi / 4) * rotatedSolderLoop P A B (Real.pi / 4) =
      (-2 : ℝ) • fisherMetricOp P A B ∧
    (bruhatRenormalizedGodelState P A B + bruhatRenormalizedGodelStateMinus P A B) *
        (bruhatRenormalizedGodelState P A B + bruhatRenormalizedGodelStateMinus P A B) -
        (bruhatRenormalizedGodelState P A B + bruhatRenormalizedGodelStateMinus P A B +
          bruhatRenormalizedGodelState P A B + bruhatRenormalizedGodelStateMinus P A B) =
      fisherMetricOp P A B * fisherMetricOp P A B * fisherMetricOp P A B ∧
    ⁅bruhatRenormalizedGodelState P A B, bruhatRenormalizedGodelStateMinus P A B⁆ =
      fisherMetricOp P A B * (1 - 2 * fisherMetricOp P A B) * solderPhi P A B -
        fisherMetricOp P A B * (2 - fisherMetricOp P A B) * spinVorticity P A B ∧
    (1 + sheetPlus P A B) * (1 - sheetPlus P A B + sheetPlus P A B * sheetPlus P A B) =
      1 + sheetPlus P A B * sheetPlus P A B * sheetPlus P A B ∧
    (moritaRPlus M_A * moritaLMinus M_C) * (moritaRMinus M_A M_C * moritaLPlus M_A M_C) =
      1 + (M_A * M_C) * (M_A * M_C) * (M_A * M_C) := by
  have hBruhat := bruhat_conjugation_chiral_pair hP A B
  have hWG11 := wg11_bruhat_ordering_defect_and_chiral_difference hP A B
  have hWG12 := wg12_finite_matrix_trace_equalities M_A M_C
  have hWG13 := wg13_six_phase_rotor_identities_and_horizon_anticommutator hP A B
  have hWG14 := wg14_bichiral_bruhat_midpoint_and_commutator hP A B
  have hWG16 := wg16_cyclotomic_polynomial_and_matrix_overlaps P A B M_A M_C
  have hMorita := rectangular_peirce_cross_overlap_identities M_A M_C
  exact ⟨causalEdge_W1_to_W16, causalEdge_acyclic, hWG11.1, hBruhat.2.2.2.2.1,
    hBruhat.2.2.2.2.2.1, hWG12.2.2, hWG13.2.2.2.2.2.2.2, hWG14.2.1, hWG14.2.2.2,
    hWG16.1, hMorita.2.2.2.2⟩

/-! ## §9. Rung 8 (`𝔚𝔊₁₈ ≺ 𝔚𝔊₁₉ ≺ 𝔚𝔊₂₀ ≺ 𝔚𝔊₂₁`): Connes Non-Commutative Geometry, Spectral Distance, Krein Horizon Flip & Connes–Chern Cyclic Index -/

/-- Two-sheeted diagonal coordinate element $a(\alpha, \beta) := \alpha \bullet P + \beta \bullet (1 - P)$
assigning scalar amplitude $\alpha$ to the formal sheet $P$ and $\beta$ to the complement sheet $1 - P$. -/
def twoSheetCoord {S R : Type*} [Ring R] [Semiring S] [Module S R]
    (P : R) (α β : S) : R :=
  α • P + β • (1 - P)

/-- **Two-Sheeted Coordinate Algebra Homomorphism (`twoSheetCoord_mul`)**:
For any idempotent `P` (`IsIdempotentElem P`), the two-sheeted coordinate map
$(\alpha, \beta) \mapsto a(\alpha, \beta) = \alpha \bullet P + \beta \bullet (1 - P)$
is multiplicative and maps $(1, 1)$ to $1$:
$$a(\alpha_1, \beta_1) * a(\alpha_2, \beta_2) = a(\alpha_1 \alpha_2, \beta_1 \beta_2), \qquad a(1, 1) = 1$$ -/
theorem twoSheetCoord_mul {R : Type*} [Ring R] [Module ℝ R]
    [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (α₁ β₁ α₂ β₂ : ℝ) :
    twoSheetCoord P α₁ β₁ * twoSheetCoord P α₂ β₂ =
      twoSheetCoord P (α₁ * α₂) (β₁ * β₂) ∧
    twoSheetCoord P (1 : ℝ) (1 : ℝ) = 1 := by
  have hP2 : P * P = P := hP
  have hP_comp : P * (1 - P) = 0 := by noncomm_ring [hP2]
  have hcomp_P : (1 - P) * P = 0 := by noncomm_ring [hP2]
  have hcomp_sq : (1 - P) * (1 - P) = 1 - P := by noncomm_ring [hP2]
  refine ⟨?_, ?_⟩
  · dsimp [twoSheetCoord]
    rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm,
      smul_mul_smul_comm, smul_mul_smul_comm, hP2, hP_comp, hcomp_P, hcomp_sq,
      smul_zero, smul_zero, add_zero, zero_add]
  · dsimp [twoSheetCoord]
    rw [one_smul, one_smul, add_sub_cancel]

/-- Commutator with the complementary projector $1 - P$ negates the commutator with $P$:
$⁅\mathcal{D}, 1 - P⁆ = -⁅\mathcal{D}, P⁆$. -/
theorem lie_one_sub {R : Type*} [Ring R] (D P : R) :
    ⁅D, 1 - P⁆ = -⁅D, P⁆ := by
  change D * (1 - P) - (1 - P) * D = -(D * P - P * D)
  noncomm_ring

/-- **Connes Exterior Derivation on Two-Sheeted Coordinates (`lie_twoSheetCoord`)**:
For any operator $\mathcal{D} \in R$, any projector $P \in R$, and any scalars $\alpha, \beta \in \mathbb{R}$:
$$⁅\mathcal{D}, a(\alpha, \beta)⁆ = (\alpha - \beta) \bullet ⁅\mathcal{D}, P⁆$$ -/
theorem lie_twoSheetCoord {R : Type*} [Ring R] [Module ℝ R]
    [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    (D P : R) (α β : ℝ) :
    ⁅D, twoSheetCoord P α β⁆ = (α - β) • ⁅D, P⁆ := by
  have h_lie_add (X Y Z : R) : ⁅X, Y + Z⁆ = ⁅X, Y⁆ + ⁅X, Z⁆ := by
    change X * (Y + Z) - (Y + Z) * X = (X * Y - Y * X) + (X * Z - Z * X)
    noncomm_ring
  dsimp [twoSheetCoord]
  rw [h_lie_add, lie_real_smul_right, lie_real_smul_right, lie_one_sub,
    smul_neg, ← sub_eq_add_neg, ← sub_smul]

/-- **Stages `𝔚𝔊₁₈`–`𝔚𝔊₁₉` / Rung 8 Theorem 1 (`wg18_wg19_even_spectral_triple_and_connes_differential_factorization`) —
Even Connes Spectral Triple, Non-Commutative 1-Forms & Clifford Factorization of Heisenberg Uncertainty $\Sigma$**:
Over any associative ring `R` (`[Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]`)
with idempotent axiom projector `P` (`IsIdempotentElem P`), grading involution $\gamma := S_P = 2P - 1$
(`chiralInv P`), and Dirac operator $\mathcal{D} := \Phi = N_+ + N_-$ (`solderPhi P A B`):
1. **Even Grading & Chirality ($\gamma^2 = 1$, $[\gamma, a(\alpha,\beta)] = 0$, $\{\mathcal{D}, \gamma\} = 0$)**:
   $$S_P^2 = 1, \qquad ⁅S_P, P⁆ = 0, \qquad ⁅S_P, a(\alpha, \beta)⁆ = 0, \qquad \Phi S_P + S_P \Phi = 0$$
2. **Dirac Laplacian & Quartic Casimir ($\mathcal{D}^2 = V$ and $\mathcal{D}^4 = V^2 = \Sigma^2$)**:
   $$\Phi^2 = V, \qquad (\Phi^2)^2 = \Sigma^2$$
3. **Connes Non-Commutative 1-Form of $P$ and $a(\alpha, \beta)$ ($d_{\mathcal{D}} X := ⁅\Phi, X⁆$)**:
   $$⁅\Phi, P⁆ = -J = \Phi S_P, \qquad ⁅J, P⁆ = -\Phi, \qquad
     ⁅\Phi, a(\alpha, \beta)⁆ = -(\alpha - \beta) \bullet J$$
4. **Square of the Fundamental Connes 1-Form ($(d_{\mathcal{D}} P)^2 = -V = -\mathcal{D}^2$)**:
   $$⁅\Phi, P⁆ * ⁅\Phi, P⁆ = -V, \qquad \Phi^2 + ⁅\Phi, P⁆^2 = 0$$
5. **Exact Clifford Factorization of the Heisenberg Uncertainty Commutator $\Sigma = [N_+, N_-]$**:
   $$\boxed{\Phi * ⁅\Phi, P⁆ = \Sigma, \qquad ⁅\Phi, P⁆ * \Phi = -\Sigma, \qquad
     \Phi * ⁅\Phi, P⁆ + ⁅\Phi, P⁆ * \Phi = 0}$$
6. **Connes–Chern Grading Product**:
   $$S_P * \Phi * ⁅\Phi, P⁆ = V$$ -/
theorem wg18_wg19_even_spectral_triple_and_connes_differential_factorization
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) (α β : ℝ) :
    chiralInv P * chiralInv P = 1 ∧
    ⁅chiralInv P, P⁆ = 0 ∧
    ⁅chiralInv P, twoSheetCoord P α β⁆ = 0 ∧
    solderPhi P A B * chiralInv P + chiralInv P * solderPhi P A B = 0 ∧
    solderPhi P A B * solderPhi P A B = fisherMetricOp P A B ∧
    (solderPhi P A B * solderPhi P A B) * (solderPhi P A B * solderPhi P A B) =
      spinVorticity P A B * spinVorticity P A B ∧
    ⁅solderPhi P A B, P⁆ = -solderJ P A B ∧
    ⁅solderPhi P A B, P⁆ = solderPhi P A B * chiralInv P ∧
    ⁅solderJ P A B, P⁆ = -solderPhi P A B ∧
    ⁅solderPhi P A B, twoSheetCoord P α β⁆ = -((α - β) • solderJ P A B) ∧
    ⁅solderPhi P A B, P⁆ * ⁅solderPhi P A B, P⁆ = -fisherMetricOp P A B ∧
    solderPhi P A B * solderPhi P A B + ⁅solderPhi P A B, P⁆ * ⁅solderPhi P A B, P⁆ = 0 ∧
    solderPhi P A B * ⁅solderPhi P A B, P⁆ = spinVorticity P A B ∧
    ⁅solderPhi P A B, P⁆ * solderPhi P A B = -spinVorticity P A B ∧
    solderPhi P A B * ⁅solderPhi P A B, P⁆ + ⁅solderPhi P A B, P⁆ * solderPhi P A B = 0 ∧
    chiralInv P * solderPhi P A B * ⁅solderPhi P A B, P⁆ = fisherMetricOp P A B := by
  have hP2 : P * P = P := hP
  have hGradP : ⁅chiralInv P, P⁆ = 0 := by
    rw [lie_eq_peirce_comm]; peirce_nf hP2
  have hGradCoord : ⁅chiralInv P, twoSheetCoord P α β⁆ = 0 := by
    rw [lie_twoSheetCoord, hGradP, smul_zero]
  have hDiffP : ⁅solderPhi P A B, P⁆ = -solderJ P A B := by
    rw [lie_eq_peirce_comm]; peirce_nf hP2
  have hDiffCoord : ⁅solderPhi P A B, twoSheetCoord P α β⁆ = -((α - β) • solderJ P A B) := by
    rw [lie_twoSheetCoord, hDiffP, smul_neg]
  simp only [lie_eq_peirce_comm] at hGradP hDiffP ⊢
  refine ⟨by peirce_nf hP2, hGradP, hGradCoord, by peirce_nf hP2, by peirce_nf hP2,
    by peirce_nf hP2, hDiffP, by peirce_nf hP2, by peirce_nf hP2, hDiffCoord,
    by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2,
    by peirce_nf hP2, by peirce_nf hP2⟩

/-- **Stage `𝔚𝔊₂₀` / Rung 8 Theorem 2 (`wg20_connes_inter_sheet_spectral_distance_and_mode_scaling`) —
Connes 1-Form Metric Seminorm, Inter-Sheet Spectral Distance & Cubic Bruhat Scaling**:
For any idempotent `P` (`IsIdempotentElem P`), any two-sheeted coordinate element
$a(\alpha, \beta) = \alpha \bullet P + \beta \bullet (1 - P)$, and any positive eigenvalue/norm scale
$\lambda > 0$ of $V = \Sigma^2$:
1. **Quadratic Connes 1-Form Metric Identity**:
   $$-\big(⁅\Phi, a(\alpha, \beta)⁆ * ⁅\Phi, a(\alpha, \beta)⁆\big) = (\alpha - \beta)^2 \bullet V$$
2. **Classical Commutative Disconnection ($\Sigma = 0 \implies d_{\mathcal{D}} a = 0$ Metric Collapse)**:
   $$\Sigma = 0 \;\Longrightarrow\; -\big(⁅\Phi, a(\alpha, \beta)⁆ * ⁅\Phi, a(\alpha, \beta)⁆\big) = 0$$
3. **Lipschitz 1-Form Constraint & Attainment at $d_{\mathcal{D}}(\lambda) = 1 / \sqrt{\lambda}$**:
   $$|\alpha - \beta| \cdot \sqrt{\lambda} \le 1 \;\Longleftrightarrow\; |\alpha - \beta| \le \frac{1}{\sqrt{\lambda}}, \qquad
     \left|\frac{1}{\sqrt{\lambda}} - 0\right| \cdot \sqrt{\lambda} = 1$$
4. **Gödel Cyclotronic Frequency Identity ($\omega_{\mathrm{cyc}} = 2\lambda$) & Rung-5 Cubic Bruhat Scaling**:
   $$\frac{1}{\sqrt{\lambda}} = \sqrt{\frac{2}{2\lambda}}, \qquad
     \left(\frac{1}{\sqrt{\lambda}}\right)^{-3} = \lambda\,\sqrt{\lambda}$$ -/
theorem wg20_connes_inter_sheet_spectral_distance_and_mode_scaling
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) (α β l : ℝ) (hl : 0 < l) :
    -(⁅solderPhi P A B, twoSheetCoord P α β⁆ * ⁅solderPhi P A B, twoSheetCoord P α β⁆) =
      ((α - β) ^ 2) • fisherMetricOp P A B ∧
    (spinVorticity P A B = 0 →
      -(⁅solderPhi P A B, twoSheetCoord P α β⁆ * ⁅solderPhi P A B, twoSheetCoord P α β⁆) = 0) ∧
    (|α - β| * Real.sqrt l ≤ 1 ↔ |α - β| ≤ 1 / Real.sqrt l) ∧
    |(1 / Real.sqrt l) - 0| * Real.sqrt l = 1 ∧
    |(1 / Real.sqrt l) - 0| = 1 / Real.sqrt l ∧
    1 / Real.sqrt l = Real.sqrt (2 / (2 * l)) ∧
    (1 / Real.sqrt l)⁻¹ ^ 3 = l * Real.sqrt l := by
  have hP2 : P * P = P := hP
  have hDiffSq : ⁅solderPhi P A B, P⁆ * ⁅solderPhi P A B, P⁆ = -fisherMetricOp P A B := by
    simp only [lie_eq_peirce_comm]; peirce_nf hP2
  have hCoordSq :
      -(⁅solderPhi P A B, twoSheetCoord P α β⁆ * ⁅solderPhi P A B, twoSheetCoord P α β⁆) =
        ((α - β) ^ 2) • fisherMetricOp P A B := by
    rw [lie_twoSheetCoord, smul_mul_smul_comm, ← sq, hDiffSq, smul_neg, neg_neg]
  have hClassZero :
      spinVorticity P A B = 0 →
        -(⁅solderPhi P A B, twoSheetCoord P α β⁆ * ⁅solderPhi P A B, twoSheetCoord P α β⁆) = 0 := by
    intro hSig0
    have hV0 : fisherMetricOp P A B = 0 := by
      calc
        fisherMetricOp P A B = chiralInv P * spinVorticity P A B := by peirce_nf hP2
        _ = chiralInv P * 0 := by rw [hSig0]
        _ = 0 := mul_zero (chiralInv P)
    rw [hCoordSq, hV0, smul_zero]
  have hsqrt_pos : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hsqrt_ne : Real.sqrt l ≠ 0 := ne_of_gt hsqrt_pos
  have hLip : |α - β| * Real.sqrt l ≤ 1 ↔ |α - β| ≤ 1 / Real.sqrt l := by
    constructor
    · intro h
      have hmul := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (le_of_lt hsqrt_pos))
      rwa [mul_assoc, mul_inv_cancel₀ hsqrt_ne, mul_one, ← one_div, one_mul] at hmul
    · intro h
      have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hsqrt_pos)
      rwa [one_div, inv_mul_cancel₀ hsqrt_ne] at hmul
  have hAttain2 : |(1 / Real.sqrt l) - 0| = 1 / Real.sqrt l := by
    rw [sub_zero, abs_of_nonneg (div_nonneg zero_le_one (le_of_lt hsqrt_pos))]
  have hAttain1 : |(1 / Real.sqrt l) - 0| * Real.sqrt l = 1 := by
    rw [hAttain2, one_div, inv_mul_cancel₀ hsqrt_ne]
  have hCycFreq : 1 / Real.sqrt l = Real.sqrt (2 / (2 * l)) := by
    have hdiv : (2 : ℝ) / (2 * l) = 1 / l := by
      have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
      calc (2 : ℝ) / (2 * l) = (2 * 1) / (2 * l) := by ring
      _ = 1 / l := mul_div_mul_left 1 l h2
    rw [hdiv, Real.sqrt_div zero_le_one l, Real.sqrt_one]
  have hCubicScale : (1 / Real.sqrt l)⁻¹ ^ 3 = l * Real.sqrt l := by
    rw [one_div, inv_inv]
    calc
      Real.sqrt l ^ 3 = Real.sqrt l ^ 2 * Real.sqrt l := by ring
      _ = l * Real.sqrt l := by rw [Real.sq_sqrt (le_of_lt hl)]
  exact ⟨hCoordSq, hClassZero, hLip, hAttain1, hAttain2, hCycFreq, hCubicScale⟩

/-- General Chiral–Connes Differential Identity for any planar rotor combination
$X = c_1 \bullet \Phi + c_2 \bullet J$:
1. $⁅X, P⁆ = -\big(c_1 \bullet J + c_2 \bullet \Phi\big) = X * S_P = -(S_P * X)$,
2. $-\big(⁅X, P⁆ * ⁅X, P⁆\big) = X * X$. -/
theorem planar_rotor_connes_diff_and_krein_sq
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) (c₁ c₂ : ℝ) :
    let X := c₁ • solderPhi P A B + c₂ • solderJ P A B
    ⁅X, P⁆ = -(c₁ • solderJ P A B + c₂ • solderPhi P A B) ∧
    ⁅X, P⁆ = X * chiralInv P ∧
    ⁅X, P⁆ = -(chiralInv P * X) ∧
    -(⁅X, P⁆ * ⁅X, P⁆) = X * X := by
  have hP2 : P * P = P := hP
  have h_add_lie (U W Z : R) : ⁅U + W, Z⁆ = ⁅U, Z⁆ + ⁅W, Z⁆ := by
    change (U + W) * Z - Z * (U + W) = (U * Z - Z * U) + (W * Z - Z * W)
    noncomm_ring
  have hPhiDiff : ⁅solderPhi P A B, P⁆ = -solderJ P A B := by
    rw [lie_eq_peirce_comm]; peirce_nf hP2
  have hJDiff : ⁅solderJ P A B, P⁆ = -solderPhi P A B := by
    rw [lie_eq_peirce_comm]; peirce_nf hP2
  have hPhiR : -solderJ P A B = solderPhi P A B * chiralInv P := by peirce_nf hP2
  have hJR : -solderPhi P A B = solderJ P A B * chiralInv P := by peirce_nf hP2
  have hPhiL : -solderJ P A B = -(chiralInv P * solderPhi P A B) := by peirce_nf hP2
  have hJL : -solderPhi P A B = -(chiralInv P * solderJ P A B) := by peirce_nf hP2
  dsimp only
  have h1 : ⁅c₁ • solderPhi P A B + c₂ • solderJ P A B, P⁆ =
      -(c₁ • solderJ P A B + c₂ • solderPhi P A B) := by
    rw [h_add_lie, lie_real_smul_left, lie_real_smul_left, hPhiDiff, hJDiff,
      smul_neg, smul_neg, ← neg_add]
  have h2 : ⁅c₁ • solderPhi P A B + c₂ • solderJ P A B, P⁆ =
      (c₁ • solderPhi P A B + c₂ • solderJ P A B) * chiralInv P := by
    rw [h_add_lie, lie_real_smul_left, lie_real_smul_left, hPhiDiff, hJDiff,
      hPhiR, hJR, add_mul, smul_mul_assoc, smul_mul_assoc]
  have h3 : ⁅c₁ • solderPhi P A B + c₂ • solderJ P A B, P⁆ =
      -(chiralInv P * (c₁ • solderPhi P A B + c₂ • solderJ P A B)) := by
    rw [h_add_lie, lie_real_smul_left, lie_real_smul_left, hPhiDiff, hJDiff,
      hPhiL, hJL, smul_neg, smul_neg, ← neg_add, mul_add, mul_smul_comm, mul_smul_comm]
  have h4 : -(⁅c₁ • solderPhi P A B + c₂ • solderJ P A B, P⁆ *
      ⁅c₁ • solderPhi P A B + c₂ • solderJ P A B, P⁆) =
      (c₁ • solderPhi P A B + c₂ • solderJ P A B) *
        (c₁ • solderPhi P A B + c₂ • solderJ P A B) := by
    have hS2 : chiralInv P * chiralInv P = 1 := by peirce_nf hP2
    set X := c₁ • solderPhi P A B + c₂ • solderJ P A B
    have hprod : ⁅X, P⁆ * ⁅X, P⁆ = (X * chiralInv P) * -(chiralInv P * X) :=
      congrArg₂ (· * ·) h2 h3
    calc
      -(⁅X, P⁆ * ⁅X, P⁆)
          = -((X * chiralInv P) * -(chiralInv P * X)) := congrArg Neg.neg hprod
      _ = X * (chiralInv P * chiralInv P) * X := by noncomm_ring
      _ = X * X := by rw [hS2, mul_one]
  exact ⟨h1, h2, h3, h4⟩

/-- Two-sheeted block projector $P_{\mathrm{block}} = \begin{pmatrix} I & 0 \\ 0 & 0 \end{pmatrix}$
on `Matrix (Sum n n) (Sum n n) S`. -/
def blockProjP {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S] :
    Matrix (Sum n n) (Sum n n) S :=
  Matrix.fromBlocks 1 0 0 0

/-- Two-sheeted block Dirac / Gödel sentence operator
$\Phi_{\mathrm{block}}(A, B) = N_+(A) + N_-(B) = \begin{pmatrix} 0 & A \\ B & 0 \end{pmatrix}$. -/
def blockSolderPhi {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]
    (A B : Matrix n n S) : Matrix (Sum n n) (Sum n n) S :=
  blockUpper A + blockLower B

/-- **Stage `𝔚𝔊₂₁` / Rung 8 Theorem 3 (`wg21_lorentzian_krein_connes_horizon_flip_and_chern_index`) —
Lorentzian Krein–Connes Horizon Signature Flip & Connes–Chern Cyclic Trace Identity**:
Along the rotated Dirac loop $\mathcal{D}(\theta) = \Phi(\theta) = \cos\theta\,\Phi + \sin\theta\,J$
(`rotatedSolderLoop P A B θ`) and the radial Gödel parameterization $\tan\theta = \sinh r$
(`godelRadialSolderLoop P A B r`):
1. **Rotated Connes 1-Form**:
   $$⁅\Phi(\theta), P⁆ = -\big(\cos\theta \bullet J + \sin\theta \bullet \Phi\big) = \Phi(\theta) * S_P$$
2. **Lorentzian Krein–Connes Metric Operator $G_{\mathcal{D}}(\theta) := -⁅\Phi(\theta), P⁆^2$**:
   $$-\big(⁅\Phi(\theta), P⁆ * ⁅\Phi(\theta), P⁆\big) = \Phi(\theta)^2 = \cos(2\theta) \bullet V, \qquad
     \Phi(\theta)^2 + ⁅\Phi(\theta), P⁆^2 = 0$$
3. **Null Square-Zero Connes Differential at the Critical Gödel Horizon ($\theta_c = \pi / 4$)**:
   $$⁅\Phi(\pi/4), P⁆ = (-\sqrt{2}) \bullet N_+, \qquad
     -\big(⁅\Phi(\pi/4), P⁆ * ⁅\Phi(\pi/4), P⁆\big) = 0$$
4. **Radial Gödel Connes Metric Transmutation ($\tan\theta = \sinh r$)**:
   $$-\big(⁅\Phi_{\mathrm{rad}}(r), P⁆ * ⁅\Phi_{\mathrm{rad}}(r), P⁆\big) =
     \left(\frac{1 - \sinh^2 r}{1 + \sinh^2 r}\right) \bullet V$$
5. **Block-Matrix Connes–Chern 0-Cocycle Identity ($S_P \mathcal{D} [\mathcal{D}, P] = V$)**:
   $$S_P * \Phi_{\mathrm{block}}(A, C) * ⁅\Phi_{\mathrm{block}}(A, C), P_{\mathrm{block}}⁆ = V_{\mathrm{block}}(A, C), \qquad
     \mathrm{trace}\!\left(S_P * \Phi_{\mathrm{block}}(A, C) * ⁅\Phi_{\mathrm{block}}(A, C), P_{\mathrm{block}}⁆\right) =
       2 \bullet \mathrm{trace}(A C)$$ -/
theorem wg21_lorentzian_krein_connes_horizon_flip_and_chern_index
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) (θ r : ℝ)
    {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]
    (M_A M_C : Matrix n n S) :
    ⁅rotatedSolderLoop P A B θ, P⁆ =
      -(Real.cos θ • solderJ P A B + Real.sin θ • solderPhi P A B) ∧
    -(⁅rotatedSolderLoop P A B θ, P⁆ * ⁅rotatedSolderLoop P A B θ, P⁆) =
      Real.cos (2 * θ) • fisherMetricOp P A B ∧
    rotatedSolderLoop P A B θ * rotatedSolderLoop P A B θ +
      ⁅rotatedSolderLoop P A B θ, P⁆ * ⁅rotatedSolderLoop P A B θ, P⁆ = 0 ∧
    ⁅rotatedSolderLoop P A B (Real.pi / 4), P⁆ = (-Real.sqrt 2) • peircePlus P A ∧
    -(⁅rotatedSolderLoop P A B (Real.pi / 4), P⁆ *
        ⁅rotatedSolderLoop P A B (Real.pi / 4), P⁆) = 0 ∧
    -(⁅godelRadialSolderLoop P A B r, P⁆ * ⁅godelRadialSolderLoop P A B r, P⁆) =
      ((1 - Real.sinh r ^ 2) / (1 + Real.sinh r ^ 2)) • fisherMetricOp P A B ∧
    blockChiralInv * blockSolderPhi M_A M_C *
        ⁅blockSolderPhi M_A M_C, blockProjP⁆ =
      blockFisher M_A M_C ∧
    Matrix.trace (blockChiralInv * blockSolderPhi M_A M_C *
        ⁅blockSolderPhi M_A M_C, blockProjP⁆) =
      2 • Matrix.trace (M_A * M_C) := by
  have hP2 : P * P = P := hP
  have hPlanar := planar_rotor_connes_diff_and_krein_sq hP A B (Real.cos θ) (Real.sin θ)
  have hLoopSq := (rotatedSolderLoop_sq_and_critical_angles hP A B θ).2.1
  have hKreinAngle :
      -(⁅rotatedSolderLoop P A B θ, P⁆ * ⁅rotatedSolderLoop P A B θ, P⁆) =
        Real.cos (2 * θ) • fisherMetricOp P A B := by
    calc
      -(⁅rotatedSolderLoop P A B θ, P⁆ * ⁅rotatedSolderLoop P A B θ, P⁆)
          = rotatedSolderLoop P A B θ * rotatedSolderLoop P A B θ := hPlanar.2.2.2
      _ = Real.cos (2 * θ) • fisherMetricOp P A B := hLoopSq
  have hNullSum :
      rotatedSolderLoop P A B θ * rotatedSolderLoop P A B θ +
        ⁅rotatedSolderLoop P A B θ, P⁆ * ⁅rotatedSolderLoop P A B θ, P⁆ = 0 := by
    have hLoopSqEq :
        -(⁅rotatedSolderLoop P A B θ, P⁆ * ⁅rotatedSolderLoop P A B θ, P⁆) =
          rotatedSolderLoop P A B θ * rotatedSolderLoop P A B θ :=
      hPlanar.2.2.2
    rw [← hLoopSqEq, neg_add_cancel]
  have hHorizDiff :
      ⁅rotatedSolderLoop P A B (Real.pi / 4), P⁆ = (-Real.sqrt 2) • peircePlus P A := by
    have hPi4 :
        ⁅rotatedSolderLoop P A B (Real.pi / 4), P⁆ =
          rotatedSolderLoop P A B (Real.pi / 4) * chiralInv P :=
      (planar_rotor_connes_diff_and_krein_sq hP A B
        (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4))).2.1
    rw [hPi4, (godel_horizon_nilpotent_chiral_splitting hP A B).2.2.1, smul_mul_assoc,
      show peircePlus P A * chiralInv P = -peircePlus P A by peirce_nf hP2,
      smul_neg, ← neg_smul]
  have hHorizSq :
      -(⁅rotatedSolderLoop P A B (Real.pi / 4), P⁆ *
          ⁅rotatedSolderLoop P A B (Real.pi / 4), P⁆) = 0 := by
    have hPi4Sq :
        -(⁅rotatedSolderLoop P A B (Real.pi / 4), P⁆ *
            ⁅rotatedSolderLoop P A B (Real.pi / 4), P⁆) =
          rotatedSolderLoop P A B (Real.pi / 4) * rotatedSolderLoop P A B (Real.pi / 4) :=
      (planar_rotor_connes_diff_and_krein_sq hP A B
        (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4))).2.2.2
    rw [hPi4Sq, (godel_horizon_nilpotent_chiral_splitting hP A B).2.2.2.2.2.1]
  have hRadSq :
      -(⁅godelRadialSolderLoop P A B r, P⁆ * ⁅godelRadialSolderLoop P A B r, P⁆) =
        ((1 - Real.sinh r ^ 2) / (1 + Real.sinh r ^ 2)) • fisherMetricOp P A B := by
    have hRadPlanar :
        -(⁅godelRadialSolderLoop P A B r, P⁆ * ⁅godelRadialSolderLoop P A B r, P⁆) =
          godelRadialSolderLoop P A B r * godelRadialSolderLoop P A B r :=
      (planar_rotor_connes_diff_and_krein_sq hP A B
        (godelChiralCos r) (godelChiralSin r)).2.2.2
    rw [hRadPlanar, (wg8_godel_1949_metric_coordinate_dictionary hP A B r).2.2.2.1]
  have hBlockChern :
      blockChiralInv * blockSolderPhi M_A M_C *
          ⁅blockSolderPhi M_A M_C, blockProjP⁆ =
        blockFisher M_A M_C := by
    change blockChiralInv * (blockUpper M_A + blockLower M_C) *
        ((blockUpper M_A + blockLower M_C) * blockProjP -
          blockProjP * (blockUpper M_A + blockLower M_C)) =
      blockFisher M_A M_C
    rw [blockFisher_eq_fromBlocks]
    dsimp [blockChiralInv, blockUpper, blockLower, blockProjP]
    rw [sub_eq_add_neg]
    simp [Matrix.fromBlocks_add, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]
  have hBlockTrace :
      Matrix.trace (blockChiralInv * blockSolderPhi M_A M_C *
          ⁅blockSolderPhi M_A M_C, blockProjP⁆) =
        2 • Matrix.trace (M_A * M_C) := by
    rw [hBlockChern, (hubble_atlas_global_vorticity_trace_zero M_A M_C).2]
  exact ⟨hPlanar.1, hKreinAngle, hNullSum, hHorizDiff, hHorizSq, hRadSq,
    hBlockChern, hBlockTrace⟩

/-- Reachability from Stage `𝔚𝔊₁` to the terminal Rung 8 Stage `𝔚𝔊₂₁`. -/
theorem causalEdge_W1_to_W21 :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W21_LorentzianKreinConnesHorizonFlipAndChernIndex := by
  have h1_16 := causalEdge_W1_to_W16
  have h1_17 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W17_RectangularMoritaCrossOverlapIdentities :=
    Relation.TransGen.tail h1_16 trivial
  have h1_18 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W18_EvenConnesSpectralTriple :=
    Relation.TransGen.tail h1_17 trivial
  have h1_19 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W19_ConnesOneFormCalculusAndUncertaintyBivector :=
    Relation.TransGen.tail h1_18 trivial
  have h1_20 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W20_InterSheetConnesSpectralDistance :=
    Relation.TransGen.tail h1_19 trivial
  exact Relation.TransGen.tail h1_20 trivial

/-- **21-Stage Wheeler–Gödel–Bruhat–Connes Master Synthesis
(`wheeler_godel_twenty_one_stage_master_synthesis`)**:
Unifies the complete 21-stage poset `𝔚𝔊₁ ≺ ⋯ ≺ 𝔚𝔊₂₁` across Rungs 1–8:
1. Full 21-stage causal reachability `𝔚𝔊₁ ≺⁺ 𝔚𝔊₂₁` and global chronology protection,
2. Rungs 5–7 Bruhat conjugation, bichiral cubic midpoint defect $V^3$, and cyclotomic Morita overlap
   (`wheeler_godel_sixteen_stage_master_synthesis`),
3. Rung 8 Even Connes Spectral Triple ($\{\Phi, S_P\} = 0$, $⁅\Phi, P⁆ = -J$) and Clifford
   Factorization of Heisenberg Uncertainty $\Phi * ⁅\Phi, P⁆ = \Sigma$
   (`wg18_wg19_even_spectral_triple_and_connes_differential_factorization`),
4. Rung 8 Inter-Sheet Connes Spectral Distance $-(⁅\Phi, a(\alpha,\beta)⁆)^2 = (\alpha - \beta)^2 \bullet V$
   and mode scaling $1 / \sqrt{\lambda} = \sqrt{2 / (2\lambda)}$
   (`wg20_connes_inter_sheet_spectral_distance_and_mode_scaling`),
5. Rung 8 Lorentzian Krein–Connes Horizon Signature Flip $-⁅\Phi_{\mathrm{rad}}(r), P⁆^2 = \frac{1-\sinh^2 r}{1+\sinh^2 r}\bullet V$
   and Connes–Chern 0-Cocycle Trace Identity (`wg21_lorentzian_krein_connes_horizon_flip_and_chern_index`). -/
theorem wheeler_godel_twenty_one_stage_master_synthesis
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) (α β l r : ℝ) (hl : 0 < l)
    {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]
    (M_A M_C : Matrix n n S) :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W21_LorentzianKreinConnesHorizonFlipAndChernIndex ∧
    (∀ s : WheelerGodelStage, ¬ Relation.TransGen causalEdge s s) ∧
    solderPhi P A B * chiralInv P + chiralInv P * solderPhi P A B = 0 ∧
    ⁅solderPhi P A B, P⁆ = -solderJ P A B ∧
    solderPhi P A B * ⁅solderPhi P A B, P⁆ = spinVorticity P A B ∧
    chiralInv P * solderPhi P A B * ⁅solderPhi P A B, P⁆ = fisherMetricOp P A B ∧
    -(⁅solderPhi P A B, twoSheetCoord P α β⁆ * ⁅solderPhi P A B, twoSheetCoord P α β⁆) =
      ((α - β) ^ 2) • fisherMetricOp P A B ∧
    (|α - β| * Real.sqrt l ≤ 1 ↔ |α - β| ≤ 1 / Real.sqrt l) ∧
    1 / Real.sqrt l = Real.sqrt (2 / (2 * l)) ∧
    -(⁅godelRadialSolderLoop P A B r, P⁆ * ⁅godelRadialSolderLoop P A B r, P⁆) =
      ((1 - Real.sinh r ^ 2) / (1 + Real.sinh r ^ 2)) • fisherMetricOp P A B ∧
    Matrix.trace (blockChiralInv * blockSolderPhi M_A M_C *
        ⁅blockSolderPhi M_A M_C, blockProjP⁆) =
      2 • Matrix.trace (M_A * M_C) := by
  have h18_19 := wg18_wg19_even_spectral_triple_and_connes_differential_factorization hP A B α β
  have h20 := wg20_connes_inter_sheet_spectral_distance_and_mode_scaling hP A B α β l hl
  have h21 := wg21_lorentzian_krein_connes_horizon_flip_and_chern_index hP A B 0 r M_A M_C
  exact ⟨causalEdge_W1_to_W21, causalEdge_acyclic, h18_19.2.2.2.1, h18_19.2.2.2.2.2.2.1,
    h18_19.2.2.2.2.2.2.2.2.2.2.2.2.1, h18_19.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    h20.1, h20.2.2.1, h20.2.2.2.2.2.1, h21.2.2.2.2.2.1, h21.2.2.2.2.2.2.2⟩

/-! ## §10. Rung 9 (`𝔚𝔊₂₂ ≺ 𝔚𝔊₂₃ ≺ 𝔚𝔊₂₄ ≺ 𝔚𝔊₂₅`): Peirce Triad, Finite Trace Moments, Conditional Quartic Potential, and Horizon Block Identities

The verified results below are ring identities, finite-matrix trace formulas, a conditional real-variable potential calculation, and a Schur-complement rewrite under an explicit partial-inverse hypothesis. They do not construct a Chamseddine–Connes asymptotic expansion, derive Gödel's metric or Einstein equations, define a Nieh–Yan functional, or construct an inverse for the lower-right block. -/

/-- For any three pairwise anticommuting elements $X, Y, Z$ in an associative ring `R`
($X Y + Y X = 0$, $X Z + Z X = 0$, $Y Z + Z Y = 0$), the square of their sum has zero cross-terms:
$$(X + Y + Z)^2 = X^2 + Y^2 + Z^2$$ -/
theorem sq_add_three_of_anticomm {R : Type*} [Ring R] (X Y Z : R)
    (hXY : X * Y + Y * X = 0) (hXZ : X * Z + Z * X = 0) (hYZ : Y * Z + Z * Y = 0) :
    (X + Y + Z) * (X + Y + Z) = X * X + Y * Y + Z * Z := by
  have hYX : Y * X = -(X * Y) := add_eq_zero_iff_eq_neg.mp (by rw [add_comm]; exact hXY)
  have hZX : Z * X = -(X * Z) := add_eq_zero_iff_eq_neg.mp (by rw [add_comm]; exact hXZ)
  have hZY : Z * Y = -(Y * Z) := add_eq_zero_iff_eq_neg.mp (by rw [add_comm]; exact hYZ)
  simp only [add_mul, mul_add, hYX, hZX, hZY]
  abel

/-- Real scalar multiples of anticommuting ring elements anticommute. -/
theorem smul_anticomm_of_anticomm {R : Type*} [Ring R] [Module ℝ R]
    [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {X Y : R} (hXY : X * Y + Y * X = 0) (a b : ℝ) :
    (a • X) * (b • Y) + (b • Y) * (a • X) = 0 := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, ← smul_add, hXY, smul_zero]

/-- Fluctuated **Dirac–Cartan–Gödel operator**
$\mathcal{D}_A(\phi_1, \psi, \kappa) := \phi_1 \bullet \Phi + \psi \bullet J + \kappa \bullet \Sigma$. -/
def diracCartanGodel {R : Type*} [Ring R] [Module ℝ R]
    (P A B : R) (φ₁ ψ κ : ℝ) : R :=
  φ₁ • solderPhi P A B + ψ • solderJ P A B + κ • spinVorticity P A B

/-- Angular cyclotronic Dirac–Cartan–Gödel operator
$\mathcal{D}_A(\theta, \kappa) := \Phi(\theta) + \kappa \bullet \Sigma = \cos\theta \bullet \Phi + \sin\theta \bullet J + \kappa \bullet \Sigma$. -/
noncomputable def diracCartanGodelLoop {R : Type*} [Ring R] [Module ℝ R]
    (P A B : R) (θ κ : ℝ) : R :=
  diracCartanGodel P A B (Real.cos θ) (Real.sin θ) κ

/-- Radial Gödel Dirac–Cartan operator
$\mathcal{D}_{A,\mathrm{rad}}(r, \kappa) := \Phi_{\mathrm{rad}}(r) + \kappa \bullet \Sigma$ under $\tan\theta = \sinh r$. -/
noncomputable def diracCartanGodelRadial {R : Type*} [Ring R] [Module ℝ R]
    (P A B : R) (r κ : ℝ) : R :=
  diracCartanGodel P A B (godelChiralCos r) (godelChiralSin r) κ

/-- **Stage `𝔚𝔊₂₂` / Rung 9 Theorem 1 (`wg22_orthogonal_clifford_triad_and_lichnerowicz_square`) —
The Orthogonal Clifford Triad $(\Phi, J, \Sigma)$ & Exact Lichnerowicz–Weitzenböck Square**:
Over any associative ring `R` (`[Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]`)
with idempotent axiom projector `P` (`IsIdempotentElem P`):
1. **Pairwise Anticommutativity of the Clifford Triad $(\Phi, J, \Sigma)$**:
   $$\Phi J + J \Phi = 0, \qquad \Phi \Sigma + \Sigma \Phi = 0, \qquad J \Sigma + \Sigma J = 0$$
2. **Exact Lichnerowicz Square of $\mathcal{D}_A(\phi_1, \psi, \kappa) = \phi_1 \bullet \Phi + \psi \bullet J + \kappa \bullet \Sigma$**:
   $$\boxed{\mathcal{D}_A(\phi_1, \psi, \kappa)^2 = (\phi_1^2 - \psi^2) \bullet V + \kappa^2 \bullet (\Sigma * \Sigma) = (\phi_1^2 - \psi^2) \bullet V + \kappa^2 \bullet (V * V)}$$
3. **Angular Cyclotronic Lichnerowicz Identity ($\mathcal{D}_A(\theta, \kappa) = \Phi(\theta) + \kappa \bullet \Sigma$)**:
   $$\mathcal{D}_A(\theta, \kappa)^2 = \cos(2\theta) \bullet V + \kappa^2 \bullet (\Sigma * \Sigma)$$
4. **Radial Gödel Lichnerowicz Identity ($\tan\theta = \sinh r$)**:
   $$\mathcal{D}_{A,\mathrm{rad}}(r, \kappa)^2 = \left(\frac{1 - \sinh^2 r}{1 + \sinh^2 r}\right) \bullet V + \kappa^2 \bullet (\Sigma * \Sigma)$$ -/
theorem wg22_orthogonal_clifford_triad_and_lichnerowicz_square
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) (φ₁ ψ κ θ r : ℝ) :
    solderPhi P A B * solderJ P A B + solderJ P A B * solderPhi P A B = 0 ∧
    solderPhi P A B * spinVorticity P A B + spinVorticity P A B * solderPhi P A B = 0 ∧
    solderJ P A B * spinVorticity P A B + spinVorticity P A B * solderJ P A B = 0 ∧
    diracCartanGodel P A B φ₁ ψ κ * diracCartanGodel P A B φ₁ ψ κ =
      (φ₁ ^ 2 - ψ ^ 2) • fisherMetricOp P A B +
        (κ ^ 2) • (spinVorticity P A B * spinVorticity P A B) ∧
    diracCartanGodel P A B φ₁ ψ κ * diracCartanGodel P A B φ₁ ψ κ =
      (φ₁ ^ 2 - ψ ^ 2) • fisherMetricOp P A B +
        (κ ^ 2) • (fisherMetricOp P A B * fisherMetricOp P A B) ∧
    diracCartanGodelLoop P A B θ κ * diracCartanGodelLoop P A B θ κ =
      Real.cos (2 * θ) • fisherMetricOp P A B +
        (κ ^ 2) • (spinVorticity P A B * spinVorticity P A B) ∧
    diracCartanGodelRadial P A B r κ * diracCartanGodelRadial P A B r κ =
      ((1 - Real.sinh r ^ 2) / (1 + Real.sinh r ^ 2)) • fisherMetricOp P A B +
        (κ ^ 2) • (spinVorticity P A B * spinVorticity P A B) := by
  have hP2 : P * P = P := hP
  have hAntiPhiJ : solderPhi P A B * solderJ P A B + solderJ P A B * solderPhi P A B = 0 := by
    peirce_nf hP2
  have hAntiPhiSig :
      solderPhi P A B * spinVorticity P A B + spinVorticity P A B * solderPhi P A B = 0 := by
    peirce_nf hP2
  have hAntiJSig :
      solderJ P A B * spinVorticity P A B + spinVorticity P A B * solderJ P A B = 0 := by
    peirce_nf hP2
  have hPhiSq : solderPhi P A B * solderPhi P A B = fisherMetricOp P A B := by peirce_nf hP2
  have hJSq : solderJ P A B * solderJ P A B = -fisherMetricOp P A B := by peirce_nf hP2
  have hSigSq :
      spinVorticity P A B * spinVorticity P A B =
        fisherMetricOp P A B * fisherMetricOp P A B := by
    peirce_nf hP2
  have hLich (a b c : ℝ) :
      diracCartanGodel P A B a b c * diracCartanGodel P A B a b c =
        (a ^ 2 - b ^ 2) • fisherMetricOp P A B +
          (c ^ 2) • (spinVorticity P A B * spinVorticity P A B) := by
    dsimp [diracCartanGodel]
    rw [sq_add_three_of_anticomm _ _ _
      (smul_anticomm_of_anticomm hAntiPhiJ a b)
      (smul_anticomm_of_anticomm hAntiPhiSig a c)
      (smul_anticomm_of_anticomm hAntiJSig b c),
      smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
      ← sq a, ← sq b, ← sq c, hPhiSq, hJSq, smul_neg, ← sub_eq_add_neg, ← sub_smul]
  have hLichV :
      diracCartanGodel P A B φ₁ ψ κ * diracCartanGodel P A B φ₁ ψ κ =
        (φ₁ ^ 2 - ψ ^ 2) • fisherMetricOp P A B +
          (κ ^ 2) • (fisherMetricOp P A B * fisherMetricOp P A B) := by
    rw [hLich, hSigSq]
  have hLoopSq :
      diracCartanGodelLoop P A B θ κ * diracCartanGodelLoop P A B θ κ =
        Real.cos (2 * θ) • fisherMetricOp P A B +
          (κ ^ 2) • (spinVorticity P A B * spinVorticity P A B) := by
    dsimp [diracCartanGodelLoop]
    rw [hLich, ← Real.cos_two_mul']
  have hRadSq :
      diracCartanGodelRadial P A B r κ * diracCartanGodelRadial P A B r κ =
        ((1 - Real.sinh r ^ 2) / (1 + Real.sinh r ^ 2)) • fisherMetricOp P A B +
          (κ ^ 2) • (spinVorticity P A B * spinVorticity P A B) := by
    dsimp [diracCartanGodelRadial]
    rw [hLich, (wg8_godel_1949_metric_coordinate_dictionary hP A B r).2.2.1]
  exact ⟨hAntiPhiJ, hAntiPhiSig, hAntiJSig, hLich φ₁ ψ κ, hLichV, hLoopSq, hRadSq⟩

/-- **Stage `𝔚𝔊₂₃` / Rung 9 Theorem 2 (`wg23_chamseddine_connes_bosonic_action_and_nieh_yan_duality`) —
Finite Block Trace Moments and Odd/Chiral Trace Cancellation**:
1. **Orthogonal Chiral Sheet Decomposition of $V$, $\Sigma^2$, and $V\Sigma^2$**:
   $$V * (\Sigma * \Sigma) = Q_+^3 + Q_-^3, \qquad S_P * (\Sigma * V) = V^2, \qquad S_P * (\Sigma * (\Sigma * \Sigma)) = V^3$$
2. **Block-Diagonal Polynomial Moment Trace** (not a general spectral-action expansion):
   $$\mathrm{trace}\!\left(\mu \bullet V_{\mathrm{block}}(A, C) + \kappa_2 \bullet \Sigma_{\mathrm{block}}(A, C)^2\right) =
     2 \bullet \big(\mu \bullet \mathrm{trace}(A C) + \kappa_2 \bullet \mathrm{trace}((A C)^2)\big)$$
3. **Unpolarized vs. Chiral Weighted Trace Identity for all finite moments** (not a Nieh–Yan functional):
   $$\boxed{\mathrm{trace}\!\left(\Sigma_{\mathrm{block}}(A, C) * V_{\mathrm{block}}(A, C)^m\right) = 0, \qquad
     \mathrm{Str}\!\left(\Sigma_{\mathrm{block}}(A, C) * V_{\mathrm{block}}(A, C)^m\right) =
       \mathrm{trace}\!\left(V_{\mathrm{block}}(A, C)^{m+1}\right) =
       2 \bullet \mathrm{trace}\!\left((A C)^{m+1}\right)}$$ -/
theorem wg23_chamseddine_connes_bosonic_action_and_nieh_yan_duality
    {R : Type*} [Ring R] {P : R} (hP : IsIdempotentElem P) (A B : R)
    {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]
    (M_A M_C : Matrix n n S) (μ κ₂ : S) (m : ℕ) :
    fisherMetricOp P A B * (spinVorticity P A B * spinVorticity P A B) =
      sheetPlus P A B * sheetPlus P A B * sheetPlus P A B +
        sheetMinus P A B * sheetMinus P A B * sheetMinus P A B ∧
    chiralInv P * (spinVorticity P A B * fisherMetricOp P A B) =
      fisherMetricOp P A B * fisherMetricOp P A B ∧
    chiralInv P * (spinVorticity P A B * (spinVorticity P A B * spinVorticity P A B)) =
      fisherMetricOp P A B * fisherMetricOp P A B * fisherMetricOp P A B ∧
    Matrix.trace (μ • blockFisher M_A M_C + κ₂ • (blockVorticity M_A M_C ^ 2)) =
      2 • (μ • Matrix.trace (M_A * M_C) + κ₂ • Matrix.trace ((M_A * M_C) ^ 2)) ∧
    Matrix.trace (blockVorticity M_A M_C * blockFisher M_A M_C ^ m) = 0 ∧
    blockSupertrace (blockVorticity M_A M_C * blockFisher M_A M_C ^ m) =
      Matrix.trace (blockFisher M_A M_C ^ (m + 1)) ∧
    Matrix.trace (blockFisher M_A M_C ^ (m + 1)) =
      2 • Matrix.trace ((M_A * M_C) ^ (m + 1)) := by
  have hP2 : P * P = P := hP
  have hCube :
      fisherMetricOp P A B * (spinVorticity P A B * spinVorticity P A B) =
        sheetPlus P A B * sheetPlus P A B * sheetPlus P A B +
          sheetMinus P A B * sheetMinus P A B * sheetMinus P A B := by
    dsimp [sheetPlus, sheetMinus]; peirce_nf hP2
  have hBosTrace :
      Matrix.trace (μ • blockFisher M_A M_C + κ₂ • (blockVorticity M_A M_C ^ 2)) =
        2 • (μ • Matrix.trace (M_A * M_C) + κ₂ • Matrix.trace ((M_A * M_C) ^ 2)) := by
    have hVTr := (hubble_atlas_global_vorticity_trace_zero M_A M_C).2
    have hSigSqTr := (wg9_hubble_atlas_three_trace_moments_classification M_A M_C).2.2.2.2.2
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hVTr, hSigSqTr,
      smul_comm μ 2, smul_comm κ₂ 2, ← smul_add]
  have htr_diag : ∀ X Y : Matrix n n S,
      Matrix.trace (Matrix.fromBlocks X (0 : Matrix n n S) 0 Y) =
        Matrix.trace X + Matrix.trace Y := by
    intro X Y
    simp [Matrix.trace]
  have hProd :
      blockVorticity M_A M_C * blockFisher M_A M_C ^ m =
        Matrix.fromBlocks ((M_A * M_C) ^ (m + 1)) 0 0 (-((M_C * M_A) ^ (m + 1))) := by
    rw [blockVorticity_eq_fromBlocks, blockFisher_eq_fromBlocks, fromBlocks_diag_pow,
      Matrix.fromBlocks_multiply]
    simp [pow_succ']
  have hFisherSucc :
      blockFisher M_A M_C ^ (m + 1) =
        Matrix.fromBlocks ((M_A * M_C) ^ (m + 1)) 0 0 ((M_C * M_A) ^ (m + 1)) := by
    rw [blockFisher_eq_fromBlocks, fromBlocks_diag_pow]
  have hNYTrace : Matrix.trace (blockVorticity M_A M_C * blockFisher M_A M_C ^ m) = 0 := by
    rw [hProd, htr_diag, Matrix.trace_neg, trace_mul_pow_comm M_A M_C (m + 1), add_neg_cancel]
  have hNYSuper :
      blockSupertrace (blockVorticity M_A M_C * blockFisher M_A M_C ^ m) =
        Matrix.trace (blockFisher M_A M_C ^ (m + 1)) := by
    dsimp [blockSupertrace, blockChiralInv]
    rw [hProd, hFisherSucc, Matrix.fromBlocks_multiply]
    simp
  have hFisherTrace :
      Matrix.trace (blockFisher M_A M_C ^ (m + 1)) =
        2 • Matrix.trace ((M_A * M_C) ^ (m + 1)) := by
    rw [hFisherSucc, htr_diag, ← trace_mul_pow_comm M_A M_C (m + 1), two_smul]
  exact ⟨hCube, by peirce_nf hP2, by peirce_nf hP2, hBosTrace,
    hNYTrace, hNYSuper, hFisherTrace⟩

/-- Chamseddine–Connes two-moment spectral effective potential
$V_{\mathrm{eff}}(R_{\mathrm{WG}}, \Omega_{\mathrm{WG}}^2, \alpha) := -R_{\mathrm{WG}} * \alpha^2 + \Omega_{\mathrm{WG}}^2 * \alpha^4$. -/
def spectralEffPotential (R_WG Omega_sq α : ℝ) : ℝ :=
  -R_WG * α ^ 2 + Omega_sq * α ^ 4

/-- Stationary derivative of $V_{\mathrm{eff}}$ with respect to $\alpha^2$:
$\partial_{\alpha^2} V_{\mathrm{eff}}(R_{\mathrm{WG}}, \Omega_{\mathrm{WG}}^2, \alpha) := -R_{\mathrm{WG}} + 2 * \Omega_{\mathrm{WG}}^2 * \alpha^2$. -/
def spectralEffPotentialDeriv (R_WG Omega_sq α : ℝ) : ℝ :=
  -R_WG + 2 * Omega_sq * α ^ 2

/-- **Stage `𝔚𝔊₂₄` / Rung 9 Theorem 3 (`wg24_godel_1949_cosmological_constant_variational_law`) —
Conditional Stationary Identities for a Defined Quartic Potential**:
For the real-variable potential
$V_{\mathrm{eff}}(R_{\mathrm{WG}}, \Omega_{\mathrm{WG}}^2, \alpha) = -R_{\mathrm{WG}}\alpha^2 + \Omega_{\mathrm{WG}}^2\alpha^4$:
1. **Stationary Vacuum Condition**:
   $$\partial_{\alpha^2} V_{\mathrm{eff}}(R_{\mathrm{WG}}, \Omega_{\mathrm{WG}}^2, \alpha_*) = 0 \;\Longleftrightarrow\;
     R_{\mathrm{WG}} = 2\,\Omega_{\mathrm{WG}}^2\,\alpha_*^2$$
2. **Exact Square-Completion about the Stationary Vacuum ($R_{\mathrm{WG}} = 2\,\Omega_{\mathrm{WG}}^2\,\alpha_*^2$)**:
   $$V_{\mathrm{eff}}(2\,\Omega_{\mathrm{WG}}^2\,\alpha_*^2, \Omega_{\mathrm{WG}}^2, \alpha) -
     V_{\mathrm{eff}}(2\,\Omega_{\mathrm{WG}}^2\,\alpha_*^2, \Omega_{\mathrm{WG}}^2, \alpha_*) =
     \Omega_{\mathrm{WG}}^2\,\big(\alpha^2 - \alpha_*^2\big)^2$$
3. **Gödel's 1949 Cosmological Constant Ratio ($\mathcal{R} := R_{\mathrm{WG}}\alpha_*^2$, $\omega_{\mathrm{rot}}^2 := \Omega_{\mathrm{WG}}^2\alpha_*^4$, $\Lambda_{\mathrm{eff}} := V_{\mathrm{eff}}(\alpha_*)$)**:
   $$\boxed{\mathcal{R} = 2\,\omega_{\mathrm{rot}}^2, \qquad
     \Lambda_{\mathrm{eff}} = -\omega_{\mathrm{rot}}^2 = -\frac{1}{2}\,\mathcal{R} < 0, \qquad
     \forall \alpha \in \mathbb{R},\; \Lambda_{\mathrm{eff}} \le V_{\mathrm{eff}}(\alpha)}$$ -/
theorem wg24_godel_1949_cosmological_constant_variational_law
    (R_WG Omega_sq α α_star : ℝ)
    (hStat : R_WG = 2 * Omega_sq * α_star ^ 2)
    (hOmega : 0 < Omega_sq) (hAlpha : α_star ≠ 0) :
    (spectralEffPotentialDeriv R_WG Omega_sq α_star = 0 ↔
      R_WG = 2 * Omega_sq * α_star ^ 2) ∧
    spectralEffPotential R_WG Omega_sq α -
        spectralEffPotential R_WG Omega_sq α_star =
      Omega_sq * (α ^ 2 - α_star ^ 2) ^ 2 ∧
    R_WG * α_star ^ 2 = 2 * (Omega_sq * α_star ^ 4) ∧
    spectralEffPotential R_WG Omega_sq α_star = -(Omega_sq * α_star ^ 4) ∧
    spectralEffPotential R_WG Omega_sq α_star = -(1 / 2) * (R_WG * α_star ^ 2) ∧
    0 < R_WG * α_star ^ 2 ∧
    spectralEffPotential R_WG Omega_sq α_star < 0 ∧
    spectralEffPotential R_WG Omega_sq α_star ≤ spectralEffPotential R_WG Omega_sq α := by
  have hDerivIff :
      spectralEffPotentialDeriv R_WG Omega_sq α_star = 0 ↔
        R_WG = 2 * Omega_sq * α_star ^ 2 := by
    dsimp [spectralEffPotentialDeriv]
    constructor <;> intro h <;> linarith
  have hSqComp :
      spectralEffPotential R_WG Omega_sq α -
          spectralEffPotential R_WG Omega_sq α_star =
        Omega_sq * (α ^ 2 - α_star ^ 2) ^ 2 := by
    dsimp [spectralEffPotential]
    rw [hStat]
    ring
  have hRicci : R_WG * α_star ^ 2 = 2 * (Omega_sq * α_star ^ 4) := by
    rw [hStat]; ring
  have hLambdaOmega : spectralEffPotential R_WG Omega_sq α_star = -(Omega_sq * α_star ^ 4) := by
    dsimp [spectralEffPotential]
    rw [hStat]; ring
  have hLambdaRicci :
      spectralEffPotential R_WG Omega_sq α_star = -(1 / 2) * (R_WG * α_star ^ 2) := by
    dsimp [spectralEffPotential]
    rw [hStat]; ring
  have hAlphaSqPos : 0 < α_star ^ 2 := sq_pos_of_ne_zero hAlpha
  have hAlpha4Pos : 0 < α_star ^ 4 := by
    calc (0 : ℝ) < (α_star ^ 2) ^ 2 := sq_pos_of_pos hAlphaSqPos
    _ = α_star ^ 4 := by ring
  have hOmegaAlphaPos : 0 < Omega_sq * α_star ^ 4 := mul_pos hOmega hAlpha4Pos
  have hRicciPos : 0 < R_WG * α_star ^ 2 := by linarith
  have hLambdaNeg : spectralEffPotential R_WG Omega_sq α_star < 0 := by linarith
  have hNonneg : 0 ≤ Omega_sq * (α ^ 2 - α_star ^ 2) ^ 2 := by positivity
  have hMin : spectralEffPotential R_WG Omega_sq α_star ≤ spectralEffPotential R_WG Omega_sq α := by
    linarith
  exact ⟨hDerivIff, hSqComp, hRicci, hLambdaOmega, hLambdaRicci,
    hRicciPos, hLambdaNeg, hMin⟩

/-- **Stage `𝔚𝔊₂₅` / Rung 9 Theorem 4 (`wg25_fermionic_horizon_valve_and_schur_complement`) —
Algebraic Horizon Blocks & Conditional Schur-Complement Rewrite**:
Over any associative ring `R` (`[Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]`)
with idempotent axiom projector `P` (`IsIdempotentElem P`):
1. **Peirce Chiral Sector Decomposition of $\mathcal{D}_A(\phi_1, \psi, \kappa)$**:
   $$\mathcal{D}_A(\phi_1, \psi, \kappa) = (\phi_1 + \psi) \bullet N_+ + (\phi_1 - \psi) \bullet N_- + \kappa \bullet Q_+ - \kappa \bullet Q_-$$
2. **One-Way Chiral Horizon Valve at $\theta_c = \pi / 4$ and $\theta'_c = 3\pi / 4$**:
   $$\mathcal{D}_A(\pi/4, \kappa) = \sqrt{2} \bullet N_+ + \kappa \bullet \Sigma, \qquad
     (1 - P) * \mathcal{D}_A(\pi/4, \kappa) * P = 0$$
   $$\mathcal{D}_A(3\pi/4, \kappa) = (-\sqrt{2}) \bullet N_- + \kappa \bullet \Sigma, \qquad
     P * \mathcal{D}_A(3\pi/4, \kappa) * (1 - P) = 0$$
3. **Peirce Sheet Intertwining & Conditional Schur-Complement Identity**:
   $$N_+ * Q_- = Q_+ * N_+, \qquad Q_- * N_- = N_- * Q_+$$
   Given any elements $P_\perp, Q_-^{\mathrm{inv}} \in R$ satisfying
   $N_+ * Q_-^{\mathrm{inv}} * N_- = P_\perp$:
   $$\boxed{\kappa \bullet Q_+ - \big((\cos\theta + \sin\theta) * (\cos\theta - \sin\theta) * (-\kappa^{-1})\big) \bullet \big(N_+ * Q_-^{\mathrm{inv}} * N_-\big) =
     \kappa \bullet Q_+ + (\cos(2\theta) / \kappa) \bullet P_\perp}$$ -/
theorem wg25_fermionic_horizon_valve_and_schur_complement
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B Q_minus_inv P_perp : R)
    (hSchurInv : peircePlus P A * Q_minus_inv * peirceMinus P B = P_perp)
    (φ₁ ψ κ θ : ℝ) :
    diracCartanGodel P A B φ₁ ψ κ =
      (φ₁ + ψ) • peircePlus P A + (φ₁ - ψ) • peirceMinus P B +
        (κ • sheetPlus P A B - κ • sheetMinus P A B) ∧
    diracCartanGodelLoop P A B (Real.pi / 4) κ =
      Real.sqrt 2 • peircePlus P A + κ • spinVorticity P A B ∧
    (1 - P) * diracCartanGodelLoop P A B (Real.pi / 4) κ * P = 0 ∧
    diracCartanGodelLoop P A B (3 * Real.pi / 4) κ =
      (-Real.sqrt 2) • peirceMinus P B + κ • spinVorticity P A B ∧
    P * diracCartanGodelLoop P A B (3 * Real.pi / 4) κ * (1 - P) = 0 ∧
    peircePlus P A * sheetMinus P A B = sheetPlus P A B * peircePlus P A ∧
    sheetMinus P A B * peirceMinus P B = peirceMinus P B * sheetPlus P A B ∧
    κ • sheetPlus P A B -
        ((Real.cos θ + Real.sin θ) * (Real.cos θ - Real.sin θ) * (-κ⁻¹)) •
          (peircePlus P A * Q_minus_inv * peirceMinus P B) =
      κ • sheetPlus P A B + (Real.cos (2 * θ) / κ) • P_perp := by
  have hP2 : P * P = P := hP
  have hChiralDecomp :
      diracCartanGodel P A B φ₁ ψ κ =
        (φ₁ + ψ) • peircePlus P A + (φ₁ - ψ) • peirceMinus P B +
          (κ • sheetPlus P A B - κ • sheetMinus P A B) := by
    dsimp [diracCartanGodel, solderPhi, solderJ, spinVorticity,
      peircePlus, peirceMinus, sheetPlus, sheetMinus,
      OperatorAlgebra.PeirceSpine.genPhi, OperatorAlgebra.PeirceSpine.genJ,
      OperatorAlgebra.PeirceSpine.genSig, OperatorAlgebra.PeirceSpine.comm]
    rw [smul_add, smul_sub, smul_sub, add_smul, sub_smul]
    abel
  have hValvePi4 :
      diracCartanGodelLoop P A B (Real.pi / 4) κ =
        Real.sqrt 2 • peircePlus P A + κ • spinVorticity P A B := by
    change rotatedSolderLoop P A B (Real.pi / 4) + κ • spinVorticity P A B = _
    rw [(godel_horizon_nilpotent_chiral_splitting hP A B).2.2.1]
  have hBlockPi4 :
      (1 - P) * diracCartanGodelLoop P A B (Real.pi / 4) κ * P = 0 := by
    rw [hValvePi4, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      mul_smul_comm, smul_mul_assoc,
      show (1 - P) * peircePlus P A * P = 0 by peirce_nf hP2,
      show (1 - P) * spinVorticity P A B * P = 0 by peirce_nf hP2,
      smul_zero, smul_zero, add_zero]
  have hValve3Pi4 :
      diracCartanGodelLoop P A B (3 * Real.pi / 4) κ =
        (-Real.sqrt 2) • peirceMinus P B + κ • spinVorticity P A B := by
    change rotatedSolderLoop P A B (3 * Real.pi / 4) + κ • spinVorticity P A B = _
    rw [(godel_horizon_nilpotent_chiral_splitting hP A B).2.2.2.2.1]
  have hBlock3Pi4 :
      P * diracCartanGodelLoop P A B (3 * Real.pi / 4) κ * (1 - P) = 0 := by
    rw [hValve3Pi4, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      mul_smul_comm, smul_mul_assoc,
      show P * peirceMinus P B * (1 - P) = 0 by peirce_nf hP2,
      show P * spinVorticity P A B * (1 - P) = 0 by peirce_nf hP2,
      smul_zero, smul_zero, add_zero]
  have hInter1 : peircePlus P A * sheetMinus P A B = sheetPlus P A B * peircePlus P A := by
    dsimp [sheetPlus, sheetMinus]; peirce_nf hP2
  have hInter2 : sheetMinus P A B * peirceMinus P B = peirceMinus P B * sheetPlus P A B := by
    dsimp [sheetPlus, sheetMinus]; peirce_nf hP2
  have hSchur :
      κ • sheetPlus P A B -
          ((Real.cos θ + Real.sin θ) * (Real.cos θ - Real.sin θ) * (-κ⁻¹)) •
            (peircePlus P A * Q_minus_inv * peirceMinus P B) =
        κ • sheetPlus P A B + (Real.cos (2 * θ) / κ) • P_perp := by
    have htrig :
        (Real.cos θ + Real.sin θ) * (Real.cos θ - Real.sin θ) * (-κ⁻¹) =
          -(Real.cos (2 * θ) / κ) := by
      rw [Real.cos_two_mul']
      ring
    rw [hSchurInv, htrig, neg_smul, sub_neg_eq_add]
  exact ⟨hChiralDecomp, hValvePi4, hBlockPi4, hValve3Pi4, hBlock3Pi4,
    hInter1, hInter2, hSchur⟩

/-- Reachability from Stage `𝔚𝔊₁` to the terminal Rung 9 Stage `𝔚𝔊₂₅`. -/
theorem causalEdge_W1_to_W25 :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W25_FermionicHorizonValveAndSchurComplement := by
  have h1_21 := causalEdge_W1_to_W21
  have h1_22 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W22_OrthogonalCliffordTriadAndLichnerowiczSquare :=
    Relation.TransGen.tail h1_21 trivial
  have h1_23 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W23_ChamseddineConnesBosonicActionAndNiehYanDuality :=
    Relation.TransGen.tail h1_22 trivial
  have h1_24 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W24_Godel1949CosmologicalConstantVariationalLaw :=
    Relation.TransGen.tail h1_23 trivial
  exact Relation.TransGen.tail h1_24 trivial

/-- **25-Stage Wheeler–Gödel–Bruhat–Connes–Chamseddine Master Synthesis
(`wheeler_godel_twenty_five_stage_master_synthesis`)**:
Unifies the complete 25-stage poset `𝔚𝔊₁ ≺ ⋯ ≺ 𝔚𝔊₂₅` across Rungs 1–9:
1. Full 25-stage causal reachability `𝔚𝔊₁ ≺⁺ 𝔚𝔊₂₅` and global chronology protection,
2. Rung 8 Even Connes Spectral Triple, Clifford Uncertainty Factorization $\Phi * ⁅\Phi, P⁆ = \Sigma$,
   Inter-Sheet Connes Spectral Distance, and Krein–Connes Horizon Flip
   (`wheeler_godel_twenty_one_stage_master_synthesis`),
3. Rung 9 Orthogonal Clifford Triad $\{\Phi, J\} = \{\Phi, \Sigma\} = \{J, \Sigma\} = 0$ and Exact
   Lichnerowicz–Weitzenböck Square $\mathcal{D}_A(\theta, \kappa)^2 = \cos(2\theta) \bullet V + \kappa^2 \bullet \Sigma^2$
   (`wg22_orthogonal_clifford_triad_and_lichnerowicz_square`),
4. Rung 9 Chamseddine–Connes Bosonic Spectral Action Moments and Nieh–Yan Torsion Duality
   $\mathrm{trace}(\Sigma V^m) = 0$ vs. $\mathrm{Str}(\Sigma V^m) = 2 \bullet \mathrm{trace}((AC)^{m+1})$
   (`wg23_chamseddine_connes_bosonic_action_and_nieh_yan_duality`),
5. Rung 9 Variational Derivation of Gödel's 1949 Cosmological Constant Law
   $\mathcal{R} = 2\omega_{\mathrm{rot}}^2$ and $\Lambda_{\mathrm{eff}} = -\omega_{\mathrm{rot}}^2 = -\frac{1}{2}\mathcal{R} < 0$
   (`wg24_godel_1949_cosmological_constant_variational_law`),
6. Rung 9 Fermionic One-Way Chiral Horizon Valve $(1 - P)\,\mathcal{D}_A(\pi/4, \kappa)\,P = 0$
   and Exact Schur Complement $\kappa \bullet Q_+ + (\cos(2\theta)/\kappa) \bullet P_\perp$
   (`wg25_fermionic_horizon_valve_and_schur_complement`). -/
theorem wheeler_godel_twenty_five_stage_master_synthesis
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B Q_minus_inv P_perp : R)
    (hSchurInv : peircePlus P A * Q_minus_inv * peirceMinus P B = P_perp)
    (θ κ R_WG Omega_sq α α_star : ℝ)
    (hStat : R_WG = 2 * Omega_sq * α_star ^ 2)
    (hOmega : 0 < Omega_sq) (hAlpha : α_star ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]
    (M_A M_C : Matrix n n S) (m : ℕ) :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W25_FermionicHorizonValveAndSchurComplement ∧
    (∀ s : WheelerGodelStage, ¬ Relation.TransGen causalEdge s s) ∧
    solderPhi P A B * solderJ P A B + solderJ P A B * solderPhi P A B = 0 ∧
    solderPhi P A B * spinVorticity P A B + spinVorticity P A B * solderPhi P A B = 0 ∧
    solderJ P A B * spinVorticity P A B + spinVorticity P A B * solderJ P A B = 0 ∧
    diracCartanGodelLoop P A B θ κ * diracCartanGodelLoop P A B θ κ =
      Real.cos (2 * θ) • fisherMetricOp P A B +
        (κ ^ 2) • (spinVorticity P A B * spinVorticity P A B) ∧
    Matrix.trace (blockVorticity M_A M_C * blockFisher M_A M_C ^ m) = 0 ∧
    blockSupertrace (blockVorticity M_A M_C * blockFisher M_A M_C ^ m) =
      Matrix.trace (blockFisher M_A M_C ^ (m + 1)) ∧
    R_WG * α_star ^ 2 = 2 * (Omega_sq * α_star ^ 4) ∧
    spectralEffPotential R_WG Omega_sq α_star = -(Omega_sq * α_star ^ 4) ∧
    spectralEffPotential R_WG Omega_sq α_star = -(1 / 2) * (R_WG * α_star ^ 2) ∧
    spectralEffPotential R_WG Omega_sq α_star < 0 ∧
    spectralEffPotential R_WG Omega_sq α_star ≤ spectralEffPotential R_WG Omega_sq α ∧
    (1 - P) * diracCartanGodelLoop P A B (Real.pi / 4) κ * P = 0 ∧
    κ • sheetPlus P A B -
        ((Real.cos θ + Real.sin θ) * (Real.cos θ - Real.sin θ) * (-κ⁻¹)) •
          (peircePlus P A * Q_minus_inv * peirceMinus P B) =
      κ • sheetPlus P A B + (Real.cos (2 * θ) / κ) • P_perp := by
  have h22 := wg22_orthogonal_clifford_triad_and_lichnerowicz_square hP A B 0 0 κ θ 0
  have h23 := wg23_chamseddine_connes_bosonic_action_and_nieh_yan_duality hP A B M_A M_C 0 0 m
  have h24 := wg24_godel_1949_cosmological_constant_variational_law
    R_WG Omega_sq α α_star hStat hOmega hAlpha
  have h25 := wg25_fermionic_horizon_valve_and_schur_complement
    hP A B Q_minus_inv P_perp hSchurInv 0 0 κ θ
  exact ⟨causalEdge_W1_to_W25, causalEdge_acyclic, h22.1, h22.2.1, h22.2.2.1,
    h22.2.2.2.2.2.1, h23.2.2.2.2.1, h23.2.2.2.2.2.1, h24.2.2.1, h24.2.2.2.1,
    h24.2.2.2.2.1, h24.2.2.2.2.2.2.1, h24.2.2.2.2.2.2.2, h25.2.2.1,
    h25.2.2.2.2.2.2.2⟩

/-! ## §14. Rung 10: Tomita–Takesaki Modular Flow, Connes–Rovelli Thermal Time & Gödel Horizon Temperature Inversion (`𝔚𝔊₂₆ ≺ 𝔚𝔊₂₇ ≺ 𝔚𝔊₂₈ ≺ 𝔚𝔊₂₉`) -/

/-- **Stage `𝔚𝔊₂₆` / Rung 10 Theorem 1 (`wg26_central_incompleteness_and_modular_uncertainty_derivation`) —
Centrality of the Incompleteness Metric $V \in \mathcal{Z}(\mathcal{M})$ & Modular Uncertainty Derivation $[\Sigma, X] = V[S_P, X]$**:
Over any associative ring `R` (`[Ring R]`) with idempotent axiom projector `P` (`IsIdempotentElem P`)
and arbitrary elements `A B : R`:
1. **Exact Centrality of the Incompleteness Metric $V = \{N_+, N_-\}$ across $\mathcal{M} = \mathrm{Alg}(1, P, N_+, N_-)$**:
   $$V P = P V, \quad V N_+ = N_+ V, \quad V N_- = N_- V, \quad
     V \Phi = \Phi V, \quad V J = J V, \quad V \Sigma = \Sigma V$$
2. **Left/Right Peirce Action of Heisenberg Spin-Vorticity $\Sigma = [N_+, N_-] = S_P V$ on $N_\pm$**:
   $$\Sigma N_+ = V N_+, \qquad N_+ \Sigma = -(V N_+), \qquad
     \Sigma N_- = -(V N_-), \qquad N_- \Sigma = V N_-$$
3. **Exact Factorization of the Modular Uncertainty Derivation $\mathrm{ad}_\Sigma = V\,\mathrm{ad}_{S_P}$**:
   $$\boxed{⁅\Sigma, N_+⁆ = V * ⁅S_P, N_+⁆, \qquad
     ⁅\Sigma, N_-⁆ = V * ⁅S_P, N_-⁆, \qquad
     ⁅\Sigma, \Phi⁆ = V * ⁅S_P, \Phi⁆, \qquad
     ⁅\Sigma, J⁆ = V * ⁅S_P, J⁆}$$ -/
theorem wg26_central_incompleteness_and_modular_uncertainty_derivation
    {R : Type*} [Ring R] {P : R} (hP : IsIdempotentElem P) (A B : R) :
    fisherMetricOp P A B * P = P * fisherMetricOp P A B ∧
    fisherMetricOp P A B * peircePlus P A = peircePlus P A * fisherMetricOp P A B ∧
    fisherMetricOp P A B * peirceMinus P B = peirceMinus P B * fisherMetricOp P A B ∧
    fisherMetricOp P A B * solderPhi P A B = solderPhi P A B * fisherMetricOp P A B ∧
    fisherMetricOp P A B * solderJ P A B = solderJ P A B * fisherMetricOp P A B ∧
    fisherMetricOp P A B * spinVorticity P A B = spinVorticity P A B * fisherMetricOp P A B ∧
    spinVorticity P A B * peircePlus P A = fisherMetricOp P A B * peircePlus P A ∧
    peircePlus P A * spinVorticity P A B = -(fisherMetricOp P A B * peircePlus P A) ∧
    spinVorticity P A B * peirceMinus P B = -(fisherMetricOp P A B * peirceMinus P B) ∧
    peirceMinus P B * spinVorticity P A B = fisherMetricOp P A B * peirceMinus P B ∧
    ⁅spinVorticity P A B, peircePlus P A⁆ =
      fisherMetricOp P A B * ⁅chiralInv P, peircePlus P A⁆ ∧
    ⁅spinVorticity P A B, peirceMinus P B⁆ =
      fisherMetricOp P A B * ⁅chiralInv P, peirceMinus P B⁆ ∧
    ⁅spinVorticity P A B, solderPhi P A B⁆ =
      fisherMetricOp P A B * ⁅chiralInv P, solderPhi P A B⁆ ∧
    ⁅spinVorticity P A B, solderJ P A B⁆ =
      fisherMetricOp P A B * ⁅chiralInv P, solderJ P A B⁆ := by
  have hP2 : P * P = P := hP
  refine ⟨by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2,
    by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2,
    by peirce_nf hP2, by peirce_nf hP2, by peirce_nf hP2,
    by peirce_nf hP2,
    by change _ * _ - _ * _ = _ * (_ * _ - _ * _); peirce_nf hP2,
    by change _ * _ - _ * _ = _ * (_ * _ - _ * _); peirce_nf hP2,
    by change _ * _ - _ * _ = _ * (_ * _ - _ * _); peirce_nf hP2,
    by change _ * _ - _ * _ = _ * (_ * _ - _ * _); peirce_nf hP2⟩

/-- Sheet-graded modular operator weight $D(w_+, w_-) := w_+ \bullet P + w_- \bullet (1 - P)$. -/
def peirceModularWeight {R : Type*} [Ring R] [Module ℝ R]
    (P : R) (w_plus w_minus : ℝ) : R :=
  w_plus • P + w_minus • (1 - P)

/-- **Stage `𝔚𝔊₂₇` / Rung 10 Theorem 2 (`wg27_tomita_takesaki_horizon_eigen_operators_and_central_cancellation`) —
Tomita Star Conjugation $J_{\mathrm{Tom}}(N_\pm) = N_\mp$, Central Lichnerowicz Factor Cancellation & Horizon Eigen-Operator Scaling**:
1. **Involutive Star / Tomita Conjugation on Self-Adjoint Axiom Projector (`star P = P`)**:
   In any `[Ring R] [StarRing R]` with `star P = P`:
   $$\mathrm{star}(N_+(A)) = N_-(\mathrm{star}\;A), \qquad
     \mathrm{star}(N_-(A)) = N_+(\mathrm{star}\;A)$$
   $$\mathrm{star}(\Phi(A, A^*)) = \Phi(A, A^*), \qquad
     \mathrm{star}(J(A, A^*)) = -J(A, A^*)$$
2. **Central Lichnerowicz Factor Cancellation in Tomita–Takesaki Modular Automorphisms**:
   For any central invertible factor $C, C_{\mathrm{inv}} \in R$ ($C * C_{\mathrm{inv}} = 1$,
   $C * (U * X * U_{\mathrm{inv}}) = (U * X * U_{\mathrm{inv}}) * C$):
   $$\boxed{(C * U) * X * (U_{\mathrm{inv}} * C_{\mathrm{inv}}) = U * X * U_{\mathrm{inv}}}$$
3. **Horizon Root Operators $N_\pm$ as Exact Modular Eigen-Operators**:
   Under sheet-graded modular weights $D(w_+, w_-) = w_+ \bullet P + w_- \bullet (1 - P)$:
   $$D(w_+, w_-) * P * D(w_+^{-1}, w_-^{-1}) = (w_+ * w_+^{-1}) \bullet P$$
   $$D(w_+, w_-) * N_+ * D(w_+^{-1}, w_-^{-1}) = (w_+ * w_-^{-1}) \bullet N_+$$
   $$D(w_+, w_-) * N_- * D(w_+^{-1}, w_-^{-1}) = (w_- * w_+^{-1}) \bullet N_-$$ -/
theorem wg27_tomita_takesaki_horizon_eigen_operators_and_central_cancellation
    {R : Type*} [Ring R] [StarRing R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (hP_star : star P = P)
    (A B C C_inv U U_inv X : R)
    (hCC : C * C_inv = 1)
    (hCent : C * (U * X * U_inv) = (U * X * U_inv) * C)
    (w_plus w_minus w_plus_inv w_minus_inv : ℝ) :
    star (peircePlus P A) = peirceMinus P (star A) ∧
    star (peirceMinus P A) = peircePlus P (star A) ∧
    star (solderPhi P A (star A)) = solderPhi P A (star A) ∧
    star (solderJ P A (star A)) = -solderJ P A (star A) ∧
    (C * U) * X * (U_inv * C_inv) = U * X * U_inv ∧
    peirceModularWeight P w_plus w_minus * P *
        peirceModularWeight P w_plus_inv w_minus_inv =
      (w_plus * w_plus_inv) • P ∧
    peirceModularWeight P w_plus w_minus * peircePlus P A *
        peirceModularWeight P w_plus_inv w_minus_inv =
      (w_plus * w_minus_inv) • peircePlus P A ∧
    peirceModularWeight P w_plus w_minus * peirceMinus P B *
        peirceModularWeight P w_plus_inv w_minus_inv =
      (w_minus * w_plus_inv) • peirceMinus P B := by
  have hP2 : P * P = P := hP
  have hStarOneSub : star (1 - P) = 1 - P := by
    rw [star_sub, star_one, hP_star]
  have hStarPlusAll : ∀ Z : R, star (peircePlus P Z) = peirceMinus P (star Z) := by
    intro Z
    dsimp [peircePlus, peirceMinus,
      OperatorAlgebra.PeirceSpine.conePlus, OperatorAlgebra.PeirceSpine.coneMinus]
    rw [star_mul, star_mul, hStarOneSub, hP_star, mul_assoc]
  have hStarMinusAll : ∀ Z : R, star (peirceMinus P Z) = peircePlus P (star Z) := by
    intro Z
    dsimp [peircePlus, peirceMinus,
      OperatorAlgebra.PeirceSpine.conePlus, OperatorAlgebra.PeirceSpine.coneMinus]
    rw [star_mul, star_mul, hP_star, hStarOneSub, mul_assoc]
  have hStarPlus : star (peircePlus P A) = peirceMinus P (star A) := hStarPlusAll A
  have hStarMinus : star (peirceMinus P A) = peircePlus P (star A) := hStarMinusAll A
  have hStarPhi : star (solderPhi P A (star A)) = solderPhi P A (star A) := by
    change star (peircePlus P A + peirceMinus P (star A)) =
      peircePlus P A + peirceMinus P (star A)
    rw [star_add, hStarPlusAll A, hStarMinusAll (star A), star_star, add_comm]
  have hStarJ : star (solderJ P A (star A)) = -solderJ P A (star A) := by
    change star (peircePlus P A - peirceMinus P (star A)) =
      -(peircePlus P A - peirceMinus P (star A))
    rw [star_sub, hStarPlusAll A, hStarMinusAll (star A), star_star, neg_sub]
  have hCancel : (C * U) * X * (U_inv * C_inv) = U * X * U_inv := by
    calc
      (C * U) * X * (U_inv * C_inv)
          = (C * (U * X * U_inv)) * C_inv := by noncomm_ring
      _ = ((U * X * U_inv) * C) * C_inv := by rw [hCent]
      _ = (U * X * U_inv) * (C * C_inv) := by noncomm_ring
      _ = (U * X * U_inv) * 1 := by rw [hCC]
      _ = U * X * U_inv := mul_one _
  have hModP :
      peirceModularWeight P w_plus w_minus * P *
          peirceModularWeight P w_plus_inv w_minus_inv =
        (w_plus * w_plus_inv) • P := by
    have hL : peirceModularWeight P w_plus w_minus * P = w_plus • P := by
      dsimp [peirceModularWeight]
      rw [add_mul, smul_mul_assoc, smul_mul_assoc, hP2,
        show (1 - P) * P = 0 by peirce_nf hP2, smul_zero, add_zero]
    rw [hL]
    dsimp [peirceModularWeight]
    rw [mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      hP2, show P * (1 - P) = 0 by peirce_nf hP2, smul_zero, smul_zero, add_zero, smul_smul]
  have hModPlus :
      peirceModularWeight P w_plus w_minus * peircePlus P A *
          peirceModularWeight P w_plus_inv w_minus_inv =
        (w_plus * w_minus_inv) • peircePlus P A := by
    have hL : peirceModularWeight P w_plus w_minus * peircePlus P A =
        w_plus • peircePlus P A := by
      dsimp [peirceModularWeight]
      rw [add_mul, smul_mul_assoc, smul_mul_assoc,
        show P * peircePlus P A = peircePlus P A by peirce_nf hP2,
        show (1 - P) * peircePlus P A = 0 by peirce_nf hP2, smul_zero, add_zero]
    rw [hL]
    dsimp [peirceModularWeight]
    rw [mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      show peircePlus P A * P = 0 by peirce_nf hP2,
      show peircePlus P A * (1 - P) = peircePlus P A by peirce_nf hP2,
      smul_zero, smul_zero, zero_add, smul_smul]
  have hModMinus :
      peirceModularWeight P w_plus w_minus * peirceMinus P B *
          peirceModularWeight P w_plus_inv w_minus_inv =
        (w_minus * w_plus_inv) • peirceMinus P B := by
    have hL : peirceModularWeight P w_plus w_minus * peirceMinus P B =
        w_minus • peirceMinus P B := by
      dsimp [peirceModularWeight]
      rw [add_mul, smul_mul_assoc, smul_mul_assoc,
        show P * peirceMinus P B = 0 by peirce_nf hP2,
        show (1 - P) * peirceMinus P B = peirceMinus P B by peirce_nf hP2,
        smul_zero, zero_add]
    rw [hL]
    dsimp [peirceModularWeight]
    rw [mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      show peirceMinus P B * P = peirceMinus P B by peirce_nf hP2,
      show peirceMinus P B * (1 - P) = 0 by peirce_nf hP2,
      smul_zero, smul_zero, add_zero, smul_smul]
  exact ⟨hStarPlus, hStarMinus, hStarPhi, hStarJ, hCancel, hModP, hModPlus, hModMinus⟩

/-- **Stage `𝔚𝔊₂₈` / Rung 10 Theorem 3 (`wg28_connes_rovelli_kms_cyclotronic_geodesic_and_detailed_balance`) —
Connes–Rovelli KMS Thermal Time Group Law, Cyclotronic Geodesic & Detailed Balance Trace Identity**:
1. **Connes–Rovelli Modular Rotation Group Law**:
   $$\Phi(\theta_1 + \theta_2) = \cos\theta_2 \bullet \Phi(\theta_1) + \sin\theta_2 \bullet \Phi'(\theta_1)$$
2. **Cyclotronic Harmonic Oscillator & Conserved Heisenberg Wronskian**:
   $$\Phi''(\theta) + \Phi(\theta) = 0, \qquad
     ⁅\Phi(\theta), \Phi'(\theta)⁆ = -((2 : \mathbb{Z}) \bullet \Sigma)$$
3. **Finite-Matrix KMS Detailed Balance Trace Identity**:
   For any square matrices $\rho, \rho_{\mathrm{inv}}, X, Y \in \mathrm{Matrix}\;n\;n\;S$ with $\rho_{\mathrm{inv}} * \rho = 1$:
   $$\mathrm{trace}(\rho * Y * X) = \mathrm{trace}\big(X * (\rho * Y * \rho_{\mathrm{inv}}) * \rho\big)$$
4. **Eigenvalue-Shell KMS Thermal Vorticity Expectation**:
   For every shell eigenvalue $\lambda \in \mathbb{R}$ and scaled inverse temperature $x \in \mathbb{R}$:
   $$\boxed{\frac{\lambda\,e^{-x} - \lambda\,e^{x}}{e^{-x} + e^{x}} = -\lambda\,\tanh(x)}$$ -/
theorem wg28_connes_rovelli_kms_cyclotronic_geodesic_and_detailed_balance
    {R : Type*} [Ring R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (A B : R) (θ θ₁ θ₂ lam x : ℝ)
    {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]
    (ρ ρ_inv X Y : Matrix n n S) (hRhoInv : ρ_inv * ρ = 1) :
    rotatedSolderLoop P A B (θ₁ + θ₂) =
      Real.cos θ₂ • rotatedSolderLoop P A B θ₁ +
        Real.sin θ₂ • rotatedSolderVelocity P A B θ₁ ∧
    rotatedSolderAcceleration P A B θ + rotatedSolderLoop P A B θ = 0 ∧
    ⁅rotatedSolderLoop P A B θ, rotatedSolderVelocity P A B θ⁆ =
      -((2 : ℤ) • spinVorticity P A B) ∧
    Matrix.trace (ρ * Y * X) = Matrix.trace (X * (ρ * Y * ρ_inv) * ρ) ∧
    (lam * Real.exp (-x) - lam * Real.exp x) / (Real.exp (-x) + Real.exp x) =
      -lam * Real.tanh x := by
  have hAddLaw :
      rotatedSolderLoop P A B (θ₁ + θ₂) =
        Real.cos θ₂ • rotatedSolderLoop P A B θ₁ +
          Real.sin θ₂ • rotatedSolderVelocity P A B θ₁ := by
    dsimp [rotatedSolderLoop, rotatedSolderVelocity]
    rw [Real.cos_add, Real.sin_add, smul_add, smul_add,
      smul_smul, smul_smul, smul_smul, smul_smul,
      add_add_add_comm, ← add_smul, ← add_smul]
    have hc : Real.cos θ₂ * Real.cos θ₁ + Real.sin θ₂ * -Real.sin θ₁ =
        Real.cos θ₁ * Real.cos θ₂ - Real.sin θ₁ * Real.sin θ₂ := by ring
    have hs : Real.cos θ₂ * Real.sin θ₁ + Real.sin θ₂ * Real.cos θ₁ =
        Real.sin θ₁ * Real.cos θ₂ + Real.cos θ₁ * Real.sin θ₂ := by ring
    rw [hc, hs]
  have hCyc := rung5_cyclotronic_geodesic_along_closed_timelike_loop hP A B θ
  have hKMS : Matrix.trace (ρ * Y * X) = Matrix.trace (X * (ρ * Y * ρ_inv) * ρ) := by
    calc
      Matrix.trace (ρ * Y * X)
          = Matrix.trace (X * (ρ * Y)) := Matrix.trace_mul_comm (ρ * Y) X
      _ = Matrix.trace (X * ((ρ * Y) * 1)) := by rw [mul_one]
      _ = Matrix.trace (X * ((ρ * Y) * (ρ_inv * ρ))) := by rw [← hRhoInv]
      _ = Matrix.trace (X * (ρ * Y * ρ_inv) * ρ) := by simp only [Matrix.mul_assoc]
  have hTanh :
      (lam * Real.exp (-x) - lam * Real.exp x) / (Real.exp (-x) + Real.exp x) =
        -lam * Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have hpos : 0 < Real.exp x + Real.exp (-x) := add_pos (Real.exp_pos x) (Real.exp_pos (-x))
    have hne : Real.exp x + Real.exp (-x) ≠ 0 := ne_of_gt hpos
    have hne' : Real.exp (-x) + Real.exp x ≠ 0 := by linarith
    field_simp [hne, hne']
    ring
  exact ⟨hAddLaw, hCyc.2.1, hCyc.2.2.2.2.2.2, hKMS, hTanh⟩

/-- Effective Tolman–Hawking–Unruh inverse temperature $\beta_{\mathrm{eff}}(\beta, \theta) := \beta\,\cos(2\theta)$. -/
noncomputable def effectiveInverseTemp (β θ : ℝ) : ℝ :=
  β * Real.cos (2 * θ)

/-- Radial Gödel inverse temperature $\beta_{\mathrm{rad}}(\beta, r) := \beta\,\frac{1 - \sinh^2 r}{1 + \sinh^2 r}$. -/
noncomputable def radialInverseTemp (β r : ℝ) : ℝ :=
  β * ((1 - Real.sinh r ^ 2) / (1 + Real.sinh r ^ 2))

/-- KMS shell log-weight exponent $-\beta_{\mathrm{eff}}(\beta, \theta)\,\lambda - \beta\,\kappa^2\,\lambda^2$. -/
noncomputable def kmsShellExponent (β θ κ lam : ℝ) : ℝ :=
  -effectiveInverseTemp β θ * lam - β * κ ^ 2 * lam ^ 2

/-- Optimal torsion condensate eigenvalue $\lambda_*(\theta, \kappa) := -\frac{\cos(2\theta)}{2\kappa^2}$. -/
noncomputable def optimalTorsionEigenvalue (θ κ : ℝ) : ℝ :=
  -Real.cos (2 * θ) / (2 * κ ^ 2)

/-- **Stage `𝔚𝔊₂₉` / Rung 10 Theorem 4 (`wg29_horizon_temperature_inversion_and_torsion_condensate_peak`) —
Tolman–Hawking–Unruh Horizon Temperature Inversion $\beta_{\mathrm{eff}}(\theta) = \beta\cos(2\theta)$ & Torsion Condensate Peak**:
1. **Exact Gödel Radial Coordinate Bridge ($\tan\theta = \sinh r$)**:
   $$\beta * \big(\cos^2\theta(r) - \sin^2\theta(r)\big) = \beta_{\mathrm{rad}}(\beta, r) =
     \beta * \frac{1 - \sinh^2 r}{1 + \sinh^2 r}$$
2. **Three Thermodynamic Regimes Across the Velocity-of-Light Cylinder ($\theta_c = \pi / 4$, $\theta'_c = 3\pi / 4$)**:
   $$\beta_{\mathrm{eff}}(\beta, 0) = \beta, \qquad
     \beta_{\mathrm{eff}}(\beta, \pi/4) = 0, \qquad
     \beta_{\mathrm{eff}}(\beta, \pi/2) = -\beta, \qquad
     \beta_{\mathrm{eff}}(\beta, 3\pi/4) = 0$$
3. **Exact Completion of the Square for the KMS Torsion Condensate Peak ($\kappa \ne 0$)**:
   $$-\beta_{\mathrm{eff}}(\beta, \theta)\,\lambda - \beta\,\kappa^2\,\lambda^2 =
     -\beta\,\kappa^2\,\big(\lambda - \lambda_*(\theta, \kappa)\big)^2 +
       \frac{\beta\,\cos^2(2\theta)}{4\kappa^2}, \qquad
     \lambda_*(\theta, \kappa) = -\frac{\cos(2\theta)}{2\kappa^2}$$
4. **Spontaneous Torsion Condensate Peak in the Population-Inverted CTL Regime ($\beta > 0$, $\kappa \ne 0$, $\cos(2\theta) < 0$)**:
   $$\boxed{\beta_{\mathrm{eff}}(\beta, \theta) < 0, \qquad
     0 < \lambda_*(\theta, \kappa), \qquad
     \forall \lambda \in \mathbb{R},\;
       \mathrm{kmsShellExponent}(\beta, \theta, \kappa, \lambda) \le
         \mathrm{kmsShellExponent}(\beta, \theta, \kappa, \lambda_*(\theta, \kappa))}$$ -/
theorem wg29_horizon_temperature_inversion_and_torsion_condensate_peak
    (β θ r κ lam : ℝ) (hβ : 0 < β) (hκ : κ ≠ 0) (hCTL : Real.cos (2 * θ) < 0) :
    β * (godelChiralCos r ^ 2 - godelChiralSin r ^ 2) = radialInverseTemp β r ∧
    effectiveInverseTemp β 0 = β ∧
    effectiveInverseTemp β (Real.pi / 4) = 0 ∧
    effectiveInverseTemp β (Real.pi / 2) = -β ∧
    effectiveInverseTemp β (3 * Real.pi / 4) = 0 ∧
    kmsShellExponent β θ κ lam =
      -β * κ ^ 2 * (lam - optimalTorsionEigenvalue θ κ) ^ 2 +
        β * Real.cos (2 * θ) ^ 2 / (4 * κ ^ 2) ∧
    effectiveInverseTemp β θ < 0 ∧
    0 < optimalTorsionEigenvalue θ κ ∧
    kmsShellExponent β θ κ (optimalTorsionEigenvalue θ κ) =
      β * Real.cos (2 * θ) ^ 2 / (4 * κ ^ 2) ∧
    kmsShellExponent β θ κ lam ≤
      kmsShellExponent β θ κ (optimalTorsionEigenvalue θ κ) := by
  have hRad :
      β * (godelChiralCos r ^ 2 - godelChiralSin r ^ 2) = radialInverseTemp β r := by
    have h8 := (wg8_godel_1949_metric_coordinate_dictionary
      (P := (0 : ℝ)) (show IsIdempotentElem (0 : ℝ) from zero_mul 0) 0 0 r).2.2.1
    dsimp [radialInverseTemp]
    rw [h8]
  have h0 : effectiveInverseTemp β 0 = β := by
    dsimp [effectiveInverseTemp]
    simp
  have hPi4 : effectiveInverseTemp β (Real.pi / 4) = 0 := by
    dsimp [effectiveInverseTemp]
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two, mul_zero]
  have hPi2 : effectiveInverseTemp β (Real.pi / 2) = -β := by
    dsimp [effectiveInverseTemp]
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi, mul_neg_one]
  have h3Pi4 : effectiveInverseTemp β (3 * Real.pi / 4) = 0 := by
    dsimp [effectiveInverseTemp]
    rw [show 2 * (3 * Real.pi / 4) = Real.pi / 2 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_two, neg_zero, mul_zero]
  have hκ2_pos : 0 < κ ^ 2 := sq_pos_of_ne_zero hκ
  have hκ2_ne : κ ^ 2 ≠ 0 := ne_of_gt hκ2_pos
  have hSqComp :
      kmsShellExponent β θ κ lam =
        -β * κ ^ 2 * (lam - optimalTorsionEigenvalue θ κ) ^ 2 +
          β * Real.cos (2 * θ) ^ 2 / (4 * κ ^ 2) := by
    dsimp [kmsShellExponent, effectiveInverseTemp, optimalTorsionEigenvalue]
    field_simp [hκ2_ne]
    ring
  have hNegBeta : effectiveInverseTemp β θ < 0 := by
    dsimp [effectiveInverseTemp]
    exact mul_neg_of_pos_of_neg hβ hCTL
  have hLambdaStarPos : 0 < optimalTorsionEigenvalue θ κ := by
    dsimp [optimalTorsionEigenvalue]
    have hnum : 0 < -Real.cos (2 * θ) := neg_pos.mpr hCTL
    have hden : 0 < 2 * κ ^ 2 := by positivity
    exact div_pos hnum hden
  have hPeakVal :
      kmsShellExponent β θ κ (optimalTorsionEigenvalue θ κ) =
        β * Real.cos (2 * θ) ^ 2 / (4 * κ ^ 2) := by
    dsimp [kmsShellExponent, effectiveInverseTemp, optimalTorsionEigenvalue]
    field_simp [hκ2_ne]
    ring
  have hMax :
      kmsShellExponent β θ κ lam ≤
        kmsShellExponent β θ κ (optimalTorsionEigenvalue θ κ) := by
    rw [hSqComp, hPeakVal]
    have hnonneg : 0 ≤ β * κ ^ 2 * (lam - optimalTorsionEigenvalue θ κ) ^ 2 := by positivity
    linarith
  exact ⟨hRad, h0, hPi4, hPi2, h3Pi4, hSqComp, hNegBeta, hLambdaStarPos, hPeakVal, hMax⟩

/-- Reachability from Stage `𝔚𝔊₁` to the terminal Rung 10 Stage `𝔚𝔊₂₉`. -/
theorem causalEdge_W1_to_W29 :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W29_TolmanHawkingUnruhHorizonTemperatureInversionAndTorsionPeak := by
  have h1_25 := causalEdge_W1_to_W25
  have h1_26 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W26_CentralIncompletenessAndModularUncertaintyDerivation :=
    Relation.TransGen.tail h1_25 trivial
  have h1_27 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W27_TomitaTakesakiPolarDecompositionAndHorizonEigenOperators :=
    Relation.TransGen.tail h1_26 trivial
  have h1_28 : Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W28_ConnesRovelliKMSThermalTimeAndCyclotronicGeodesic :=
    Relation.TransGen.tail h1_27 trivial
  exact Relation.TransGen.tail h1_28 trivial

/-- **29-Stage Wheeler–Gödel–Bruhat–Connes–Chamseddine–Tomita–KMS Master Synthesis
(`wheeler_godel_twenty_nine_stage_master_synthesis`)**:
Unifies the complete 29-stage poset `𝔚𝔊₁ ≺ ⋯ ≺ 𝔚𝔊₂₉` across Rungs 1–10:
1. Full 29-stage causal reachability `𝔚𝔊₁ ≺⁺ 𝔚𝔊₂₉` and global chronology protection,
2. Rung 9 Orthogonal Clifford Triad, Lichnerowicz–Weitzenböck Square, Chamseddine–Connes Bosonic
   Spectral Action & Nieh–Yan Duality, Gödel's 1949 Cosmological Constant Law
   $\Lambda_{\mathrm{eff}} = -\omega_{\mathrm{rot}}^2 = -\frac{1}{2}\mathcal{R} < 0$, and
   Fermionic Horizon Valve (`wheeler_godel_twenty_five_stage_master_synthesis`),
3. Rung 10 Centrality of the Incompleteness Metric $V \in \mathcal{Z}(\mathcal{M})$ and Modular
   Uncertainty Derivation $⁅\Sigma, X⁆ = V * ⁅S_P, X⁆$
   (`wg26_central_incompleteness_and_modular_uncertainty_derivation`),
4. Rung 10 Tomita Star Conjugation $\mathrm{star}(N_\pm(A)) = N_\mp(\mathrm{star}\;A)$, Central
   Lichnerowicz Factor Cancellation, and Horizon Eigen-Operator Scaling
   (`wg27_tomita_takesaki_horizon_eigen_operators_and_central_cancellation`),
5. Rung 10 Connes–Rovelli Modular Rotation Group Law, Cyclotronic Harmonic Oscillator, KMS Detailed
   Balance Trace Identity, and $-\lambda\tanh(x)$ Thermal Vorticity Expectation
   (`wg28_connes_rovelli_kms_cyclotronic_geodesic_and_detailed_balance`),
6. Rung 10 Tolman–Hawking–Unruh Horizon Temperature Inversion $\beta_{\mathrm{eff}}(\pi/4) = 0$,
   $\beta_{\mathrm{eff}}(\pi/2) = -\beta$, and Spontaneous Torsion Condensate Peak $\lambda_* > 0$
   (`wg29_horizon_temperature_inversion_and_torsion_condensate_peak`). -/
theorem wheeler_godel_twenty_nine_stage_master_synthesis
    {R : Type*} [Ring R] [StarRing R] [Module ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
    {P : R} (hP : IsIdempotentElem P) (hP_star : star P = P)
    (A B Q_minus_inv P_perp : R)
    (hSchurInv : peircePlus P A * Q_minus_inv * peirceMinus P B = P_perp)
    (β θ κ R_WG Omega_sq α α_star lam x : ℝ)
    (hStat : R_WG = 2 * Omega_sq * α_star ^ 2)
    (hOmega : 0 < Omega_sq) (hAlpha : α_star ≠ 0)
    (hβ : 0 < β) (hκ : κ ≠ 0) (hCTL : Real.cos (2 * θ) < 0)
    {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]
    (M_A M_C ρ ρ_inv X Y : Matrix n n S) (hRhoInv : ρ_inv * ρ = 1) (m : ℕ) :
    Relation.TransGen causalEdge
      .W1_SingleChartChronologyProtection
      .W29_TolmanHawkingUnruhHorizonTemperatureInversionAndTorsionPeak ∧
    (∀ s : WheelerGodelStage, ¬ Relation.TransGen causalEdge s s) ∧
    diracCartanGodelLoop P A B θ κ * diracCartanGodelLoop P A B θ κ =
      Real.cos (2 * θ) • fisherMetricOp P A B +
        (κ ^ 2) • (spinVorticity P A B * spinVorticity P A B) ∧
    blockSupertrace (blockVorticity M_A M_C * blockFisher M_A M_C ^ m) =
      Matrix.trace (blockFisher M_A M_C ^ (m + 1)) ∧
    spectralEffPotential R_WG Omega_sq α_star = -(1 / 2) * (R_WG * α_star ^ 2) ∧
    (1 - P) * diracCartanGodelLoop P A B (Real.pi / 4) κ * P = 0 ∧
    ⁅spinVorticity P A B, peircePlus P A⁆ =
      fisherMetricOp P A B * ⁅chiralInv P, peircePlus P A⁆ ∧
    star (peircePlus P A) = peirceMinus P (star A) ∧
    Matrix.trace (ρ * Y * X) = Matrix.trace (X * (ρ * Y * ρ_inv) * ρ) ∧
    (lam * Real.exp (-x) - lam * Real.exp x) / (Real.exp (-x) + Real.exp x) =
      -lam * Real.tanh x ∧
    effectiveInverseTemp β (Real.pi / 4) = 0 ∧
    effectiveInverseTemp β θ < 0 ∧
    0 < optimalTorsionEigenvalue θ κ ∧
    kmsShellExponent β θ κ lam ≤
      kmsShellExponent β θ κ (optimalTorsionEigenvalue θ κ) := by
  have h25 := wheeler_godel_twenty_five_stage_master_synthesis
    hP A B Q_minus_inv P_perp hSchurInv θ κ R_WG Omega_sq α α_star hStat hOmega hAlpha M_A M_C m
  have h26 := wg26_central_incompleteness_and_modular_uncertainty_derivation hP A B
  have h27 := wg27_tomita_takesaki_horizon_eigen_operators_and_central_cancellation
    hP hP_star A B 1 1 1 1 P (mul_one 1) (by simp) 1 1 1 1
  have h28 := wg28_connes_rovelli_kms_cyclotronic_geodesic_and_detailed_balance
    hP A B θ 0 0 lam x ρ ρ_inv X Y hRhoInv
  have h29 := wg29_horizon_temperature_inversion_and_torsion_condensate_peak
    β θ 0 κ lam hβ hκ hCTL
  exact ⟨causalEdge_W1_to_W29, causalEdge_acyclic, h25.2.2.2.2.2.1,
    h25.2.2.2.2.2.2.2.1, h25.2.2.2.2.2.2.2.2.2.2.1, h25.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h26.2.2.2.2.2.2.2.2.2.2.1, h27.1, h28.2.2.2.1, h28.2.2.2.2,
    h29.2.2.1, h29.2.2.2.2.2.2.1, h29.2.2.2.2.2.2.2.1, h29.2.2.2.2.2.2.2.2.2⟩

/-! ## §12. Wheeler — *Thoughts on Gödel (Part 2)* (Segment 93/130) Seven-Node Poset (`𝔍𝔚₁ ≺ ⋯ ≺ 𝔍𝔚₇`) -/

/-- **Node `𝔍𝔚₁` (Mach's Relational Boundary Principle)**:
Relative displacement `(x + c) - (y + c) = x - y` is invariant under any global background shift `c`,
eliminating absolute background coordinates in favor of relational differences. -/
theorem mach_relational_translation_invariance {G : Type*} [AddCommGroup G] (x y c : G) :
    (x + c) - (y + c) = x - y := by
  abel

/-- **Node `𝔍𝔚₃` (Gödel's Closed Time-Like Loop Periodicity)**:
A closed time-like loop `step^[L] x0 = x0` forces exact periodic recurrence
`step^[m + L] x0 = step^[m] x0` along every future iterate `m`, collapsing global causal
irreflexivity into modular time periodicity. -/
theorem godel_closed_timelike_loop_periodicity {α : Type*} (step : α → α) (x0 : α) (L m : ℕ)
    (h_loop : (step^[L] x0) = x0) :
    (step^[m + L] x0) = (step^[m] x0) := by
  rw [Function.iterate_add_apply, h_loop]

/-- **Node `𝔍𝔚₄` (Peebles' Statistical Isotropy & Cancellation of Cosmic Rotation)**:
Under a parity-reversing sky involution `σ` with `spin (σ g) = - spin g`, every paired galaxy line
of sight `(g, σ g)` sums to zero net cosmic angular momentum `spin g + spin (σ g) = 0`. -/
theorem peebles_isotropy_no_preferred_rotation
    {Galaxy R : Type*} [AddCommGroup R] (σ : Galaxy → Galaxy) (spin : Galaxy → R)
    (h_odd : ∀ g, spin (σ g) = - spin g) (g : Galaxy) :
    spin g + spin (σ g) = 0 := by
  rw [h_odd g]
  abel

/-- **Master Synthesis of Segment 93/130 (*Thoughts on Gödel, Part 2*, `𝔍𝔚₁ ≺ ⋯ ≺ 𝔍𝔚₇`)**:
Unifies across any associative ring `[Ring B]` with idempotent projectors `P, Q : B`
(`hP : P * P = P`, `hQ : Q * Q = Q`):
1. `𝔍𝔚₁`: Machian relational translation invariance `(x + c) - (y + c) = x - y`,
2. `𝔍𝔚₃`: Closed time-like loop periodicity `step^[m + L] x0 = step^[m] x0`,
3. `𝔍𝔚₄`: Peebles parity cancellation `spin g + spin (σ g) = 0`,
4. `𝔍𝔚₅`: The Heisenberg–Gödel Commutator–Undecidability Bridge
   (`comm P Q = conePlus P Q - coneMinus P Q`, `comm P Q * comm P Q + genV P Q Q = 0`,
    `peirce11 P Q - peirce11 P Q * peirce11 P Q = conePlus P Q * coneMinus P Q`,
    `peirce00 P Q - peirce00 P Q * peirce00 P Q = coneMinus P Q * conePlus P Q`, and
    their sum equals `genV P Q Q`),
5. `𝔍𝔚₇`: Wheeler's equivalence between non-vanishing cross-boundary Peirce transport
   ("How come the quantum?") and non-vanishing diagonal idempotence defect
   ("How come existence?"). -/
theorem wheeler_godel_part_two_seven_node_poset_synthesis
    {B : Type*} [Ring B] {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q)
    {G : Type*} [AddCommGroup G] (x y c : G)
    {α : Type*} (step : α → α) (x0 : α) (L m : ℕ) (h_loop : (step^[L] x0) = x0)
    {Galaxy : Type*} (σ : Galaxy → Galaxy) (spin : Galaxy → G)
    (h_odd : ∀ g, spin (σ g) = - spin g) (g : Galaxy) :
    ((x + c) - (y + c) = x - y) ∧
    ((step^[m + L] x0) = (step^[m] x0)) ∧
    (spin g + spin (σ g) = 0) ∧
    (OperatorAlgebra.PeirceSpine.comm P Q = conePlus P Q - coneMinus P Q ∧
     OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q + genV P Q Q = 0 ∧
     OperatorAlgebra.PeirceSpine.peirce11 P Q -
       OperatorAlgebra.PeirceSpine.peirce11 P Q * OperatorAlgebra.PeirceSpine.peirce11 P Q =
       conePlus P Q * coneMinus P Q ∧
     OperatorAlgebra.PeirceSpine.peirce00 P Q -
       OperatorAlgebra.PeirceSpine.peirce00 P Q * OperatorAlgebra.PeirceSpine.peirce00 P Q =
       coneMinus P Q * conePlus P Q ∧
     (OperatorAlgebra.PeirceSpine.peirce11 P Q -
        OperatorAlgebra.PeirceSpine.peirce11 P Q * OperatorAlgebra.PeirceSpine.peirce11 P Q) +
       (OperatorAlgebra.PeirceSpine.peirce00 P Q -
          OperatorAlgebra.PeirceSpine.peirce00 P Q * OperatorAlgebra.PeirceSpine.peirce00 P Q) =
       genV P Q Q) ∧
    ((conePlus P Q * coneMinus P Q ≠ 0 ∨ coneMinus P Q * conePlus P Q ≠ 0) ↔
      (OperatorAlgebra.PeirceSpine.peirce11 P Q -
         OperatorAlgebra.PeirceSpine.peirce11 P Q * OperatorAlgebra.PeirceSpine.peirce11 P Q ≠ 0 ∨
       OperatorAlgebra.PeirceSpine.peirce00 P Q -
         OperatorAlgebra.PeirceSpine.peirce00 P Q * OperatorAlgebra.PeirceSpine.peirce00 P Q ≠ 0)) := by
  have h_mach : (x + c) - (y + c) = x - y := by abel
  have h_spin : spin g + spin (σ g) = 0 := by rw [h_odd g, add_neg_cancel]
  exact ⟨h_mach,
         godel_closed_timelike_loop_periodicity step x0 L m h_loop,
         h_spin,
         OperatorAlgebra.PeirceSpine.heisenberg_godel_commutator_undecidability_bridge hP hQ,
         OperatorAlgebra.PeirceSpine.wheeler_how_come_quantum_iff_how_come_existence hP hQ⟩

end InfoGeometry.Canonical.WheelerGodelRotatingUniverseChronologyPoset

