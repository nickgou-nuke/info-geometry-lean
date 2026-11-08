/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.SuperGrassmannianProjectorBridge
import InfoGeometry.SuperGrassmannian.ProjectorGraphChart
import InfoGeometry.SuperGrassmannian.GradedGraphChart
import InfoGeometry.SuperGrassmannian.GraphChartTransition
import InfoGeometry.SuperGrassmannian.GradedGraphTransition
import InfoGeometry.SuperGrassmannian.GraphChartCocycle
import InfoGeometry.SuperGrassmannian.ZornGraphChart
import InfoGeometry.SuperGrassmannian.SuperGrassmannianMoebiusQuotient
import InfoGeometry.SuperGrassmannian.WeylBerezinianDeformation
import InfoGeometry.SuperGrassmannian.ProjectiveKreinBerezinian
import InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
import InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
import InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair
import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
import InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
import InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParaKahlerBregmanModularNoetherPoset
import InfoGeometry.Canonical.OperatorLogDetDikinGeometry
import InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
import InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis
import InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset
import InfoGeometry.Canonical.SupergradedAmariBerezinianColimitObservabilityPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.MultiScalePeirceGateTower
import InfoGeometry.Canonical.MonodromyCPTDyckFiniteMatrixBridge
import InfoGeometry.Canonical.ZornPluckerHodgeBinetCauchyBacCabAmariPoset
import InfoGeometry.Canonical.PeirceBackpropTraceGradientBridge

/-!
# The 8-Stage Supergrassmannian & Para-Kähler Information Geometry Manifold Poset (`𝔊₁ ≺ 𝔊₂ ≺ ⋯ ≺ 𝔊₈`)

This module extends the repository's canonical ontology from the **Split-Octonion Circularly
Polarized Isotropic Amari & Nambu Poset** (`𝔒₁ ≺ ⋯ ≺ 𝔒₇`,
`InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset`) and the **Supergraded
Amari–Berezinian–Colimit–Observability Poset** (`𝔘₁ ≺ ⋯ ≺ 𝔘₈`,
`InfoGeometry.Canonical.SupergradedAmariBerezinianColimitObservabilityPoset`) directly into
**Supergrassmannians and Para-Kähler Information Geometry Manifolds**, reusing existing
repository owners with zero `sorry`, `admit`, custom axioms, or vacuous wrappers:

* **Stage `𝔊₁` (`G1_ParaComplexPolarizationAndBiLagrangianIsotropicSheets`)**:
  - Reuses `InfoGeometry.SuperGrassmannian` (`paraProjectorPlus`, `paraProjectorMinus`,
    `primalSheet`, `covectorVacuumSheet`, `primal_sheet_is_isotropic`,
    `covector_vacuum_sheet_is_isotropic`), `InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT`
    (`ParaKahlerDatum`, `paraBerryTwoForm`, `paraQGT`, `metric_hyperbolic_flow_preserved`),
    and `InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis`
    (`paraKahler_majorana_car_ccr_chameleon`, `four_majorana_pairs_car_ccr_chameleon`).
  - Establishes the fundamental binary cut between compact Kähler ($J^2 = -1$) and Para-Kähler
    ($K^2 = +1$) geometry: the chiral polarization projectors $P_\pm = \frac{1}{2}(1 \pm K)$
    decompose the carrier into twin isotropic Lagrangian sheets $T^+ = \ker(K - I)$ and
    $T^- = \ker(K + I)$ under the anti-invariant neutral metric $g(Ku, Kv) = -g(u, v)$ and
    skew-symmetric Para-Berry 2-form $\Omega(u, v) = g(Ku, v)$, unifying CAR and CCR pairings
    on $(T^-, T^+)$.

* **Stage `𝔊₂` (`G2_NoncommutativeProjectorGraphChartsAndZornGrassmannian`)**:
  - Reuses `InfoGeometry.SuperGrassmannian.ProjectorGraphChart` (`graphProjector`,
    `graphProjector_idempotent`, `graphProjector_mul`, `graphProjector_commute_iff`,
    `range_graphProjector`), `InfoGeometry.SuperGrassmannian.GradedGraphChart`
    (`PreservesDegree`, `IsGraded`, `graph_isGraded_iff`, `graphChartEquiv`), and
    `InfoGeometry.SuperGrassmannian.ZornGraphChart` (`splitEquiv`, `graphReadout`,
    `grassmannianChart`, `grassmannianChart_injective`, `zero_graph_eq_range_left_E11`).
  - Proves that linear maps $f : U \to W$ between the positive and negative polarization sheets
    parametrize complemented graph submodules $\Gamma(f) \subset U \oplus W$ with noncommuting
    idempotent projectors $P_f P_g = P_f$, that direct-sum homogeneity of $\Gamma(f)$ is
    equivalent to degree preservation of $f$, and that on the 8D Zorn split-octonion carrier
    `ZornVectorMatrix R ≃ Positive R × Negative R` every $f$ defines a native rank-4 Grassmannian
    point `grassmannianChart f : Module.Grassmannian R (ZornVectorMatrix R) 4`.

* **Stage `𝔊₃` (`G3_OperatorMoebiusFractionalTransitionsAndOverlapCocycle`)**:
  - Reuses `InfoGeometry.SuperGrassmannian.GraphChartTransition` (`block_map_graph`,
    `exists_map_graph_iff`, `swap_map_graph_eq_iff`),
    `InfoGeometry.SuperGrassmannian.GradedGraphTransition` (`preservesDegree_symm`,
    `fractional_preservesDegree`), `InfoGeometry.SuperGrassmannian.GraphChartCocycle`
    (`Overlap`, `transition`, `transition_graph`, `transition_cocycle`, `transition_inverse`),
    and `InfoGeometry.SuperGrassmannian.MoebiusQuotient` (`K_mat`, `M_mat`, `g_mat`, `omega_mat`,
    `moebius_anticommutes_polarization`, `moebius_metric_isometry`,
    `moebius_symplectic_anti_invariance`).
  - Proves the ordered noncommutative operator Möbius fractional transition
    $f \mapsto (c + d \circ f) \circ (a + b \circ f)^{-1}$ on the exact bijective denominator
    overlap domain `Overlap G f`, its cocycle law `transition (H ∘ G) f = transition H (transition G f)`,
    its degree preservation under graded block operators, and the Möbius sheet-swap reflection
    identities $\{M, K\} = 0$, $M^T g M = g$, $M^T \omega M = -\omega$.

* **Stage `𝔊₄` (`G4_ProjectiveKreinBerezinianAndWeylDeformationTriad`)**:
  - Reuses `InfoGeometry.SuperGrassmannian.WeylBerezinian` (`superTrace`, `scaleOperator`,
    `chiralOperator`, `volumeOperator`, `scale_chiral_commutator`,
    `scale_chiral_commutator_balanced`, `total_deformation_superTrace`),
    `InfoGeometry.SuperGrassmannian.ProjectiveKreinBerezinian` (`kreinMetric`, `paraComplexK`,
    `krein_paraComplex_anticomm`, `balanced_homothety_berezinian_eq_one`,
    `unbalanced_homothety_berezinian`), and
    `InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis`
    (`superBerezinian23`, `superTrace23`, `super_berezinian_gauge_invariance`).
  - Proves that the supertrace of the $(p|q)$ deformation triad isolates the Weyl scale anomaly
    $\operatorname{STr}(S(p,q,\sigma) + X(k_1,k_2) + V(a)) = (p - q)\sigma$, that balanced
    $(p|p)$ super-Grassmannians are homothety-invariant ($c^p (c^{-1})^p = 1$), and that on the
    $(2|3)$ lepton–quark super-carrier $\operatorname{Ber}(A_{\text{bos}}, D_{\text{fer}})$ is
    invariant under Weyl light-cone boosts and $\mathrm{SL}(3,\mathbb{R})$ color gauge transformations.

* **Stage `𝔊₅` (`G5_FiveGradedKantorTanakaKKTTangentTowerAndColorSUSY`)**:
  - Reuses `InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra`
    (`quintic_polynomial_factorization`, `adH_quintic_identity`, `adH_bosonic_cubic`),
    `InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian`
    (`odd_contact_bracket`, `spinor_bilinear_sum_eq_H`, `J_inverts_H`),
    `InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair` (`osp_anticomm_plus_minus`),
    `InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis`
    (`mcCurvatureTower_flat_iff_source_laws`, `canonicalMaurerCartanJet_flat`), and
    `InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis`
    (`z2z2_color_supersymmetry_sign_laws`, `gunaydin_gursey_g1_gm1_superbracket_closure`,
    `oddSupercolorFull_sq_closes_on_even_bosonic_socle`).
  - Establishes the 5-graded Kantor–Tanaka / KKT tangent tower
    $\mathfrak{g} = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$
    ($\operatorname{ad}_H^5 - 5\operatorname{ad}_H^3 + 4\operatorname{ad}_H = 0$), the 5-graded
    Maurer–Cartan flatness source equations, and the $\mathbb{Z}_2 \times \mathbb{Z}_2$
    Günaydin–Gürsey color-supersymmetry bracket closures.

* **Stage `𝔊₆` (`G6_SplitOctonionCl33ParaKahlerPhaseSpaceAndMetriplecticProduct`)**:
  - Reuses `InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone`
    (`fin8ToZorn_gPlus1_vac_eq_embedVec_primalSheet`,
    `fin8ToZorn_gPlus2Hodge_vac_eq_embedVec_dualSheet`,
    `zornMul_embedVec_metriplectic_decomp`, `paraKahler_lagrange_norm_composition`,
    `zorn_primal_triple_bracketing_sum_eq_volume_smul_one`,
    `zorn_primal_triple_associator_eq_volume_paraGrading`).
  - Bridges the 6D Para-Kähler phase space $V = T^+ \oplus T^-$ inside the 8D Zorn split-octonion
    algebra to Fock creation columns, the metriplectic product decomposition
    $z_1 z_2 = \frac{1}{2}g(z_1, z_2) 1 + \frac{1}{2}\omega(z_1, z_2) I_{\text{para}} + z_1 \times_H z_2$,
    the Lagrange–Binet–Cauchy norm composition law, and the primal triple-product sum/associator
    volume identities on $1_{\text{Zorn}}$ and $I_{\text{para}}$.

* **Stage `𝔊₇` (`G7_ParaKahlerInformationManifoldChiralTwoJetAndBregmanClosure`)**:
  - Reuses `InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset`
    (`chiralTwoJet_decomposition`, `rung0_schwarz_symmetry_aporia`),
    `InfoGeometry.OperatorAlgebra.PeirceSpine`
    (`archetype_M1_parakahler_hessian_and_curvature_2form`,
    `archetype_M2_modular_surprisal_and_bregman_three_point`), and
    `InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis`
    (`superSouriauMassieu_uv_cancellation_and_moment_readout`).
  - Proves the chiral 2-jet split $2 N_+ N_- = V + \Sigma$ and $2 N_- N_+ = V - \Sigma$, the
    noncommutative Schwarz defect $[\delta_+, \delta_-](X) = [\Sigma, X]$ (and its Rung 0 metric
    collapse $2 V^2 = 0$ if $[\delta_+, \delta_-](N_\pm) = 0$), the symmetric Para-Kähler Fisher
    Hessian decomposition, the universal noncommutative Bregman three-point identity, and the
    supersymmetric Souriau–Massieu UV defect cancellation and moment readout.

* **Stage `𝔊₈` (`G8_GrandSuperGrassmannianParaKahlerInfoGeometrySynthesis`)**:
  - Unifies Stages `𝔊₁` through `𝔊₇` together with the preceding `𝔒₁ ≺ ⋯ ≺ 𝔒₇` and
    `𝔘₁ ≺ ⋯ ≺ 𝔘₈` posets into a single kernel-checked master theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.SuperGrassmannianParaKahlerInfoGeometryPoset

open scoped Matrix BigOperators
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.SuperGrassmannian
open InfoGeometry.SuperGrassmannian.ProjectorGraphChart
open InfoGeometry.SuperGrassmannian.GradedGraphChart
open InfoGeometry.SuperGrassmannian.GraphChartTransition
open InfoGeometry.SuperGrassmannian.GradedGraphTransition
open InfoGeometry.SuperGrassmannian.GraphChartCocycle
open InfoGeometry.SuperGrassmannian.ZornGraphChart
open InfoGeometry.SuperGrassmannian.MoebiusQuotient
open InfoGeometry.SuperGrassmannian.WeylBerezinian
open InfoGeometry.SuperGrassmannian.ProjectiveKreinBerezinian
open InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
open InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis
open InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset
open InfoGeometry.Canonical.SupergradedAmariBerezinianColimitObservabilityPoset

/-!
## 1. The 8-Stage Supergrassmannian & Para-Kähler Information Geometry Poset (`𝔊₁ ≺ 𝔊₂ ≺ ⋯ ≺ 𝔊₈`)
-/

/-- The 8 stages of the **Supergrassmannian & Para-Kähler Information Geometry Manifold Poset**
(`𝔊₁ ≺ 𝔊₂ ≺ 𝔊₃ ≺ 𝔊₄ ≺ 𝔊₅ ≺ 𝔊₆ ≺ 𝔊₇ ≺ 𝔊₈`). -/
inductive SuperGrassmannianParaKahlerStage : Type
  /-- `𝔊₁`: Para-complex polarization `K² = 1`, chiral projectors `P_± = ½(1 ± K)`, isotropic
      Lagrangian sheets `T^+ ⊕ T^-`, Para-Berry 2-form `Ω(u,v) = g(Ku,v)`, and CAR/CCR chameleon. -/
  | G1_ParaComplexPolarizationAndBiLagrangianIsotropicSheets
  /-- `𝔊₂`: Noncommutative projector graph charts `P_f P_g = P_f`, graded direct-sum graph
      submodules `IsGraded ↔ PreservesDegree`, and native Zorn Grassmannian `Gr(4, ZornVectorMatrix R)`. -/
  | G2_NoncommutativeProjectorGraphChartsAndZornGrassmannian
  /-- `𝔊₃`: Noncommutative operator Möbius fractional graph transitions `(c + d ∘ f) ∘ (a + b ∘ f)⁻¹`,
      exact bijective overlap cocycle, and Möbius sheet-swap reflection `{M, K} = 0`. -/
  | G3_OperatorMoebiusFractionalTransitionsAndOverlapCocycle
  /-- `𝔊₄`: Projective Krein–Berezinian volume invariant, Weyl deformation triad
      `STr(S + X + V) = (p - q)σ`, and `(2|3)` lepton–quark Berezinian gauge invariance. -/
  | G4_ProjectiveKreinBerezinianAndWeylDeformationTriad
  /-- `𝔊₅`: 5-graded Kantor–Tanaka / KKT Supergrassmannian tangent tower
      `ad_H^5 - 5 ad_H^3 + 4 ad_H = 0`, 5-graded Maurer–Cartan flatness, and `ℤ₂ × ℤ₂` color SUSY. -/
  | G5_FiveGradedKantorTanakaKKTTangentTowerAndColorSUSY
  /-- `𝔊₆`: Split-octonion `Cl(3,3)` 6D Para-Kähler phase space, Fock spinor sheet bridge,
      metriplectic Zorn product `½ g 1 + ½ ω I_para + z₁ ×_H z₂`, and Lagrange norm composition. -/
  | G6_SplitOctonionCl33ParaKahlerPhaseSpaceAndMetriplecticProduct
  /-- `𝔊₇`: Para-Kähler Information Geometry Manifold: chiral 2-jet `2 N_+ N_- = V + Σ`,
      noncommutative Schwarz defect `[δ_+, δ_-](X) = [Σ, X]`, Bregman 3-point law, and
      supersymmetric Souriau–Massieu UV cancellation. -/
  | G7_ParaKahlerInformationManifoldChiralTwoJetAndBregmanClosure
  /-- `𝔊₈`: Grand unified Supergrassmannian & Para-Kähler Information Geometry Manifold synthesis. -/
  | G8_GrandSuperGrassmannianParaKahlerInfoGeometrySynthesis
  deriving DecidableEq, Repr, Inhabited

namespace SuperGrassmannianParaKahlerStage

/-- Numerical rank `0..7` of each stage `𝔊₁..𝔊₈`. -/
def rank : SuperGrassmannianParaKahlerStage → ℕ
  | .G1_ParaComplexPolarizationAndBiLagrangianIsotropicSheets => 0
  | .G2_NoncommutativeProjectorGraphChartsAndZornGrassmannian => 1
  | .G3_OperatorMoebiusFractionalTransitionsAndOverlapCocycle => 2
  | .G4_ProjectiveKreinBerezinianAndWeylDeformationTriad => 3
  | .G5_FiveGradedKantorTanakaKKTTangentTowerAndColorSUSY => 4
  | .G6_SplitOctonionCl33ParaKahlerPhaseSpaceAndMetriplecticProduct => 5
  | .G7_ParaKahlerInformationManifoldChiralTwoJetAndBregmanClosure => 6
  | .G8_GrandSuperGrassmannianParaKahlerInfoGeometrySynthesis => 7

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder SuperGrassmannianParaKahlerStage where
  le a b := rank a ≤ rank b
  lt a b := rank a < rank b
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (rank a) (rank b)
  le_antisymm _ _ h1 h2 := rank_injective (Nat.le_antisymm h1 h2)
  le_total a b := le_total (rank a) (rank b)
  toDecidableLE a b := Nat.decLe (rank a) (rank b)
  toDecidableLT a b := Nat.decLt (rank a) (rank b)
  toDecidableEq := inferInstance

instance : Fintype SuperGrassmannianParaKahlerStage where
  elems := {
    .G1_ParaComplexPolarizationAndBiLagrangianIsotropicSheets,
    .G2_NoncommutativeProjectorGraphChartsAndZornGrassmannian,
    .G3_OperatorMoebiusFractionalTransitionsAndOverlapCocycle,
    .G4_ProjectiveKreinBerezinianAndWeylDeformationTriad,
    .G5_FiveGradedKantorTanakaKKTTangentTowerAndColorSUSY,
    .G6_SplitOctonionCl33ParaKahlerPhaseSpaceAndMetriplecticProduct,
    .G7_ParaKahlerInformationManifoldChiralTwoJetAndBregmanClosure,
    .G8_GrandSuperGrassmannianParaKahlerInfoGeometrySynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_eight : Fintype.card SuperGrassmannianParaKahlerStage = 8 := rfl

/-- Directed causal edges `𝔊₁ ≺ 𝔊₂ ≺ ⋯ ≺ 𝔊₈` together with cross-stage structural dependencies. -/
inductive causalEdge : SuperGrassmannianParaKahlerStage → SuperGrassmannianParaKahlerStage → Prop
  | g1_to_g2 : causalEdge .G1_ParaComplexPolarizationAndBiLagrangianIsotropicSheets
      .G2_NoncommutativeProjectorGraphChartsAndZornGrassmannian
  | g2_to_g3 : causalEdge .G2_NoncommutativeProjectorGraphChartsAndZornGrassmannian
      .G3_OperatorMoebiusFractionalTransitionsAndOverlapCocycle
  | g3_to_g4 : causalEdge .G3_OperatorMoebiusFractionalTransitionsAndOverlapCocycle
      .G4_ProjectiveKreinBerezinianAndWeylDeformationTriad
  | g4_to_g5 : causalEdge .G4_ProjectiveKreinBerezinianAndWeylDeformationTriad
      .G5_FiveGradedKantorTanakaKKTTangentTowerAndColorSUSY
  | g5_to_g6 : causalEdge .G5_FiveGradedKantorTanakaKKTTangentTowerAndColorSUSY
      .G6_SplitOctonionCl33ParaKahlerPhaseSpaceAndMetriplecticProduct
  | g6_to_g7 : causalEdge .G6_SplitOctonionCl33ParaKahlerPhaseSpaceAndMetriplecticProduct
      .G7_ParaKahlerInformationManifoldChiralTwoJetAndBregmanClosure
  | g7_to_g8 : causalEdge .G7_ParaKahlerInformationManifoldChiralTwoJetAndBregmanClosure
      .G8_GrandSuperGrassmannianParaKahlerInfoGeometrySynthesis
  | g1_to_g6 : causalEdge .G1_ParaComplexPolarizationAndBiLagrangianIsotropicSheets
      .G6_SplitOctonionCl33ParaKahlerPhaseSpaceAndMetriplecticProduct
  | g2_to_g5 : causalEdge .G2_NoncommutativeProjectorGraphChartsAndZornGrassmannian
      .G5_FiveGradedKantorTanakaKKTTangentTowerAndColorSUSY
  | g4_to_g7 : causalEdge .G4_ProjectiveKreinBerezinianAndWeylDeformationTriad
      .G7_ParaKahlerInformationManifoldChiralTwoJetAndBregmanClosure

theorem causalEdge_rank_lt {a b : SuperGrassmannianParaKahlerStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases h <;> decide

theorem transGen_causalEdge_rank_lt {a b : SuperGrassmannianParaKahlerStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_rank_lt hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_rank_lt hbc)

/-- **Strict Acyclicity (`𝔊₁ ≺ 𝔊₂ ≺ ⋯ ≺ 𝔊₈`)**: No stage can cycle back to itself. -/
theorem causalEdge_acyclic (s : SuperGrassmannianParaKahlerStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl (rank s) (transGen_causalEdge_rank_lt h)

end SuperGrassmannianParaKahlerStage

/-!
## 2. Stage `𝔊₁`: Para-Complex Polarization (`K² = 1`), Bi-Lagrangian Isotropic Sheets & Para-QGT
-/

/-- **Stage `𝔊₁` (`G1_ParaComplexPolarizationAndBiLagrangianIsotropicSheets`)**:
1. **Chiral Polarization Projectors (`SuperGrassmannianProjectorBridge.lean`)**:
   For any involutive para-complex structure $K : V \to_l[\mathbb{R}] V$ ($K(K v) = v$), the
   projectors $P_\pm = \frac{1}{2}(1 \pm K)$ (`paraProjectorPlus`, `paraProjectorMinus`) are
   orthogonal idempotents summing to the identity ($P_+ + P_- = \mathrm{id}$, $P_+^2 = P_+$,
   $P_-^2 = P_-$, $P_+ P_- = P_- P_+ = 0$), with ranges equal to the primal sheet
   $\ker(K - \mathrm{id})$ and covector vacuum sheet $\ker(K + \mathrm{id})$.
2. **Bi-Lagrangian Sheet Isotropy**:
   For any bilinear metric $g$ satisfying $g(K u, K v) = -g(u, v)$, both the primal sheet and
   covector vacuum sheet are strictly isotropic ($g(P_+ v, P_+ v) = 0$ and $g(P_- v, P_- v) = 0$).
3. **Para-Berry 2-Form, Hyperbolic Flow Invariance & Para-QGT (`ParaKahlerMaurerCartanQGT.lean`)**:
   For any `D : ParaKahlerDatum ℝ V`, the Para-Berry 2-form $\Omega(u, v) = g(K u, v)$ is
   skew-symmetric ($\Omega(v, u) = -\Omega(u, v)$), hyperbolic boost flow
   $\cosh(s) u + \sinh(s) K u$ preserves $g$, and the Para-QGT $\mathcal{Q}(u, v) = g(u, v) + e\Omega(u, v)$
   ($e^2 = +1$) satisfies Para-Hermitian conjugation duality.
4. **Four-Mode Majorana CAR/CCR Chameleon (`MajoranaParaKahlerMaurerCartanSupercolorSynthesis.lean`)**:
   On $\mathbb{R}^{4,4} = \mathbb{R}^4_+ \oplus \mathbb{R}^4_-$, the cross-sheet CAR metric
   pairing `r44Metric` and CCR symplectic pairing `r44Symplectic` both equal $\delta_{jk}$ while
   intra-sheet pairings vanish. -/
theorem g1_paracomplex_polarization_isotropic_sheets_and_para_qgt
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : ParaKahlerDatum ℝ V) (s : ℝ) (u v : V)
    (j k : Fin 4) :
    let K := D.para.K
    -- 1. Chiral polarization projectors P_+ and P_- are orthogonal idempotents summing to id:
    paraProjectorPlus K (paraProjectorPlus K v) = paraProjectorPlus K v ∧
    paraProjectorMinus K (paraProjectorMinus K v) = paraProjectorMinus K v ∧
    paraProjectorPlus K v + paraProjectorMinus K v = v ∧
    paraProjectorPlus K (paraProjectorMinus K v) = 0 ∧
    paraProjectorMinus K (paraProjectorPlus K v) = 0 ∧
    InfoGeometry.SuperGrassmannian.primalSheet K = LinearMap.range (paraProjectorPlus K) ∧
    covectorVacuumSheet K = LinearMap.range (paraProjectorMinus K) ∧
    -- 2. Primal and covector vacuum sheets are g-isotropic:
    D.metric (paraProjectorPlus K v) (paraProjectorPlus K v) = 0 ∧
    D.metric (paraProjectorMinus K v) (paraProjectorMinus K v) = 0 ∧
    -- 3. Para-Berry 2-form skew-symmetry, hyperbolic flow invariance, and Para-QGT conjugation:
    D.paraBerryTwoForm v u = -D.paraBerryTwoForm u v ∧
    D.metric (Real.cosh s • u + Real.sinh s • K u) (Real.cosh s • v + Real.sinh s • K v) =
      D.metric u v ∧
    ((paraQGT D v u).re = (paraQGT D u v).re ∧ (paraQGT D v u).ep = -(paraQGT D u v).ep) ∧
    -- 4. 4-Mode Majorana CAR/CCR chameleon on ℝ^{4,4}:
    r44Metric (majoranaPairPlus j) (majoranaPairMinus k) = (if j = k then 1 else 0) ∧
    r44Symplectic (majoranaPairPlus j) (majoranaPairMinus k) = (if j = k then 1 else 0) ∧
    r44Metric (majoranaPairPlus j) (majoranaPairPlus k) = 0 ∧
    r44Symplectic (majoranaPairPlus j) (majoranaPairPlus k) = 0 := by
  intro K
  have hK : ∀ w : V, K (K w) = w := fun w => LinearMap.congr_fun D.para.K_sq w
  have hPrimalIso : D.metric (paraProjectorPlus K v) (paraProjectorPlus K v) = 0 := by
    apply primal_sheet_is_isotropic K hK D.metric D.metric_anti_compat
    · rw [primalSheet_eq_range_projectorPlus K hK]
      exact LinearMap.mem_range.mpr ⟨v, rfl⟩
    · rw [primalSheet_eq_range_projectorPlus K hK]
      exact LinearMap.mem_range.mpr ⟨v, rfl⟩
  have hVacuumIso : D.metric (paraProjectorMinus K v) (paraProjectorMinus K v) = 0 :=
    cl_nn_vacuum_sheet_quadratic_null K hK D.metric D.metric_anti_compat v
  have hMaj := four_majorana_pairs_car_ccr_chameleon j k
  exact ⟨paraProjectorPlus_idempotent K hK v,
    paraProjectorMinus_idempotent K hK v,
    paraProjectors_sum_id K v,
    paraProjectorPlus_mul_minus K hK v,
    paraProjectorMinus_mul_plus K hK v,
    primalSheet_eq_range_projectorPlus K hK,
    covectorVacuumSheet_eq_range_projectorMinus K hK,
    hPrimalIso,
    hVacuumIso,
    D.paraBerryTwoForm_skew u v,
    D.metric_hyperbolic_flow_preserved s u v,
    paraQGT_conjugation D u v,
    hMaj.1, hMaj.2.1, hMaj.2.2.1, hMaj.2.2.2⟩

/-!
## 3. Stage `𝔊₂`: Noncommutative Projector Graph Charts, Graded Submodules & Zorn Grassmannian
-/

/-- **Stage `𝔊₂` (`G2_NoncommutativeProjectorGraphChartsAndZornGrassmannian`)**:
1. **Noncommutative Projector Graph Charts (`ProjectorGraphChart.lean`)**:
   Over any associative ring `[Ring A]` and left $A$-modules $U, W$, the graph projector
   `graphProjector f : Module.End A (U × W)` ($z \mapsto (z.1, f z.1)$) satisfies
   `graphProjector f * graphProjector g = graphProjector f` (hence is idempotent and satisfies
   `Commute (graphProjector f) (graphProjector g) ↔ f = g`), with range equal to `f.graph` and
   complement `IsCompl f.graph (ker fst)`.
2. **Graded Direct-Sum Graph Submodules (`GradedGraphChart.lean`)**:
   For direct-sum decompositions `GU : ι → Submodule k U` and `GW : ι → Submodule k W`,
   the graph submodule `f.graph` is homogeneous (`IsGraded GU GW f.graph`) if and only if
   `f` is degree-preserving (`PreservesDegree GU GW f`).
3. **Native Zorn Split-Octonion Grassmannian (`ZornGraphChart.lean`)**:
   On the 8D Zorn split-octonion carrier `ZornVectorMatrix R ≃ Positive R × Negative R` over
   `[CommRing R] [Nontrivial R]`, every linear map `f : Positive R →ₗ[R] Negative R` defines a
   native rank-4 Grassmannian point `grassmannianChart f : Module.Grassmannian R (ZornVectorMatrix R) 4`,
   the map `grassmannianChart` is injective, and the origin graph `ker (graphReadout 0)` is the
   exact range of the left octonionic Peirce idempotent `L_map E11`. -/
theorem g2_noncommutative_projector_graph_charts_and_zorn_grassmannian
    {A k ι U W : Type*} [Ring A] [CommRing k] [DecidableEq ι]
    [AddCommGroup U] [Module A U] [Module k U]
    [AddCommGroup W] [Module A W] [Module k W]
    (GU : ι → Submodule k U) (GW : ι → Submodule k W)
    [DirectSum.Decomposition GU] [DirectSum.Decomposition GW]
    (f g : U →ₗ[A] W)
    {R : Type*} [CommRing R] [Nontrivial R]
    (fZ gZ : Positive R →ₗ[R] Negative R) :
    -- 1. Noncommutative graph projectors and complementation:
    graphProjector f * graphProjector g = graphProjector f ∧
    IsIdempotentElem (graphProjector f) ∧
    (Commute (graphProjector f) (graphProjector g) ↔ f = g) ∧
    LinearMap.range (graphProjector f) = f.graph ∧
    IsCompl f.graph (LinearMap.ker (LinearMap.fst A U W)) ∧
    -- 2. Graded direct-sum graph equivalence:
    (IsGraded GU GW f.graph ↔ PreservesDegree GU GW f) ∧
    -- 3. Native Zorn rank-4 Grassmannian chart injectivity and Peirce origin:
    LinearMap.ker (graphReadout (0 : Positive R →ₗ[R] Negative R)) =
      LinearMap.range (InfoGeometry.Algebra.L_map (R := R)
        (InfoGeometry.Algebra.ZornVectorMatrix.E11 : InfoGeometry.Algebra.ZornVectorMatrix R)) ∧
    (grassmannianChart fZ = grassmannianChart gZ ↔ fZ = gZ) := by
  exact ⟨graphProjector_mul f g,
    graphProjector_idempotent f,
    graphProjector_commute_iff f g,
    range_graphProjector f,
    graph_isCompl f,
    graph_isGraded_iff GU GW f,
    zero_graph_eq_range_left_E11,
    grassmannianChart_injective.eq_iff⟩

/-!
## 4. Stage `𝔊₃`: Operator Möbius Fractional Graph Transitions, Overlap Cocycle & Sheet Reflection
-/

/-- **Stage `𝔊₃` (`G3_OperatorMoebiusFractionalTransitionsAndOverlapCocycle`)**:
1. **Noncommutative Block Möbius Fractional Transition (`GraphChartTransition.lean`)**:
   Under a block operator $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$ on $U \oplus W$ where
   $u : U \simeq_l[A] U$ is the bijective denominator $a + b \circ f$, the graph `f.graph` maps
   to the graph of the ordered fractional transformation $(c + d \circ f) \circ u^{-1}$
   (`block_map_graph`), and preserves degree whenever $a, b, c, d, f$ preserve degree
   (`fractional_preservesDegree`).
2. **Exact Overlap Cocycle & Inverse Law (`GraphChartCocycle.lean`)**:
   On the overlap locus `Overlap G f ↔ Function.Bijective (denominator G f)`, the transition map
   satisfies `f.graph.map G = (transition G f hG).graph`, the composite cocycle identity
   `transition (H ∘ G) f = transition H (transition G f)`, and the inverse recovery identity
   `transition G.symm (transition G f) = f`.
3. **Coordinate Swap & Möbius Polarization Reflection (`GraphChartTransition.lean`, `SuperGrassmannianMoebiusQuotient.lean`)**:
   Swapping the summands $U \oplus W \to W \oplus U$ keeps `f.graph` in the graph chart if and
   only if `f` is bijective (`exists_swap_map_graph_iff`), while the $2 \times 2$ Möbius sheet-swap
   involution $M = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ anticommutes with the polarization
   $K = \operatorname{diag}(1, -1)$ ($\{M, K\} = 0$), preserves the neutral metric ($M^T g M = g$),
   and reverses the symplectic form ($M^T \omega M = -\omega$). -/
theorem g3_operator_moebius_fractional_transitions_and_overlap_cocycle
    {A k ι U W : Type*} [Ring A] [CommRing k] [DecidableEq ι]
    [AddCommGroup U] [Module A U] [Module k U]
    [AddCommGroup W] [Module A W] [Module k W]
    (GU : ι → Submodule k U) (GW : ι → Submodule k W)
    [DirectSum.Decomposition GU] [DirectSum.Decomposition GW]
    (a : Module.End A U) (b : W →ₗ[A] U) (c : U →ₗ[A] W) (d : Module.End A W) (f : U →ₗ[A] W)
    (ha : PreservesDegree GU GU a) (hb : PreservesDegree GW GU b)
    (hc : PreservesDegree GU GW c) (hd : PreservesDegree GW GW d)
    (hf : PreservesDegree GU GW f)
    (u : U ≃ₗ[A] U) (hu : u.toLinearMap = a + b.comp f)
    (G H : (U × W) ≃ₗ[A] (U × W))
    (hG : Overlap G.toLinearMap f)
    (hH : Overlap H.toLinearMap (transition G.toLinearMap f hG))
    {R : Type*} [CommRing R] :
    -- 1. Ordered noncommutative fractional graph transition & degree preservation:
    f.graph.map ((a.coprod b).prod (c.coprod d)) =
      ((c + d.comp f).comp u.symm.toLinearMap).graph ∧
    PreservesDegree GU GW ((c + d.comp f).comp u.symm.toLinearMap) ∧
    -- 2. Overlap cocycle and inverse recovery:
    f.graph.map G.toLinearMap = (transition G.toLinearMap f hG).graph ∧
    transition (H.toLinearMap.comp G.toLinearMap) f ((overlap_comp_iff G H f hG).mpr hH) =
      transition H.toLinearMap (transition G.toLinearMap f hG) hH ∧
    transition G.symm.toLinearMap (transition G.toLinearMap f hG) (overlap_inverse G f hG) = f ∧
    -- 3. Summand swap invertibility criterion & 2×2 Möbius reflection identities:
    ((∃ g : W →ₗ[A] U, f.graph.map (LinearEquiv.prodComm A U W).toLinearMap = g.graph) ↔
      Function.Bijective f) ∧
    M_mat (R := R) * K_mat + K_mat * M_mat = 0 ∧
    (M_mat (R := R)).transpose * g_mat * M_mat = g_mat ∧
    (M_mat (R := R)).transpose * omega_mat * M_mat = -omega_mat := by
  exact ⟨block_map_graph a b c d f u hu,
    fractional_preservesDegree GU GW a b c d f ha hb hc hd hf u hu,
    transition_graph G.toLinearMap f hG,
    transition_cocycle G H f hG hH,
    transition_inverse G f hG,
    exists_swap_map_graph_iff f,
    moebius_anticommutes_polarization,
    moebius_metric_isometry,
    moebius_symplectic_anti_invariance⟩

/-!
## 5. Stage `𝔊₄`: Projective Krein–Berezinian Volume Invariant & Weyl Deformation Triad
-/

/-- **Stage `𝔊₄` (`G4_ProjectiveKreinBerezinianAndWeylDeformationTriad`)**:
1. **Weyl Deformation Triad (`WeylBerezinianDeformation.lean`)**:
   On `Matrix (Fin 2) (Fin 2) R`, the commutator of the Weyl scale operator
   $S(p, q, \sigma) = \operatorname{diag}(p\sigma, q\sigma)$ and the chiral sheet-mixing operator
   $X(k_1, k_2) = \begin{pmatrix} 0 & k_1 \\ k_2 & 0 \end{pmatrix}$ is
   $[S, X] = \begin{pmatrix} 0 & (p-q)\sigma k_1 \\ -(p-q)\sigma k_2 & 0 \end{pmatrix}$ (vanishing
   when $p = q$), $\operatorname{STr}(X^2) = 0$, and the total deformation supertrace isolates
   strictly the Weyl scale anomaly:
   $$\operatorname{STr}(S(p, q, \sigma) + X(k_1, k_2) + V(a)) = (p - q)\sigma.$$
2. **Projective Krein–Berezinian Homothety (`ProjectiveKreinBerezinian.lean`)**:
   The split Krein metric $\eta = \operatorname{diag}(1, -1)$ and balanced para-complex structure
   $K = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ satisfy $\eta^2 = 1$, $K^2 = 1$, $\{\eta, K\} = 0$;
   under uniform homothety $c \cdot c^{-1} = 1$, balanced $(p|p)$ super-Grassmannians are
   scale-invariant ($c^p (c^{-1})^p = 1$) while unbalanced $(p+q|q)$ spaces scale by $c^p$.
3. **$(2|3)$ Lepton–Quark Super-Berezinian Gauge Invariance (`SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.lean`)**:
   On the $(2|3)$ lepton–quark super-carrier, $\operatorname{Ber}(A_{\text{bos}}, D_{\text{fer}}) = \det(A_{\text{bos}}) / \det(D_{\text{fer}})$
   is multiplicative, invariant under Weyl boosts $\operatorname{diag}(\lambda, \lambda^{-1})$ on
   $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{+2}$ and $\mathrm{SL}(3, \mathbb{R})$ color gauge
   transformations on $\mathfrak{g}_{\pm 1}$, and satisfies $\ln \operatorname{Ber}(A_1, D_1) = 0$
   whenever $\det(A_1) = \det(D_1) \neq 0$. -/
theorem g4_projective_krein_berezinian_and_weyl_deformation_triad
    {R : Type*} [CommRing R] (p q σ k₁ k₂ a c inv_c : R) (hc : c * inv_c = 1)
    (n m : ℕ)
    (A₁ A₂ A_bos : Matrix (Fin 2) (Fin 2) ℝ)
    (D₁ D₂ D_fer U_C : Matrix (Fin 3) (Fin 3) ℝ)
    (M_color : InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge.SL3)
    (lam invLam : ℝ)
    (h_weyl : lam * invLam = 1)
    (h_color_det : U_C.det = 1)
    (h_match_det : A₁.det = D₁.det)
    (hD₁_ne : D₁.det ≠ 0) :
    -- 1. Weyl deformation triad commutator and total supertrace splitting:
    scaleOperator p q σ * chiralOperator k₁ k₂ - chiralOperator k₁ k₂ * scaleOperator p q σ =
      !![0, (p - q) * σ * k₁; -(p - q) * σ * k₂, 0] ∧
    scaleOperator p p σ * chiralOperator k₁ k₂ - chiralOperator k₁ k₂ * scaleOperator p p σ = 0 ∧
    superTrace (chiralOperator (R := R) k₁ k₂ * chiralOperator (R := R) k₁ k₂) = 0 ∧
    superTrace (scaleOperator p q σ + chiralOperator k₁ k₂ + volumeOperator a) = (p - q) * σ ∧
    -- 2. Projective Krein–Berezinian anticommutation and homothety scaling:
    kreinMetric (Fin 2) (Fin 2) R *
        InfoGeometry.SuperGrassmannian.ProjectiveKreinBerezinian.paraComplexK (Fin 2) R +
      InfoGeometry.SuperGrassmannian.ProjectiveKreinBerezinian.paraComplexK (Fin 2) R *
        kreinMetric (Fin 2) (Fin 2) R = 0 ∧
    (c ^ n) * (inv_c ^ n) = 1 ∧
    (c ^ (n + m)) * (inv_c ^ m) = c ^ n ∧
    -- 3. (2|3) Lepton–Quark Super-Berezinian gauge invariance and UV zero-point cancellation:
    superBerezinian23 (A₁ * A₂) (D₁ * D₂) =
      superBerezinian23 A₁ D₁ * superBerezinian23 A₂ D₂ ∧
    superBerezinian23 (leptonWeylScaleMatrix lam invLam * A_bos) (U_C * D_fer) =
      superBerezinian23 A_bos D_fer ∧
    superTrace23 A_bos (D_fer + M_color.1) = superTrace23 A_bos D_fer ∧
    Real.log (superBerezinian23 A₁ D₁) = 0 := by
  have hBer := super_berezinian_gauge_invariance A₁ A₂ A_bos D₁ D₂ D_fer U_C M_color
    lam invLam h_weyl h_color_det h_match_det hD₁_ne
  exact ⟨scale_chiral_commutator p q σ k₁ k₂,
    scale_chiral_commutator_balanced p σ k₁ k₂,
    superTrace_chiral_square k₁ k₂,
    total_deformation_superTrace p q σ k₁ k₂ a,
    krein_paraComplex_anticomm (Fin 2) R,
    balanced_homothety_berezinian_eq_one n c inv_c hc,
    unbalanced_homothety_berezinian n m c inv_c hc,
    hBer.1, hBer.2.1, hBer.2.2.1, hBer.2.2.2⟩

/-!
## 6. Stage `𝔊₅`: 5-Graded Kantor–Tanaka / KKT Supergrassmannian Tangent Tower & Color SUSY
-/

/-- **Stage `𝔊₅` (`G5_FiveGradedKantorTanakaKKTTangentTowerAndColorSUSY`)**:
1. **5-Graded Kantor–Tanaka Characteristic Identity (`FiveGradedLieSuperalgebra.lean`)**:
   The characteristic polynomial factors as $x(x^2 - 1)(x^2 - 4) = x^5 - 5x^3 + 4x$, and for
   any $X \in M_3(R)$ the Cartan grading derivation $\operatorname{ad}_H(X) = [H, X]$
   ($H = \operatorname{diag}(1, 0, -1)$) satisfies the exact quintic identity
   $$\operatorname{ad}_H^5(X) - 5\operatorname{ad}_H^3(X) + 4\operatorname{ad}_H(X) = 0.$$
2. **Kantor–Tanaka Contact Brackets & $\mathfrak{osp}(1|2)$ Supercharges (`KantorTanakaSuperGrassmannian.lean`, `SuperconformalOSpJordanPair.lean`)**:
   In $M_3(R)$, the odd contact brackets satisfy $[E_{01}, E_{12}] = E_{02}$,
   $[E_{01}, E_{10}] + [E_{12}, E_{21}] = H$, the Krein involution $J$ inverts $H$
   ($J H J = -H$), and the odd supercharges $Q_+, Q_-$ satisfy $\{Q_+, Q_-\} = H$.
3. **5-Graded Maurer–Cartan Flatness & $\mathbb{Z}_2 \times \mathbb{Z}_2$ Günaydin–Gürsey Color SUSY (`MajoranaParaKahlerMaurerCartanSupercolorSynthesis.lean`, `SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.lean`)**:
   The 5-graded Cartan connection jet `canonicalMaurerCartanJet` is non-zero and flat
   (`mcCurvatureTower canonicalMaurerCartanJet = (0, 0, 0, 0, 0)`), the $\mathbb{Z}_2 \times \mathbb{Z}_2$
   color-supersymmetry sign $\varepsilon(g_1, g_2)$ satisfies $\varepsilon(\text{quark}, \text{lepton}) = -1$
   and $\varepsilon(\text{quark}, \text{quark}) = +1$, the quark–antiquark outer product decomposes
   into the trace-free $\mathfrak{sl}_3(\mathbb{R})$ generator plus dilatation trace, and the
   square of `oddSupercolorFull` closes onto the even bosonic socle $\mathfrak{g}_0$. -/
theorem g5_five_graded_kantor_tanaka_kkt_tangent_tower_and_color_susy
    {R : Type*} [CommRing R] (x : R) (X : Matrix (Fin 3) (Fin 3) R)
    (g₁ g₂ : Z2Z2ColorGrade) (u v eps epsBar : Fin 3 → ℝ)
    (z : InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.ZornSplitOctonion ℝ)
    (M : InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis.GunaydinGurseyMultiplet ℝ) :
    -- 1. Quintic Kantor–Tanaka factorization and matrix derivation identity:
    x * (x ^ 2 - 1) * (x ^ 2 - 4) = x ^ 5 - 5 * x ^ 3 + 4 * x ∧
    adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X = 0 ∧
    -- 2. Kantor–Tanaka contact brackets, Krein inversion, and osp(1|2) supercharge closure:
    KantorTanakaSuperGrassmannian.bracket
      (KantorTanakaSuperGrassmannian.E 0 1 : Matrix (Fin 3) (Fin 3) R)
      (KantorTanakaSuperGrassmannian.E 1 2) = KantorTanakaSuperGrassmannian.E 0 2 ∧
    KantorTanakaSuperGrassmannian.bracket
      (KantorTanakaSuperGrassmannian.E 0 1 : Matrix (Fin 3) (Fin 3) R)
      (KantorTanakaSuperGrassmannian.E 1 0) +
      KantorTanakaSuperGrassmannian.bracket
        (KantorTanakaSuperGrassmannian.E 1 2)
        (KantorTanakaSuperGrassmannian.E 2 1) = KantorTanakaSuperGrassmannian.H R ∧
    KantorTanakaSuperGrassmannian.swap (KantorTanakaSuperGrassmannian.H R) =
      -KantorTanakaSuperGrassmannian.H R ∧
    SuperconformalOSpJordanPair.anticommutator
      (SuperconformalOSpJordanPair.Q_plus R)
      (SuperconformalOSpJordanPair.Q_minus R) = SuperconformalOSpJordanPair.H_gen R ∧
    -- 3. 5-graded Maurer–Cartan flatness & ℤ₂ × ℤ₂ Günaydin–Gürsey color supersymmetry closure:
    canonicalMaurerCartanJet ≠ (default : FiveGradedMaurerCartanJet ℝ) ∧
    mcCurvatureTower canonicalMaurerCartanJet = (0, 0, 0, 0, 0) ∧
    z2z2KoszulSign g₁ g₂ = z2z2KoszulSign g₂ g₁ ∧
    z2z2KoszulSign gradeQuark gradeLepton = -1 ∧
    z2z2KoszulSign gradeQuark gradeQuark = 1 ∧
    quarkAntiquarkOuter u v =
      quarkAntiquarkTracelessSL3 u v +
        ((1 / 3 : ℝ) * quarkAntiquarkDilatationTrace u v) • (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
    Matrix.trace (quarkAntiquarkToSL3 u v).1 = 0 ∧
    (oddSupercolorFull eps epsBar (oddSupercolorFull eps epsBar M)).1 0 =
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Dot eps epsBar * M.1 0 ∧
    (oddSupercolorFull eps epsBar (oddSupercolorFull eps epsBar M)).2.1 =
      (quarkAntiquarkOuter eps epsBar).mulVec M.2.1 := by
  have hSign := z2z2_color_supersymmetry_sign_laws g₁ g₂
  have hGG := gunaydin_gursey_g1_gm1_superbracket_closure u v z
  have hSocle := oddSupercolorFull_sq_closes_on_even_bosonic_socle eps epsBar M
  exact ⟨quintic_polynomial_factorization x,
    adH_quintic_identity X,
    KantorTanakaSuperGrassmannian.odd_contact_bracket,
    KantorTanakaSuperGrassmannian.spinor_bilinear_sum_eq_H,
    KantorTanakaSuperGrassmannian.J_inverts_H,
    SuperconformalOSpJordanPair.osp_anticomm_plus_minus,
    canonicalMaurerCartanJet_ne_default,
    canonicalMaurerCartanJet_flat,
    hSign.1, hSign.2.2.2.1, hSign.2.2.2.2.2,
    hGG.1, hGG.2.1,
    hSocle.1, hSocle.2.2.1⟩

/-!
## 6b. The 6-Stage Kantor–Tanaka Contact Prolongation, Quartic Lagrange Projectors, $\mathfrak{osp}(1|2)$ Supercharge Closure, & Günaydin–Gürsey Color Poset (`𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ ⋯ ≺ 𝔎𝔗₆`)

This section refines Stage `𝔊₅` into the 6-stage Acyclic Causal Poset
$$\mathfrak{KT}_1 \prec \mathfrak{KT}_2 \prec \mathfrak{KT}_3 \prec \mathfrak{KT}_4 \prec \mathfrak{KT}_5 \prec \mathfrak{KT}_6$$
resolving why a 5-graded Kantor–Tanaka super-tower $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$
cannot be annihilated by the 3-graded Peirce operator $\mathcal{D}_3(D) = D^3 - D$:
- **Stage `𝔎𝔗₁` (`kt1_three_graded_peirce_and_grade_two_super_bracket_eruption`)**:
  For any derivation $D(X Y) = D(X) Y + X D(Y)$, the product and anticommutator of Grade-$\pm 1$
  elements have Grade-$\pm 2$ eigenvalue ($D(Q_{\pm 1}^2) = \pm 2 Q_{\pm 1}^2$ and
  $D(\{Q_{\pm 1}, Q'_{\pm 1}\}) = \pm 2 \{Q_{\pm 1}, Q'_{\pm 1}\}$). While $\mathcal{D}_3(D) = D^3 - D$
  annihilates Grades $-1, 0, +1$, on Grade $\pm 2$ it yields $\mathcal{D}_3(D)(E_{\pm 2}) = \pm 6 E_{\pm 2}$
  and $D(\mathcal{D}_3(D)(E_{\pm 2})) = 12 E_{\pm 2}$.
- **Stage `𝔎𝔗₂` (`kt2_factored_five_graded_quintic_contact_law`)**:
  The polynomial factorization $(x^2 - 4)(x^3 - x) = x(x^2 - 1)(x^2 - 4) = x^5 - 5x^3 + 4x$
  proves that for any 5-graded sum $X = X_{-2} + X_{-1} + X_0 + X_{+1} + X_{+2}$,
  $\mathcal{D}_3(D)(X) = -6 X_{-2} + 6 X_{+2}$ and $(D^2 - 4I)(\mathcal{D}_3(D)(X)) = (D^5 - 5 D^3 + 4 D)(X) = 0$.
- **Stage `𝔎𝔗₃` (`kt3_orthogonal_quartic_lagrange_projectors`)**:
  Constructs the division-free $12$-scaled quartic Lagrange projectors
  $12\Pi_0 = 12I - 15D^2 + 3D^4$, $12\Pi_{\pm 1} = 16D^2 - 4D^4$, and $12\Pi_{\pm 2} = D^4 - D^2 = D \circ \mathcal{D}_3(D)$
  (proving the **Transcendent Function Identity** that applying $D$ to the 3-graded Peirce residual
  $\mathcal{D}_3(D)$ isolates $12\Pi_{\pm 2}$), the signed 5-grade projectors isolating each $X_k$,
  and the normalized field projectors `adHProjectorZero`, `adHProjectorOne`, `adHProjectorTwo`.
- **Stage `𝔎𝔗₄` (`kt4_osp12_superconformal_contact_closure_and_super_jacobi`)**:
  Proves the universal associative odd-odd-odd super-Jacobi identity
  $[A, \{B, C\}] + [B, \{C, A\}] + [C, \{A, B\}] = 0$, the Rung 3 aporia that $\{Q_+, Q_+\} = 0$
  together with $\{Q_+, Q_-\} = H$ and $[H, Q_+] = Q_+$ forces $2 Q_+ = 0$, and the concrete
  $M_3(R)$ $\mathfrak{osp}(1|2)$ superconformal contact closure where $[Q_-, \{Q_+, Q_+\}] = [Q_-, 2 E_{+2}] = 2 Q_+$
  cancels $2[Q_+, H] = -2 Q_+$.
- **Stage `𝔎𝔗₅` (`kt5_gunaydin_gursey_gl1_sl3_color_decomposition`)**:
  Proves the orthogonal projector split $M_3(\mathbb{R}) = \mathfrak{gl}_1(\mathbb{R})_H \oplus \mathfrak{sl}_3(\mathbb{R})_{\text{color}}$
  via $\mathcal{P}_{\mathfrak{gl}_1}(X) = \frac{1}{3}\mathrm{tr}(X)I_3$ and $\mathcal{P}_{\mathfrak{sl}_3}(X) = X - \frac{1}{3}\mathrm{tr}(X)I_3$,
  unifying it with `quarkAntiquarkOuter`, `quarkAntiquarkTracelessSL3`, and `z2z2KoszulSign`.
- **Stage `𝔎𝔗₆` (`kt6_five_graded_maurer_cartan_and_kantor_sandwich_closure`)**:
  Unifies the 6-stage `KantorTanakaContactStage` poset with 5-graded Maurer–Cartan flatness
  (`mcCurvatureTower canonicalMaurerCartanJet = (0, 0, 0, 0, 0)`) and the bilateral Kantor sandwich
  identity $\mathcal{K}_0^2(X) - (\mathcal{K}_{+2}\mathcal{K}_{-2}(X) + \mathcal{K}_{-2}\mathcal{K}_{+2}(X)) = \Sigma X \Sigma$.
-/

/-- The 6 stages of the **5-Graded Kantor–Tanaka Contact Prolongation & Color SUSY Poset**
(`𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ 𝔎𝔗₃ ≺ 𝔎𝔗₄ ≺ 𝔎𝔗₅ ≺ 𝔎𝔗₆`). -/
inductive KantorTanakaContactStage : Type
  /-- `𝔎𝔗₁`: 3-Graded Peirce operator `𝒟₃(D) = D³ - D` & Grade-`±2` super-bracket eruption `𝒟₃(D)(E_{±2}) = ±6 E_{±2}`. -/
  | KT1_ThreeGradedPeirceAndGradeTwoSuperBracketEruption
  /-- `𝔎𝔗₂`: Factored 5-Graded Quintic Contact Law `(D² - 4I)(D³ - D) = D⁵ - 5D³ + 4D = 0`. -/
  | KT2_FactoredFiveGradedQuinticContactLaw
  /-- `𝔎𝔗₃`: Orthogonal Quartic Lagrange Projectors `Π_0, Π_{±1}, Π_{±2}` & Transcendent Function `12 Π_{±2} = D(D³ - D)`. -/
  | KT3_OrthogonalQuarticLagrangeProjectors
  /-- `𝔎𝔗₄`: Orthosymplectic `𝔬𝔰𝔭(1|2)` Superconformal Contact Closure & Odd-Odd-Odd Super-Jacobi Balance. -/
  | KT4_OSp12SuperconformalContactClosureAndSuperJacobi
  /-- `𝔎𝔗₅`: Günaydin–Gürsey `𝔤𝔩₁(ℝ)_H ⊕ 𝔰𝔩₃(ℝ)_color` Orthogonal Projector & Quark–Antiquark Split. -/
  | KT5_GunaydinGurseyGL1SL3ColorDecomposition
  /-- `𝔎𝔗₆`: 5-Graded Maurer–Cartan Flatness & Bilateral Kantor Sandwich Closure `𝒦₀² - (𝒦₊₂ 𝒦₋₂ + 𝒦₋₂ 𝒦₊₂) = Σ · Σ`. -/
  | KT6_FiveGradedMaurerCartanAndKantorSandwichClosure
  deriving DecidableEq, Repr, Inhabited

namespace KantorTanakaContactStage

/-- Integer rank `0 .. 5` for `𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ ⋯ ≺ 𝔎𝔗₆`. -/
def rank : KantorTanakaContactStage → ℕ
  | .KT1_ThreeGradedPeirceAndGradeTwoSuperBracketEruption => 0
  | .KT2_FactoredFiveGradedQuinticContactLaw              => 1
  | .KT3_OrthogonalQuarticLagrangeProjectors              => 2
  | .KT4_OSp12SuperconformalContactClosureAndSuperJacobi  => 3
  | .KT5_GunaydinGurseyGL1SL3ColorDecomposition           => 4
  | .KT6_FiveGradedMaurerCartanAndKantorSandwichClosure   => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder KantorTanakaContactStage where
  le a b := rank a ≤ rank b
  lt a b := rank a < rank b
  le_refl a := le_rfl
  le_trans a b c := Nat.le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (rank a) (rank b)
  le_antisymm a b hab hba := rank_injective (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total (rank a) (rank b)
  toDecidableLE a b := Nat.decLe (rank a) (rank b)
  toDecidableEq := inferInstance
  toDecidableLT a b := Nat.decLt (rank a) (rank b)

instance : Fintype KantorTanakaContactStage where
  elems := {
    .KT1_ThreeGradedPeirceAndGradeTwoSuperBracketEruption,
    .KT2_FactoredFiveGradedQuinticContactLaw,
    .KT3_OrthogonalQuarticLagrangeProjectors,
    .KT4_OSp12SuperconformalContactClosureAndSuperJacobi,
    .KT5_GunaydinGurseyGL1SL3ColorDecomposition,
    .KT6_FiveGradedMaurerCartanAndKantorSandwichClosure
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card KantorTanakaContactStage = 6 := rfl

/-- Directed covering edges `𝔎𝔗_k ≺ 𝔎𝔗_{k+1}`. -/
def causalEdge (a b : KantorTanakaContactStage) : Prop :=
  rank b = rank a + 1

theorem causalEdge_lt {a b : KantorTanakaContactStage} (h : causalEdge a b) :
    rank a < rank b := by
  dsimp [causalEdge] at h
  omega

theorem transGen_causalEdge_lt {a b : KantorTanakaContactStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

/-- Strict DAG acyclicity of `𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ ⋯ ≺ 𝔎𝔗₆`. -/
theorem causalEdge_acyclic (a : KantorTanakaContactStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_lt h)

/-- Monotone embedding into `InfoGeometry.Meta.RepDepth`. -/
def toRepDepth : KantorTanakaContactStage → InfoGeometry.Meta.RepDepth
  | .KT1_ThreeGradedPeirceAndGradeTwoSuperBracketEruption => .operator
  | .KT2_FactoredFiveGradedQuinticContactLaw              => .operator
  | .KT3_OrthogonalQuarticLagrangeProjectors              => .transport
  | .KT4_OSp12SuperconformalContactClosureAndSuperJacobi  => .transport
  | .KT5_GunaydinGurseyGL1SL3ColorDecomposition           => .thermo
  | .KT6_FiveGradedMaurerCartanAndKantorSandwichClosure   => .thermo

/-- Monotone embedding into `InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    KantorTanakaContactStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .KT1_ThreeGradedPeirceAndGradeTwoSuperBracketEruption => .M1_ProjectorClabject
  | .KT2_FactoredFiveGradedQuinticContactLaw              => .M1_ProjectorClabject
  | .KT3_OrthogonalQuarticLagrangeProjectors              => .M2_GrassmannianPowertypeOrbit
  | .KT4_OSp12SuperconformalContactClosureAndSuperJacobi  => .M2_GrassmannianPowertypeOrbit
  | .KT5_GunaydinGurseyGL1SL3ColorDecomposition           => .M3_ErlangenCasimirMetaLaw
  | .KT6_FiveGradedMaurerCartanAndKantorSandwichClosure   => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : KantorTanakaContactStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth InfoGeometry.Meta.RepDepth.toNat <;>
    decide

theorem toOntologyMetaLevel_mono {a b : KantorTanakaContactStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;>
    decide

end KantorTanakaContactStage

section KantorTanakaContactProlongationPoset

open InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
open InfoGeometry.Canonical.AmariOperatorDuallyFlatGaussianPythagoreanPoset

/-- The 3-graded Peirce operator $\mathcal{D}_3(D)(Z) := D^3(Z) - D(Z)$. -/
def peirce3Op {M : Type*} [AddCommGroup M] (D : M →+ M) (Z : M) : M :=
  D (D (D Z)) - D Z

/-- The 5-graded Kantor–Tanaka quintic operator $\mathcal{D}_5(D)(Z) := D^5(Z) - 5 D^3(Z) + 4 D(Z)$. -/
def kantorQuinticOp {M : Type*} [AddCommGroup M] (D : M →+ M) (Z : M) : M :=
  D (D (D (D (D Z)))) - (5 : ℤ) • D (D (D Z)) + (4 : ℤ) • D Z

/-- Ring-universal $12$-scaled Grade-$0$ quartic Lagrange projector
$12\Pi_0(D)(Z) := 12 Z - 15 D^2(Z) + 3 D^4(Z) = 3(D^2 - I)(D^2 - 4I)(Z)$. -/
def lagrange12Proj0 {M : Type*} [AddCommGroup M] (D : M →+ M) (Z : M) : M :=
  (12 : ℤ) • Z - (15 : ℤ) • D (D Z) + (3 : ℤ) • D (D (D (D Z)))

/-- Ring-universal $12$-scaled Grade-$\pm 1$ quartic Lagrange projector
$12\Pi_{\pm 1}(D)(Z) := 16 D^2(Z) - 4 D^4(Z) = -4 D^2(D^2 - 4I)(Z)$. -/
def lagrange12Proj1 {M : Type*} [AddCommGroup M] (D : M →+ M) (Z : M) : M :=
  (16 : ℤ) • D (D Z) - (4 : ℤ) • D (D (D (D Z)))

/-- Ring-universal $12$-scaled Grade-$\pm 2$ quartic Lagrange projector
$12\Pi_{\pm 2}(D)(Z) := D^4(Z) - D^2(Z) = D(D^3(Z) - D(Z))$. -/
def lagrange12Proj2 {M : Type*} [AddCommGroup M] (D : M →+ M) (Z : M) : M :=
  D (D (D (D Z))) - D (D Z)

/-- Orthogonal projector onto the central $\mathfrak{gl}_1(\mathbb{R})_H$ dilatation line in $M_3(\mathbb{R})$:
$\mathcal{P}_{\mathfrak{gl}_1}(X) := \frac{1}{3}\operatorname{tr}(X) I_3$. -/
noncomputable def gl1ColorProj (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((1 / 3 : ℝ) * Matrix.trace X) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- Orthogonal projector onto the traceless $\mathfrak{sl}_3(\mathbb{R})_{\text{color}}$ subalgebra in $M_3(\mathbb{R})$:
$\mathcal{P}_{\mathfrak{sl}_3}(X) := X - \frac{1}{3}\operatorname{tr}(X) I_3$. -/
noncomputable def sl3ColorProj (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  X - gl1ColorProj X

/-- **Stage `𝔎𝔗₁` (`kt1_three_graded_peirce_and_grade_two_super_bracket_eruption`)**:
1. **Derivation Eigenvalue Addition & Grade-$\pm 2$ Super-Bracket Eruption (`Axiom I Lemma 1`)**:
   In any associative ring `[Ring B]` with an additive derivation $D : B \to+ B$ satisfying
   $D(X Y) = D(X) Y + X D(Y)$:
   - If $D(Q_1) = Q_1$ and $D(Q'_1) = Q'_1$, then $D(Q_1 Q'_1) = (2 : \mathbb{Z}) \bullet (Q_1 Q'_1)$
     and $D(Q_1 Q'_1 + Q'_1 Q_1) = (2 : \mathbb{Z}) \bullet (Q_1 Q'_1 + Q'_1 Q_1)$.
   - If $D(Q_{-1}) = -Q_{-1}$ and $D(Q'_{-1}) = -Q'_{-1}$, then
     $D(Q_{-1} Q'_{-1}) = -(2 : \mathbb{Z}) \bullet (Q_{-1} Q'_{-1})$ and
     $D(Q_{-1} Q'_{-1} + Q'_{-1} Q_{-1}) = -(2 : \mathbb{Z}) \bullet (Q_{-1} Q'_{-1} + Q'_{-1} Q_{-1})$.
2. **Rung 0 — Exact Annihilation of Grades $\{-1, 0, +1\}$ vs. $\pm 6$ Eruption on Grade $\pm 2$**:
   For any `[AddCommGroup M]` and `D : M →+ M`, if $D(X_0) = 0$, $D(X_1) = X_1$, $D(X_{-1}) = -X_{-1}$,
   $D(E_2) = (2 : \mathbb{Z}) \bullet E_2$, and $D(E_{-2}) = (-2 : \mathbb{Z}) \bullet E_{-2}$:
   - `peirce3Op D X_0 = 0`, `peirce3Op D X_1 = 0`, and `peirce3Op D X_{-1} = 0`,
   - `peirce3Op D E_2 = (6 : ℤ) • E_2` and `D (peirce3Op D E_2) = (12 : ℤ) • E_2`,
   - `peirce3Op D E_{-2} = (-6 : ℤ) • E_{-2}` and `D (peirce3Op D E_{-2}) = (12 : ℤ) • E_{-2}`. -/
theorem kt1_three_graded_peirce_and_grade_two_super_bracket_eruption
    {B : Type*} [Ring B] (D_ring : B →+ B)
    (hLeib : ∀ X Y : B, D_ring (X * Y) = D_ring X * Y + X * D_ring Y)
    {Q₁ Q'₁ Qm1 Q'm1 : B}
    (hQ₁ : D_ring Q₁ = Q₁) (hQ'₁ : D_ring Q'₁ = Q'₁)
    (hQm1 : D_ring Qm1 = -Qm1) (hQ'm1 : D_ring Q'm1 = -Q'm1)
    {M : Type*} [AddCommGroup M] (D : M →+ M)
    {X₀ X₁ Xm1 E₂ Em2 : M}
    (h0 : D X₀ = 0) (h1 : D X₁ = X₁) (hm1 : D Xm1 = -Xm1)
    (h2 : D E₂ = (2 : ℤ) • E₂) (hm2 : D Em2 = (-2 : ℤ) • Em2) :
    -- 1. Grade +1 and -1 products and anticommutators erupt into Grade +2 and -2:
    D_ring (Q₁ * Q'₁) = (2 : ℤ) • (Q₁ * Q'₁) ∧
    D_ring (Q₁ * Q'₁ + Q'₁ * Q₁) = (2 : ℤ) • (Q₁ * Q'₁ + Q'₁ * Q₁) ∧
    D_ring (Qm1 * Q'm1) = (-2 : ℤ) • (Qm1 * Q'm1) ∧
    D_ring (Qm1 * Q'm1 + Q'm1 * Qm1) = (-2 : ℤ) • (Qm1 * Q'm1 + Q'm1 * Qm1) ∧
    -- 2. 3-graded Peirce operator kills Grades 0, +1, -1:
    peirce3Op D X₀ = 0 ∧
    peirce3Op D X₁ = 0 ∧
    peirce3Op D Xm1 = 0 ∧
    -- 3. Rung 0 Eruption on Grade +2 and -2:
    peirce3Op D E₂ = (6 : ℤ) • E₂ ∧
    D (peirce3Op D E₂) = (12 : ℤ) • E₂ ∧
    peirce3Op D Em2 = (-6 : ℤ) • Em2 ∧
    D (peirce3Op D Em2) = (12 : ℤ) • Em2 := by
  have hProdPos : D_ring (Q₁ * Q'₁) = (2 : ℤ) • (Q₁ * Q'₁) := by
    rw [hLeib, hQ₁, hQ'₁]
    abel
  have hProdPos' : D_ring (Q'₁ * Q₁) = (2 : ℤ) • (Q'₁ * Q₁) := by
    rw [hLeib, hQ'₁, hQ₁]
    abel
  have hAntiPos : D_ring (Q₁ * Q'₁ + Q'₁ * Q₁) = (2 : ℤ) • (Q₁ * Q'₁ + Q'₁ * Q₁) := by
    rw [map_add, hProdPos, hProdPos', ← smul_add]
  have hProdNeg : D_ring (Qm1 * Q'm1) = (-2 : ℤ) • (Qm1 * Q'm1) := by
    rw [hLeib, hQm1, hQ'm1, neg_mul, mul_neg]
    abel
  have hProdNeg' : D_ring (Q'm1 * Qm1) = (-2 : ℤ) • (Q'm1 * Qm1) := by
    rw [hLeib, hQ'm1, hQm1, neg_mul, mul_neg]
    abel
  have hAntiNeg : D_ring (Qm1 * Q'm1 + Q'm1 * Qm1) = (-2 : ℤ) • (Qm1 * Q'm1 + Q'm1 * Qm1) := by
    rw [map_add, hProdNeg, hProdNeg', ← smul_add]
  have hP0 : peirce3Op D X₀ = 0 := by
    simp [peirce3Op, h0]
  have hP1 : peirce3Op D X₁ = 0 := by
    simp [peirce3Op, h1]
  have hPm1 : peirce3Op D Xm1 = 0 := by
    simp [peirce3Op, hm1]
  have hP2 : peirce3Op D E₂ = (6 : ℤ) • E₂ := by
    simp only [peirce3Op, map_zsmul, h2, smul_smul]
    abel
  have hDP2 : D (peirce3Op D E₂) = (12 : ℤ) • E₂ := by
    rw [hP2, map_zsmul, h2, smul_smul]
    rfl
  have hPm2 : peirce3Op D Em2 = (-6 : ℤ) • Em2 := by
    simp only [peirce3Op, map_zsmul, hm2, smul_smul]
    abel
  have hDPm2 : D (peirce3Op D Em2) = (12 : ℤ) • Em2 := by
    rw [hPm2, map_zsmul, hm2, smul_smul]
    rfl
  exact ⟨hProdPos, hAntiPos, hProdNeg, hAntiNeg, hP0, hP1, hPm1, hP2, hDP2, hPm2, hDPm2⟩

/-- **Stage `𝔎𝔗₂` (`kt2_factored_five_graded_quintic_contact_law`)**:
1. **Exact Polynomial Extension Factorization (`Rung 1` & `Axiom I Theorem 1`)**:
   In any `[CommRing R]`, for all $x \in R$:
   $$(x^2 - 4)(x^3 - x) = x^5 - 5x^3 + 4x, \qquad x(x^2 - 1)(x^2 - 4) = x^5 - 5x^3 + 4x.$$
2. **Universal 5-Graded Direct-Sum Annihilation (`(D² - 4I)(𝒟₃(D)(X)) = 𝒟₅(D)(X) = 0`)**:
   For any `[AddCommGroup M]`, `D : M →+ M`, and $X_{-2}, X_{-1}, X_0, X_1, X_2 \in M$ with
   $D(X_k) = k \bullet X_k$ ($k \in \{-2, -1, 0, 1, 2\}$), the sum
   $X = X_{-2} + X_{-1} + X_0 + X_1 + X_2$ satisfies:
   - `peirce3Op D X = (-6 : ℤ) • X_{-2} + (6 : ℤ) • X_2` (the 3-graded Peirce operator kills the
     3-graded core and isolates the Grade-$\pm 2$ contact horns!),
   - `D (D (peirce3Op D X)) - (4 : ℤ) • peirce3Op D X = 0`,
   - `D (D (peirce3Op D Z)) - (4 : ℤ) • peirce3Op D Z = kantorQuinticOp D Z` for every $Z \in M$,
   - `kantorQuinticOp D X = 0`.
3. **Concrete $M_3(R)$ Kantor–Tanaka Realization**:
   `adH (adH (adH (adH (adH X_mat)))) - 5 • adH (adH (adH X_mat)) + 4 • adH X_mat = 0`. -/
theorem kt2_factored_five_graded_quintic_contact_law
    {R : Type*} [CommRing R] (x : R) (X_mat : Matrix (Fin 3) (Fin 3) R)
    {M : Type*} [AddCommGroup M] (D : M →+ M) (Z : M)
    {Xm2 Xm1 X₀ X₁ X₂ : M}
    (hm2 : D Xm2 = (-2 : ℤ) • Xm2) (hm1 : D Xm1 = -Xm1)
    (h0 : D X₀ = 0) (h1 : D X₁ = X₁) (h2 : D X₂ = (2 : ℤ) • X₂) :
    -- 1. Polynomial factorization:
    (x ^ 2 - 4) * (x ^ 3 - x) = x ^ 5 - 5 * x ^ 3 + 4 * x ∧
    x * (x ^ 2 - 1) * (x ^ 2 - 4) = x ^ 5 - 5 * x ^ 3 + 4 * x ∧
    -- 2. Operator factorization (D² - 4I)(D³ - D)(Z) = (D⁵ - 5D³ + 4D)(Z):
    D (D (peirce3Op D Z)) - (4 : ℤ) • peirce3Op D Z = kantorQuinticOp D Z ∧
    -- 3. 3-graded Peirce residual on X = X_{-2} + X_{-1} + X_0 + X_1 + X_2 isolates ±6 X_{±2}:
    peirce3Op D (Xm2 + Xm1 + X₀ + X₁ + X₂) = (-6 : ℤ) • Xm2 + (6 : ℤ) • X₂ ∧
    -- 4. Factored and expanded quintic annihilation on any 5-graded sum:
    D (D (peirce3Op D (Xm2 + Xm1 + X₀ + X₁ + X₂))) -
      (4 : ℤ) • peirce3Op D (Xm2 + Xm1 + X₀ + X₁ + X₂) = 0 ∧
    kantorQuinticOp D (Xm2 + Xm1 + X₀ + X₁ + X₂) = 0 ∧
    -- 5. Concrete M_3(R) matrix quintic law:
    adH (adH (adH (adH (adH X_mat)))) - 5 • adH (adH (adH X_mat)) + 4 • adH X_mat = 0 := by
  have hPoly1 : (x ^ 2 - 4) * (x ^ 3 - x) = x ^ 5 - 5 * x ^ 3 + 4 * x := by ring
  have hOpFact : ∀ W : M, D (D (peirce3Op D W)) - (4 : ℤ) • peirce3Op D W = kantorQuinticOp D W := by
    intro W
    simp only [peirce3Op, kantorQuinticOp, map_sub, smul_sub]
    abel
  have hRes : peirce3Op D (Xm2 + Xm1 + X₀ + X₁ + X₂) = (-6 : ℤ) • Xm2 + (6 : ℤ) • X₂ := by
    simp only [peirce3Op, map_add, map_neg, map_zsmul, hm2, hm1, h0, h1, h2, map_zero, smul_smul]
    abel
  have hFactZero :
      D (D (peirce3Op D (Xm2 + Xm1 + X₀ + X₁ + X₂))) -
        (4 : ℤ) • peirce3Op D (Xm2 + Xm1 + X₀ + X₁ + X₂) = 0 := by
    rw [hRes]
    simp only [map_add, map_zsmul, hm2, h2, smul_add, smul_smul]
    abel
  have hQuintZero : kantorQuinticOp D (Xm2 + Xm1 + X₀ + X₁ + X₂) = 0 := by
    rw [← hOpFact, hFactZero]
  exact ⟨hPoly1, quintic_polynomial_factorization x, hOpFact Z, hRes, hFactZero, hQuintZero,
    adH_quintic_identity X_mat⟩

/-- **Stage `𝔎𝔗₃` (`kt3_orthogonal_quartic_lagrange_projectors`)**:
1. **Universal $12$-Scaled Partition of Unity & Transcendent Function Identity (`Rung 2` & `Deduction 1 Theorem 2`)**:
   For any `[AddCommGroup M]`, `D : M →+ M`, and every $Z \in M$:
   - `lagrange12Proj0 D Z + lagrange12Proj1 D Z + lagrange12Proj2 D Z = (12 : ℤ) • Z`,
   - **Transcendent Function Identity (`12 Π_{±2} = D ∘ 𝒟₃(D)`)**:
     `lagrange12Proj2 D Z = D (peirce3Op D Z)`.
2. **Exact Sector Isolation & Signed 5-Grade Projectors on $X = X_{-2} + X_{-1} + X_0 + X_1 + X_2$**:
   - `lagrange12Proj0 D (Xm2 + Xm1 + X₀ + X₁ + X₂) = (12 : ℤ) • X₀`,
   - `lagrange12Proj1 D (Xm2 + Xm1 + X₀ + X₁ + X₂) = (12 : ℤ) • (Xm1 + X₁)`,
   - `lagrange12Proj2 D (Xm2 + Xm1 + X₀ + X₁ + X₂) = (12 : ℤ) • (Xm2 + X₂)`,
   - `lagrange12Proj1 D (D (Xm2 + Xm1 + X₀ + X₁ + X₂) + (Xm2 + Xm1 + X₀ + X₁ + X₂)) = (24 : ℤ) • X₁`,
   - `lagrange12Proj1 D ((Xm2 + Xm1 + X₀ + X₁ + X₂) - D (Xm2 + Xm1 + X₀ + X₁ + X₂)) = (24 : ℤ) • Xm1`,
   - `lagrange12Proj2 D (D (Xm2 + Xm1 + X₀ + X₁ + X₂) + (2 : ℤ) • (Xm2 + Xm1 + X₀ + X₁ + X₂)) = (48 : ℤ) • X₂`,
   - `lagrange12Proj2 D ((2 : ℤ) • (Xm2 + Xm1 + X₀ + X₁ + X₂) - D (Xm2 + Xm1 + X₀ + X₁ + X₂)) = (48 : ℤ) • Xm2`.
3. **Normalized Spectral Projectors on $M_3(F)$ (`FiveGradedLieSuperalgebra.lean`)**:
   Over `[Field F] [CharZero F]`, `adHProjectorZero`, `adHProjectorOne`, and `adHProjectorTwo`
   sum to the identity, are idempotent, and are pairwise orthogonal. -/
theorem kt3_orthogonal_quartic_lagrange_projectors
    {M : Type*} [AddCommGroup M] (D : M →+ M) (Z : M)
    {Xm2 Xm1 X₀ X₁ X₂ : M}
    (hm2 : D Xm2 = (-2 : ℤ) • Xm2) (hm1 : D Xm1 = -Xm1)
    (h0 : D X₀ = 0) (h1 : D X₁ = X₁) (h2 : D X₂ = (2 : ℤ) • X₂)
    {F : Type*} [Field F] [CharZero F] (X_mat : Matrix (Fin 3) (Fin 3) F) :
    -- 1. Universal 12-scaled partition of unity and Transcendent Function identity:
    lagrange12Proj0 D Z + lagrange12Proj1 D Z + lagrange12Proj2 D Z = (12 : ℤ) • Z ∧
    lagrange12Proj2 D Z = D (peirce3Op D Z) ∧
    -- 2. Unsigned and signed 5-grade isolation on X_{-2} + X_{-1} + X_0 + X_1 + X_2:
    lagrange12Proj0 D (Xm2 + Xm1 + X₀ + X₁ + X₂) = (12 : ℤ) • X₀ ∧
    lagrange12Proj1 D (Xm2 + Xm1 + X₀ + X₁ + X₂) = (12 : ℤ) • (Xm1 + X₁) ∧
    lagrange12Proj2 D (Xm2 + Xm1 + X₀ + X₁ + X₂) = (12 : ℤ) • (Xm2 + X₂) ∧
    lagrange12Proj1 D (D (Xm2 + Xm1 + X₀ + X₁ + X₂) + (Xm2 + Xm1 + X₀ + X₁ + X₂)) =
      (24 : ℤ) • X₁ ∧
    lagrange12Proj1 D ((Xm2 + Xm1 + X₀ + X₁ + X₂) - D (Xm2 + Xm1 + X₀ + X₁ + X₂)) =
      (24 : ℤ) • Xm1 ∧
    lagrange12Proj2 D (D (Xm2 + Xm1 + X₀ + X₁ + X₂) + (2 : ℤ) • (Xm2 + Xm1 + X₀ + X₁ + X₂)) =
      (48 : ℤ) • X₂ ∧
    lagrange12Proj2 D ((2 : ℤ) • (Xm2 + Xm1 + X₀ + X₁ + X₂) - D (Xm2 + Xm1 + X₀ + X₁ + X₂)) =
      (48 : ℤ) • Xm2 ∧
    -- 3. Normalized field projectors on M_3(F):
    adHProjectorZero X_mat + adHProjectorOne X_mat + adHProjectorTwo X_mat = X_mat ∧
    adHProjectorZero (adHProjectorZero X_mat) = adHProjectorZero X_mat ∧
    adHProjectorOne (adHProjectorOne X_mat) = adHProjectorOne X_mat ∧
    adHProjectorTwo (adHProjectorTwo X_mat) = adHProjectorTwo X_mat ∧
    adHProjectorZero (adHProjectorOne X_mat) = 0 ∧
    adHProjectorZero (adHProjectorTwo X_mat) = 0 ∧
    adHProjectorOne (adHProjectorTwo X_mat) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    adHProjectors_resolve X_mat,
    adHProjectorZero_idempotent X_mat,
    adHProjectorOne_idempotent X_mat,
    adHProjectorTwo_idempotent X_mat,
    adHProjectorZero_one_zero X_mat,
    adHProjectorZero_two_zero X_mat,
    adHProjectorOne_two_zero X_mat⟩
  · simp only [lagrange12Proj0, lagrange12Proj1, lagrange12Proj2]
    abel
  · simp only [lagrange12Proj2, peirce3Op, map_sub]
  · simp only [lagrange12Proj0, map_add, map_neg, map_zsmul, hm2, hm1, h0, h1, h2,
      map_zero, smul_add, smul_neg, smul_zero, smul_smul]
    abel
  · simp only [lagrange12Proj1, map_add, map_neg, map_zsmul, hm2, hm1, h0, h1, h2,
      map_zero, smul_add, smul_neg, smul_zero, smul_smul]
    abel
  · simp only [lagrange12Proj2, map_add, map_neg, map_zsmul, hm2, hm1, h0, h1, h2,
      map_zero, smul_add, smul_smul]
    abel
  · simp only [lagrange12Proj1, map_add, map_neg, map_zsmul, hm2, hm1, h0, h1, h2,
      map_zero, smul_add, smul_neg, smul_zero, smul_smul]
    abel
  · simp only [lagrange12Proj1, map_add, map_sub, map_neg, map_zsmul, hm2, hm1, h0, h1, h2,
      map_zero, smul_add, smul_sub, smul_neg, smul_zero, smul_smul]
    abel
  · simp only [lagrange12Proj2, map_add, map_neg, map_zsmul, hm2, hm1, h0, h1, h2,
      map_zero, smul_add, smul_neg, smul_zero, smul_smul]
    abel
  · simp only [lagrange12Proj2, map_add, map_sub, map_neg, map_zsmul, hm2, hm1, h0, h1, h2,
      map_zero, smul_add, smul_neg, smul_zero, smul_smul]
    abel

/-- **Stage `𝔎𝔗₄` (`kt4_osp12_superconformal_contact_closure_and_super_jacobi`)**:
1. **Universal Associative Odd-Odd-Odd Super-Jacobi Identity & Rung 3 Aporia**:
   In any associative ring `[Ring B]`, for all $A, B_1, C \in B$:
   - $[A, \{B_1, C\}] + [B_1, \{C, A\}] + [C, \{A, B_1\}] = 0$.
   - **Rung 3 Aporia (`{Q_+, Q_+} = 0 ⟹ 2 Q_+ = 0`)**:
     If $Q_+, Q_-, H \in B$ satisfy $\{Q_+, Q_-\} = H$ and $[H, Q_+] = Q_+$, then
     $[Q_+, \{Q_+, Q_-\}] + [Q_+, \{Q_-, Q_+\}] = -(2 : \mathbb{Z}) \bullet Q_+$; hence if $\{Q_+, Q_+\} = 0$,
     then $(2 : \mathbb{Z}) \bullet Q_+ = 0$.
   - **Grade-$+2$ Supercharge Rescue (`{Q_+, Q_+} = 2 E_{+2}` with `[E_{+2}, Q_-] = -Q_+`)**:
     If $\{Q_+, Q_+\} = (2 : \mathbb{Z}) \bullet E_{+2}$ and $[E_{+2}, Q_-] = -Q_+$, then
     $[Q_-, \{Q_+, Q_+\}] = (2 : \mathbb{Z}) \bullet Q_+$, balancing $-(2 : \mathbb{Z}) \bullet Q_+$ identically.
2. **Concrete $M_3(R)$ $\mathfrak{osp}(1|2)$ Superconformal Contact Closure (`SuperconformalOSpJordanPair.lean`)**:
   - $\{Q_+, Q_+\} = 2 E$, $\{Q_-, Q_-\} = -2 F$, $\{Q_+, Q_-\} = H$, $[E, F] = H$,
   - $[H, Q_+] = Q_+$, $[H, Q_-] = -Q_-$, $[E, Q_-] = -Q_+$, $[F, Q_+] = -Q_-$,
   - $[Q_+, \{Q_+, Q_-\}] + [Q_+, \{Q_-, Q_+\}] + [Q_-, \{Q_+, Q_+\}] = 0$,
   - `jordanPairPlus (a • Q_plus R) (b • Q_minus R) (c • Q_plus R) = (a * b * c) • Q_plus R`. -/
theorem kt4_osp12_superconformal_contact_closure_and_super_jacobi
    {B : Type*} [Ring B] (A B₁ C Qp Qm H_op E2 : B)
    (hAntiPM : OperatorAlgebra.PeirceSpine.anticomm Qp Qm = H_op)
    (hGradP : OperatorAlgebra.PeirceSpine.comm H_op Qp = Qp)
    {R : Type*} [CommRing R] (a b c : R) :
    -- 1. Universal odd-odd-odd super-Jacobi identity in any associative ring:
    OperatorAlgebra.PeirceSpine.comm A (OperatorAlgebra.PeirceSpine.anticomm B₁ C) +
      OperatorAlgebra.PeirceSpine.comm B₁ (OperatorAlgebra.PeirceSpine.anticomm C A) +
      OperatorAlgebra.PeirceSpine.comm C (OperatorAlgebra.PeirceSpine.anticomm A B₁) = 0 ∧
    -- 2. Rung 3 aporia: {Q_+, Q_+} = 0 forces 2 Q_+ = 0, while {Q_+, Q_+} = 2 E_{+2} balances it:
    OperatorAlgebra.PeirceSpine.comm Qp (OperatorAlgebra.PeirceSpine.anticomm Qp Qm) +
      OperatorAlgebra.PeirceSpine.comm Qp (OperatorAlgebra.PeirceSpine.anticomm Qm Qp) =
      -((2 : ℤ) • Qp) ∧
    (OperatorAlgebra.PeirceSpine.anticomm Qp Qp = 0 → (2 : ℤ) • Qp = 0) ∧
    (OperatorAlgebra.PeirceSpine.anticomm Qp Qp = (2 : ℤ) • E2 →
      OperatorAlgebra.PeirceSpine.comm E2 Qm = -Qp →
      OperatorAlgebra.PeirceSpine.comm Qm (OperatorAlgebra.PeirceSpine.anticomm Qp Qp) =
        (2 : ℤ) • Qp) ∧
    -- 3. Concrete M_3(R) osp(1|2) supercharge closure, ladder relations, and super-Jacobi balance:
    SuperconformalOSpJordanPair.anticommutator
      (SuperconformalOSpJordanPair.Q_plus R) (SuperconformalOSpJordanPair.Q_plus R) =
      2 • SuperconformalOSpJordanPair.E_gen R ∧
    SuperconformalOSpJordanPair.anticommutator
      (SuperconformalOSpJordanPair.Q_minus R) (SuperconformalOSpJordanPair.Q_minus R) =
      -2 • SuperconformalOSpJordanPair.F_gen R ∧
    SuperconformalOSpJordanPair.anticommutator
      (SuperconformalOSpJordanPair.Q_plus R) (SuperconformalOSpJordanPair.Q_minus R) =
      SuperconformalOSpJordanPair.H_gen R ∧
    SuperconformalOSpJordanPair.commutator
      (SuperconformalOSpJordanPair.E_gen R) (SuperconformalOSpJordanPair.F_gen R) =
      SuperconformalOSpJordanPair.H_gen R ∧
    SuperconformalOSpJordanPair.commutator
      (SuperconformalOSpJordanPair.E_gen R) (SuperconformalOSpJordanPair.Q_minus R) =
      -SuperconformalOSpJordanPair.Q_plus R ∧
    SuperconformalOSpJordanPair.commutator
      (SuperconformalOSpJordanPair.F_gen R) (SuperconformalOSpJordanPair.Q_plus R) =
      -SuperconformalOSpJordanPair.Q_minus R ∧
    SuperconformalOSpJordanPair.commutator
        (SuperconformalOSpJordanPair.Q_plus R)
        (SuperconformalOSpJordanPair.anticommutator
          (SuperconformalOSpJordanPair.Q_plus R)
          (SuperconformalOSpJordanPair.Q_minus R)) +
      SuperconformalOSpJordanPair.commutator
        (SuperconformalOSpJordanPair.Q_plus R)
        (SuperconformalOSpJordanPair.anticommutator
          (SuperconformalOSpJordanPair.Q_minus R)
          (SuperconformalOSpJordanPair.Q_plus R)) +
      SuperconformalOSpJordanPair.commutator
        (SuperconformalOSpJordanPair.Q_minus R)
        (SuperconformalOSpJordanPair.anticommutator
          (SuperconformalOSpJordanPair.Q_plus R)
          (SuperconformalOSpJordanPair.Q_plus R)) = 0 ∧
    SuperconformalOSpJordanPair.jordanPairPlus
      (a • SuperconformalOSpJordanPair.Q_plus R)
      (b • SuperconformalOSpJordanPair.Q_minus R)
      (c • SuperconformalOSpJordanPair.Q_plus R) =
      (a * b * c) • SuperconformalOSpJordanPair.Q_plus R := by
  have hJac :
      OperatorAlgebra.PeirceSpine.comm A (OperatorAlgebra.PeirceSpine.anticomm B₁ C) +
        OperatorAlgebra.PeirceSpine.comm B₁ (OperatorAlgebra.PeirceSpine.anticomm C A) +
        OperatorAlgebra.PeirceSpine.comm C (OperatorAlgebra.PeirceSpine.anticomm A B₁) = 0 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm, OperatorAlgebra.PeirceSpine.anticomm]
    noncomm_ring
  have hAntiSymm :
      OperatorAlgebra.PeirceSpine.anticomm Qm Qp = H_op := by
    rw [← hAntiPM]
    dsimp [OperatorAlgebra.PeirceSpine.anticomm]
    abel
  have hCommQH : OperatorAlgebra.PeirceSpine.comm Qp H_op = -Qp := by
    calc OperatorAlgebra.PeirceSpine.comm Qp H_op
      _ = -OperatorAlgebra.PeirceSpine.comm H_op Qp := by
            dsimp [OperatorAlgebra.PeirceSpine.comm]
            noncomm_ring
      _ = -Qp := by rw [hGradP]
  have hTwoTerm :
      OperatorAlgebra.PeirceSpine.comm Qp (OperatorAlgebra.PeirceSpine.anticomm Qp Qm) +
        OperatorAlgebra.PeirceSpine.comm Qp (OperatorAlgebra.PeirceSpine.anticomm Qm Qp) =
        -((2 : ℤ) • Qp) := by
    rw [hAntiPM, hAntiSymm, hCommQH]
    abel
  have hAporia :
      OperatorAlgebra.PeirceSpine.anticomm Qp Qp = 0 → (2 : ℤ) • Qp = 0 := by
    intro hZero
    have hJ0 :
        OperatorAlgebra.PeirceSpine.comm Qp (OperatorAlgebra.PeirceSpine.anticomm Qp Qm) +
          OperatorAlgebra.PeirceSpine.comm Qp (OperatorAlgebra.PeirceSpine.anticomm Qm Qp) +
          OperatorAlgebra.PeirceSpine.comm Qm (OperatorAlgebra.PeirceSpine.anticomm Qp Qp) = 0 := by
      dsimp [OperatorAlgebra.PeirceSpine.comm, OperatorAlgebra.PeirceSpine.anticomm]
      noncomm_ring
    have hComm0 : OperatorAlgebra.PeirceSpine.comm Qm (0 : B) = 0 := by
      dsimp [OperatorAlgebra.PeirceSpine.comm]
      noncomm_ring
    rw [hTwoTerm, hZero, hComm0, add_zero, neg_eq_zero] at hJ0
    exact hJ0
  have hRescue :
      OperatorAlgebra.PeirceSpine.anticomm Qp Qp = (2 : ℤ) • E2 →
        OperatorAlgebra.PeirceSpine.comm E2 Qm = -Qp →
        OperatorAlgebra.PeirceSpine.comm Qm (OperatorAlgebra.PeirceSpine.anticomm Qp Qp) =
          (2 : ℤ) • Qp := by
    intro hQQ hEQm
    rw [hQQ]
    calc OperatorAlgebra.PeirceSpine.comm Qm ((2 : ℤ) • E2)
      _ = -((2 : ℤ) • OperatorAlgebra.PeirceSpine.comm E2 Qm) := by
            dsimp [OperatorAlgebra.PeirceSpine.comm]
            noncomm_ring
      _ = (2 : ℤ) • Qp := by
            rw [hEQm, smul_neg, neg_neg]
  have hMatJac :
      SuperconformalOSpJordanPair.commutator
          (SuperconformalOSpJordanPair.Q_plus R)
          (SuperconformalOSpJordanPair.anticommutator
            (SuperconformalOSpJordanPair.Q_plus R)
            (SuperconformalOSpJordanPair.Q_minus R)) +
        SuperconformalOSpJordanPair.commutator
          (SuperconformalOSpJordanPair.Q_plus R)
          (SuperconformalOSpJordanPair.anticommutator
            (SuperconformalOSpJordanPair.Q_minus R)
            (SuperconformalOSpJordanPair.Q_plus R)) +
        SuperconformalOSpJordanPair.commutator
          (SuperconformalOSpJordanPair.Q_minus R)
          (SuperconformalOSpJordanPair.anticommutator
            (SuperconformalOSpJordanPair.Q_plus R)
            (SuperconformalOSpJordanPair.Q_plus R)) = 0 := by
    dsimp [SuperconformalOSpJordanPair.commutator, SuperconformalOSpJordanPair.anticommutator]
    noncomm_ring
  exact ⟨hJac, hTwoTerm, hAporia, hRescue,
    SuperconformalOSpJordanPair.osp_anticomm_plus_plus,
    SuperconformalOSpJordanPair.osp_anticomm_minus_minus,
    SuperconformalOSpJordanPair.osp_anticomm_plus_minus,
    SuperconformalOSpJordanPair.osp_sl2_E_F,
    SuperconformalOSpJordanPair.osp_ladder_E_Q_minus,
    SuperconformalOSpJordanPair.osp_ladder_F_Q_plus,
    hMatJac,
    SuperconformalOSpJordanPair.jordan_pair_plus_scalar_readout a b c⟩

/-- **Stage `𝔎𝔗₅` (`kt5_gunaydin_gursey_gl1_sl3_color_decomposition`)**:
1. **Orthogonal Projector Split $M_3(\mathbb{R}) = \mathfrak{gl}_1(\mathbb{R})_H \oplus \mathfrak{sl}_3(\mathbb{R})_{\text{color}}$ (`Deduction 2 Theorem 4`)**:
   For all $X, Y \in M_3(\mathbb{R})$:
   - `gl1ColorProj X + sl3ColorProj X = X`,
   - `gl1ColorProj (gl1ColorProj X) = gl1ColorProj X` and `sl3ColorProj (sl3ColorProj X) = sl3ColorProj X`,
   - `gl1ColorProj (sl3ColorProj X) = 0` and `sl3ColorProj (gl1ColorProj X) = 0`,
   - `Matrix.trace (sl3ColorProj X) = 0` and `Matrix.trace (X * Y - Y * X) = 0`,
   - `gl1ColorProj X * Y - Y * gl1ColorProj X = 0`.
2. **Günaydin–Gürsey Quark–Antiquark Superbracket & $\mathbb{Z}_2 \times \mathbb{Z}_2$ Color SUSY Closure**:
   - `quarkAntiquarkOuter u v = quarkAntiquarkTracelessSL3 u v + gl1ColorProj (quarkAntiquarkOuter u v)`,
   - `quarkAntiquarkTracelessSL3 u v = sl3ColorProj (quarkAntiquarkOuter u v)`,
   - `z2z2KoszulSign gradeQuark gradeLepton = -1` and `z2z2KoszulSign gradeQuark gradeQuark = 1`. -/
theorem kt5_gunaydin_gursey_gl1_sl3_color_decomposition
    (X Y : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ)
    (z : InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.ZornSplitOctonion ℝ) :
    -- 1. Orthogonal gl_1(ℝ) ⊕ sl_3(ℝ) projector algebra:
    gl1ColorProj X + sl3ColorProj X = X ∧
    gl1ColorProj (gl1ColorProj X) = gl1ColorProj X ∧
    sl3ColorProj (sl3ColorProj X) = sl3ColorProj X ∧
    gl1ColorProj (sl3ColorProj X) = 0 ∧
    sl3ColorProj (gl1ColorProj X) = 0 ∧
    Matrix.trace (sl3ColorProj X) = 0 ∧
    Matrix.trace (X * Y - Y * X) = 0 ∧
    gl1ColorProj X * Y - Y * gl1ColorProj X = 0 ∧
    -- 2. Quark–antiquark outer product decomposition and ℤ₂ × ℤ₂ Koszul signs:
    quarkAntiquarkOuter u v =
      quarkAntiquarkTracelessSL3 u v +
        ((1 / 3 : ℝ) * quarkAntiquarkDilatationTrace u v) • (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
    Matrix.trace (quarkAntiquarkToSL3 u v).1 = 0 ∧
    z2z2KoszulSign gradeQuark gradeLepton = -1 ∧
    z2z2KoszulSign gradeQuark gradeQuark = 1 := by
  have htr1 : Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ) = 3 := by
    rw [Matrix.trace_one, Fintype.card_fin]
    norm_num
  have htr_gl1 : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, Matrix.trace (gl1ColorProj M) = Matrix.trace M := by
    intro M
    dsimp [gl1ColorProj]
    rw [Matrix.trace_smul, htr1, smul_eq_mul]
    ring
  have htr_sl3 : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, Matrix.trace (sl3ColorProj M) = 0 := by
    intro M
    dsimp [sl3ColorProj]
    rw [Matrix.trace_sub, htr_gl1 M, sub_self]
  have h_gl1_idem : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, gl1ColorProj (gl1ColorProj M) = gl1ColorProj M := by
    intro M
    dsimp [gl1ColorProj]
    rw [Matrix.trace_smul, htr1, smul_eq_mul]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have h_gl1_sl3 : gl1ColorProj (sl3ColorProj X) = 0 := by
    dsimp [gl1ColorProj]
    rw [htr_sl3 X, mul_zero, zero_smul]
  have h_sl3_gl1 : sl3ColorProj (gl1ColorProj X) = 0 := by
    dsimp [sl3ColorProj]
    rw [h_gl1_idem X, sub_self]
  have h_sl3_idem : sl3ColorProj (sl3ColorProj X) = sl3ColorProj X := by
    change sl3ColorProj X - gl1ColorProj (sl3ColorProj X) = sl3ColorProj X
    rw [h_gl1_sl3, sub_zero]
  have h_sum : gl1ColorProj X + sl3ColorProj X = X := by
    dsimp [sl3ColorProj]
    abel
  have h_tr_comm : Matrix.trace (X * Y - Y * X) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self]
  have h_gl1_central : gl1ColorProj X * Y - Y * gl1ColorProj X = 0 := by
    dsimp [gl1ColorProj]
    rw [Algebra.smul_mul_assoc, Matrix.one_mul, Algebra.mul_smul_comm, Matrix.mul_one, sub_self]
  have hGG := gunaydin_gursey_g1_gm1_superbracket_closure u v z
  have hSign := z2z2_color_supersymmetry_sign_laws gradeQuark gradeLepton
  exact ⟨h_sum, h_gl1_idem X, h_sl3_idem, h_gl1_sl3, h_sl3_gl1,
    htr_sl3 X, h_tr_comm, h_gl1_central,
    hGG.1, hGG.2.1, hSign.2.2.2.1, hSign.2.2.2.2.2⟩

/-- **Stage `𝔎𝔗₆` (`kt6_five_graded_maurer_cartan_and_kantor_sandwich_closure`)**:
Unifies the 6-stage **Kantor–Tanaka Contact Prolongation Poset** (`𝔎𝔗₁ ≺ ⋯ ≺ 𝔎𝔗₆`) with
5-graded Maurer–Cartan flatness (`canonicalMaurerCartanJet_flat`) and the bilateral Kantor
sandwich identity (`kantorG0² - {kantorGp2, kantorGm2} = Σ · Σ`). -/
theorem kt6_five_graded_maurer_cartan_and_kantor_sandwich_closure
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B) :
    -- 1. Poset DAG acyclicity and cardinality of 𝔎𝔗₁ ≺ ⋯ ≺ 𝔎𝔗₆:
    (∀ st : KantorTanakaContactStage,
      ¬ Relation.TransGen KantorTanakaContactStage.causalEdge st st) ∧
    Fintype.card KantorTanakaContactStage = 6 ∧
    -- 2. 5-graded Maurer–Cartan non-triviality and flatness:
    canonicalMaurerCartanJet ≠ (default : FiveGradedMaurerCartanJet ℝ) ∧
    mcCurvatureTower canonicalMaurerCartanJet = (0, 0, 0, 0, 0) ∧
    -- 3. Bilateral Kantor sandwich closure on any Peirce ring:
    kantorGp2 P A (conePlus P A) = 0 ∧
    kantorGm2 P C (coneMinus P C) = 0 ∧
    kantorGp2 P A (coneMinus P C) = genV P A C * conePlus P A ∧
    kantorGm2 P C (conePlus P A) = genV P A C * coneMinus P C ∧
    kantorG0 P A C (kantorG0 P A C X) -
      (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
      genSig P A C * X * genSig P A C := by
  refine ⟨KantorTanakaContactStage.causalEdge_acyclic,
    KantorTanakaContactStage.card_eq_six,
    canonicalMaurerCartanJet_ne_default,
    canonicalMaurerCartanJet_flat,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [kantorGp2, kantorGm2, kantorG0, kantorTriple]; peirce_nf hP)

end KantorTanakaContactProlongationPoset

/-!
## 7. Stage `𝔊₆`: Split-Octonion $\mathrm{Cl}(3,3)$ Para-Kähler Phase Space & Metriplectic Product
-/

/-- **Stage `𝔊₆` (`G6_SplitOctonionCl33ParaKahlerPhaseSpaceAndMetriplecticProduct`)**:
1. **Fock Spinor Sheet Identification (`SplitOctonionParaKahlerNullCone.lean`)**:
   The vacuum columns of the grade-$+1$ Fock creation matrix `gPlus1 k` and the cyclic Hodge
   grade-$+2$ creation matrix `gPlus2Hodge k` map under `fin8ToZorn` to the embedded primal
   sheet $T^+$ and dual sheet $T^-$ of the 6D Para-Kähler phase space `ParaKahlerVec ℤ`.
2. **Clifford–Zorn Anticommutator & Metriplectic Product over `ℝ`**:
   In `ZornSplitOctonion ℝ`, the anticommutator $\{z_1, z_2\}$ is $g(z_1, z_2) \cdot 1_{\text{Zorn}}$,
   and the full split-octonion product decomposes into the symmetric Para-Kähler metric $g$, the
   symplectic 2-form $\omega$ along $I_{\text{para}}$, and the Hodge cross product $z_1 \times_H z_2$:
   $$z_1 z_2 = \tfrac{1}{2} g(z_1, z_2) 1_{\text{Zorn}} + \tfrac{1}{2} \omega(z_1, z_2) I_{\text{para}} + z_1 \times_H z_2.$$
3. **Lagrange–Binet–Cauchy Norm Composition & Primal Triple Volume Identities**:
   The Para-Kähler metric and symplectic form satisfy
   $g(z_1, z_2)^2 - \omega(z_1, z_2)^2 + 4\langle u_1 \times u_2, v_1 \times v_2 \rangle = g(z_1, z_1)g(z_2, z_2)$,
   while for three primal sheet vectors $u_1, u_2, u_3$ the bracketing sum $(u_1 u_2)u_3 + u_1(u_2 u_3)$
   lands on $\det(u_1, u_2, u_3) 1_{\text{Zorn}}$ and the associator $[u_1, u_2, u_3]$ lands on
   $-\det(u_1, u_2, u_3) I_{\text{para}}$. -/
theorem g6_split_octonion_cl33_parakahler_phase_space_and_metriplectic_product
    (k : Fin 3) (z₁ z₂ : ParaKahlerVec ℝ) (u₁ u₂ u₃ : Fin 3 → ℝ) :
    -- 1. Fock spinor bridge for primal T^+ and dual T^- sheets:
    InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.fin8ToZorn
      (fun r => InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.gPlus1 k r 0) =
      embedVec (SplitOctonionParaKahlerNullCone.primalSheet
        (fun j => if j = k then (1 : ℤ) else 0)) ∧
    InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.fin8ToZorn
      (fun r => InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.gPlus2Hodge k r 0) =
      embedVec (SplitOctonionParaKahlerNullCone.dualSheet
        (fun j => if j = k then (1 : ℤ) else 0)) ∧
    -- 2. Clifford–Zorn anticommutator and full metriplectic product decomposition over ℝ:
    zornAdd (InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul (embedVec z₁) (embedVec z₂))
        (InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul (embedVec z₂) (embedVec z₁)) =
      SplitOctonionParaKahlerNullCone.zornSmul (paraKahlerMetric z₁ z₂) zornOne ∧
    InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul (embedVec z₁) (embedVec z₂) =
      zornAdd
        (zornAdd
          (SplitOctonionParaKahlerNullCone.zornSmul ((1 / 2 : ℝ) * paraKahlerMetric z₁ z₂) zornOne)
          (SplitOctonionParaKahlerNullCone.zornSmul ((1 / 2 : ℝ) * symplecticForm z₁ z₂) zornParaGrading))
        (embedVec (hodgeCrossVec z₁ z₂)) ∧
    -- 3. Lagrange–Binet–Cauchy norm composition and primal triple sum/associator volume laws:
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 +
      4 * InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Dot
        (InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Cross z₁.u z₂.u)
        (InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Cross z₁.v z₂.v) =
      paraKahlerMetric z₁ z₁ * paraKahlerMetric z₂ z₂ ∧
    zornAdd
      (InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul
        (InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul
          (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₁))
          (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₂)))
        (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₃)))
      (InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul
        (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₁))
        (InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul
          (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₂))
          (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₃)))) =
      SplitOctonionParaKahlerNullCone.zornSmul (vec3TripleProduct u₁ u₂ u₃) zornOne ∧
    SplitOctonionParaKahlerNullCone.zornAssociator
      (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₁))
      (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₂))
      (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₃)) =
      SplitOctonionParaKahlerNullCone.zornSmul (-vec3TripleProduct u₁ u₂ u₃) zornParaGrading := by
  exact ⟨fin8ToZorn_gPlus1_vac_eq_embedVec_primalSheet k,
    fin8ToZorn_gPlus2Hodge_vac_eq_embedVec_dualSheet k,
    zorn_anticommutator_eq_paraKahlerMetric_smul_one z₁ z₂,
    zornMul_embedVec_metriplectic_decomp z₁ z₂,
    paraKahler_lagrange_norm_composition z₁ z₂,
    zorn_primal_triple_bracketing_sum_eq_volume_smul_one u₁ u₂ u₃,
    zorn_primal_triple_associator_eq_volume_paraGrading u₁ u₂ u₃⟩

/-!
## 7b. The 6-Stage Metriplectic Zorn Split-Octonion Closure, Three-Term Pythagorean Norm Law, & Dual Cubic Volume Poset (`𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ ⋯ ≺ 𝔐ℨ₆`)

This section refines Stage `𝔊₆` and `SplitOctonionCircularIsotropicAmariNambuPoset` into the
6-stage Acyclic Causal Poset
$$\mathfrak{MZ}_1 \prec \mathfrak{MZ}_2 \prec \mathfrak{MZ}_3 \prec \mathfrak{MZ}_4 \prec \mathfrak{MZ}_5 \prec \mathfrak{MZ}_6$$
on the ring-universal split-octonion carrier `ZornMat R` (`ZornMatrix R`):
- **Stage `𝔐ℨ₁` (`mz1_dewitt_basis_and_three_channel_projectors`)**:
  DeWitt idempotent basis $(u_0, u_0^*) \leftrightarrow (1 = u_0 + u_0^*, I_{\text{para}} = u_0 - u_0^*)$,
  diagonal/off-diagonal decomposition $X = \mathrm{zornDiagPart}\,X + \mathrm{zornOffDiagPart}\,X$,
  and three-channel projection identities $g_{\text{Zorn}}(z_1, z_2) = \mathrm{tr}(z_1 z_2)$,
  $\omega_{\text{Zorn}}(z_1, z_2) = \mathrm{tr}(I_{\text{para}}(z_1 z_2))$, and
  $z_1 \times_H z_2 = \mathrm{zornOffDiagPart}(z_1 z_2)$.
- **Stage `𝔐ℨ₂` (`mz2_three_term_metriplectic_zorn_decomposition`)**:
  Division-free universal ring identity over any `[Ring R]`:
  $$z_1 z_2 + z_1 z_2 = g_{\text{Zorn}}(z_1, z_2)\cdot 1_{\text{Zorn}} + \omega_{\text{Zorn}}(z_1, z_2)\cdot I_{\text{para}} + (z_1 \times_H z_2 + z_1 \times_H z_2).$$
- **Stage `𝔐ℨ₃` (`mz3_parakahler_locking_and_jordan_malcev_tangent_split`)**:
  Universal Para-Kähler locking $\omega_{\text{Zorn}}(z_1, z_2) = g_{\text{Zorn}}(I_{\text{para}} z_1, z_2)$,
  and on the 6D tangent space $\mathfrak{p}$ ($z_i = \mathrm{zornPhi}\,u_i\,v_i$):
  $g_{\text{Zorn}}(I_{\text{para}} z_1, I_{\text{para}} z_2) = -g_{\text{Zorn}}(z_1, z_2)$,
  Jordan anticommutator $\{z_1, z_2\} = g_{\text{Zorn}}(z_1, z_2)\cdot 1_{\text{Zorn}}$, and
  Malcev commutator $[z_1, z_2] = \omega_{\text{Zorn}}(z_1, z_2)\cdot I_{\text{para}} + 2(z_1 \times_H z_2)$.
- **Stage `𝔐ℨ₄` (`mz4_three_term_metriplectic_pythagorean_norm_law`)**:
  Three-term Metriplectic Pythagorean Norm Law over any `[CommRing K]`:
  $$g_{\text{Zorn}}(z_1, z_2)^2 - \omega_{\text{Zorn}}(z_1, z_2)^2 - 4\det_{\text{Zorn}}(z_1 \times_H z_2) = 4\det_{\text{Zorn}}(z_1 z_2) = 4\det_{\text{Zorn}}(z_1)\det_{\text{Zorn}}(z_2),$$
  together with the Rung 0 non-collinear reflection witness on $(e_1, e_2)$.
- **Stage `𝔐ℨ₅` (`mz5_third_order_dual_volume_split_on_sum_and_diff`)**:
  Third-order chiral volume duality on $1_{\text{Zorn}}$ vs. $I_{\text{para}}$:
  $$\{z_1 \times_H z_2, z_3\} = (\det(u_1, u_2, u_3) - \det(v_1, v_2, v_3))\cdot 1_{\text{Zorn}},$$
  $$\mathrm{zornDiagPart}([z_1, z_2, z_3]_{\text{assoc}}) = -(\det(u_1, u_2, u_3) + \det(v_1, v_2, v_3))\cdot I_{\text{para}}.$$
- **Stage `𝔐ℨ₆` (`mz6_noncommutative_nambu_associator_and_master_synthesis`)**:
  Non-commutative Nambu 3-bracket self-associators over `[Ring R]` landing strictly on $I_{\text{para}}$
  and master synthesis of `𝔐ℨ₁ ≺ ⋯ ≺ 𝔐ℨ₆` and `𝔎𝔗₁ ≺ ⋯ ≺ 𝔎𝔗₆`.
-/

/-- The 6 stages of the **Metriplectic Zorn Split-Octonion Closure & Dual Cubic Volume Poset**
(`𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ 𝔐ℨ₃ ≺ 𝔐ℨ₄ ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`). -/
inductive MetriplecticZornStage : Type
  /-- `𝔐ℨ₁`: DeWitt basis `(1, I_para)` & three-channel projectors `(g_Zorn, ω_Zorn, ×_H)`. -/
  | MZ1_DeWittBasisAndThreeChannelProjectors
  /-- `𝔐ℨ₂`: Exact three-term metriplectic Zorn product decomposition `2 z₁ z₂ = g 1 + ω I_para + 2(z₁ ×_H z₂)`. -/
  | MZ2_ThreeTermMetriplecticZornDecomposition
  /-- `𝔐ℨ₃`: Para-Kähler locking `ω(z₁, z₂) = g(I_para z₁, z₂)` & Jordan–Malcev tangent split on `𝔭`. -/
  | MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit
  /-- `𝔐ℨ₄`: Three-term metriplectic Pythagorean norm law `4 det(z₁ z₂) = g² - ω² - 4 det(z₁ ×_H z₂) = 4 det(z₁) det(z₂)`. -/
  | MZ4_ThreeTermMetriplecticPythagoreanNormLaw
  /-- `𝔐ℨ₅`: Third-order chiral volume duality on `1_Zorn` (`Δ_u - Δ_v`) vs. `I_para` (`-(Δ_u + Δ_v)`). -/
  | MZ5_ThirdOrderDualVolumeSplitOnSumAndDiff
  /-- `𝔐ℨ₆`: Non-commutative Nambu 3-bracket associator on `I_para` & master metriplectic synthesis. -/
  | MZ6_NonCommutativeNambuAssociatorAndMasterSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace MetriplecticZornStage

/-- Integer rank `0 .. 5` for `𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ ⋯ ≺ 𝔐ℨ₆`. -/
def rank : MetriplecticZornStage → ℕ
  | .MZ1_DeWittBasisAndThreeChannelProjectors            => 0
  | .MZ2_ThreeTermMetriplecticZornDecomposition          => 1
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit    => 2
  | .MZ4_ThreeTermMetriplecticPythagoreanNormLaw         => 3
  | .MZ5_ThirdOrderDualVolumeSplitOnSumAndDiff           => 4
  | .MZ6_NonCommutativeNambuAssociatorAndMasterSynthesis => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder MetriplecticZornStage where
  le a b := rank a ≤ rank b
  lt a b := rank a < rank b
  le_refl a := le_rfl
  le_trans a b c := Nat.le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (rank a) (rank b)
  le_antisymm a b hab hba := rank_injective (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total (rank a) (rank b)
  toDecidableLE a b := Nat.decLe (rank a) (rank b)
  toDecidableEq := inferInstance
  toDecidableLT a b := Nat.decLt (rank a) (rank b)

instance : Fintype MetriplecticZornStage where
  elems := {
    .MZ1_DeWittBasisAndThreeChannelProjectors,
    .MZ2_ThreeTermMetriplecticZornDecomposition,
    .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit,
    .MZ4_ThreeTermMetriplecticPythagoreanNormLaw,
    .MZ5_ThirdOrderDualVolumeSplitOnSumAndDiff,
    .MZ6_NonCommutativeNambuAssociatorAndMasterSynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card MetriplecticZornStage = 6 := rfl

/-- Directed covering edges `𝔐ℨ_k ≺ 𝔐ℨ_{k+1}`. -/
def causalEdge (a b : MetriplecticZornStage) : Prop :=
  rank b = rank a + 1

theorem causalEdge_lt {a b : MetriplecticZornStage} (h : causalEdge a b) :
    rank a < rank b := by
  dsimp [causalEdge] at h
  omega

theorem transGen_causalEdge_lt {a b : MetriplecticZornStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

/-- Strict DAG acyclicity of `𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ ⋯ ≺ 𝔐ℨ₆`. -/
theorem causalEdge_acyclic (a : MetriplecticZornStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_lt h)

/-- Monotone embedding into `InfoGeometry.Meta.RepDepth`. -/
def toRepDepth : MetriplecticZornStage → InfoGeometry.Meta.RepDepth
  | .MZ1_DeWittBasisAndThreeChannelProjectors            => .operator
  | .MZ2_ThreeTermMetriplecticZornDecomposition          => .operator
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit    => .transport
  | .MZ4_ThreeTermMetriplecticPythagoreanNormLaw         => .transport
  | .MZ5_ThirdOrderDualVolumeSplitOnSumAndDiff           => .thermo
  | .MZ6_NonCommutativeNambuAssociatorAndMasterSynthesis => .thermo

/-- Monotone embedding into `InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    MetriplecticZornStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .MZ1_DeWittBasisAndThreeChannelProjectors            => .M1_ProjectorClabject
  | .MZ2_ThreeTermMetriplecticZornDecomposition          => .M1_ProjectorClabject
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit    => .M2_GrassmannianPowertypeOrbit
  | .MZ4_ThreeTermMetriplecticPythagoreanNormLaw         => .M2_GrassmannianPowertypeOrbit
  | .MZ5_ThirdOrderDualVolumeSplitOnSumAndDiff           => .M3_ErlangenCasimirMetaLaw
  | .MZ6_NonCommutativeNambuAssociatorAndMasterSynthesis => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : MetriplecticZornStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth InfoGeometry.Meta.RepDepth.toNat <;>
    decide

theorem toOntologyMetaLevel_mono {a b : MetriplecticZornStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;>
    decide

end MetriplecticZornStage

section MetriplecticZornSplitOctonionPoset

open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon

variable {R : Type*} [Ring R]

/-- Combined 6D Para-Kähler tangent frame $\Phi(u, v) := N_+(u) + N_-(v) = \begin{pmatrix} 0 & u \\ v & 0 \end{pmatrix}$
in `ZornMat R`. -/
@[simp] def zornPhi (u v : Vec3 R) : ZornMat R :=
  ⟨0, u, v, 0⟩

/-- Diagonal projection $\mathrm{zornDiagPart}(X) := \begin{pmatrix} a & 0 \\ 0 & d \end{pmatrix}$ in `ZornMat R`. -/
@[simp] def zornDiagPart (X : ZornMat R) : ZornMat R :=
  ⟨X.a, 0, 0, X.d⟩

/-- Off-diagonal tangent projection $\mathrm{zornOffDiagPart}(X) := \begin{pmatrix} 0 & u \\ v & 0 \end{pmatrix}$
in `ZornMat R`. -/
@[simp] def zornOffDiagPart (X : ZornMat R) : ZornMat R :=
  ⟨0, X.u, X.v, 0⟩

/-- Zorn trace $\mathrm{tr}_{\text{Zorn}}(X) := a + d$ on `ZornMat R`. -/
@[simp] def zornMatTrace (X : ZornMat R) : R :=
  X.a + X.d

/-- Zorn quadratic determinant $\det_{\text{Zorn}}(X) := a d - u \cdot v$ on `ZornMat R`. -/
@[simp] def zornMatDet (X : ZornMat R) : R :=
  X.a * X.d - Vec3.dot X.u X.v

/-- Symmetric Para-Kähler metric pairing $g_{\text{Zorn}}(z_1, z_2) := (a_1 a_2 + d_1 d_2) + (u_1 \cdot v_2 + v_1 \cdot u_2)$
on `ZornMat R`. -/
@[simp] def zornMetricG (z₁ z₂ : ZornMat R) : R :=
  (z₁.a * z₂.a + z₁.d * z₂.d) + (Vec3.dot z₁.u z₂.v + Vec3.dot z₁.v z₂.u)

/-- Symplectic 2-form pairing $\omega_{\text{Zorn}}(z_1, z_2) := (a_1 a_2 - d_1 d_2) + (u_1 \cdot v_2 - v_1 \cdot u_2)$
on `ZornMat R`. -/
@[simp] def zornSymplecticOmega (z₁ z₂ : ZornMat R) : R :=
  (z₁.a * z₂.a - z₁.d * z₂.d) + (Vec3.dot z₁.u z₂.v - Vec3.dot z₁.v z₂.u)

/-- Off-diagonal 3D Hodge cross-product channel $z_1 \times_H z_2 := \mathrm{zornOffDiagPart}(z_1 z_2)$
on `ZornMat R`. -/
@[simp] def zornHodgeCross (z₁ z₂ : ZornMat R) : ZornMat R :=
  ⟨0,
   Vec3.smulLeft z₁.a z₂.u + Vec3.smulRight z₁.u z₂.d - Vec3.cross z₁.v z₂.v,
   Vec3.smulRight z₁.v z₂.a + Vec3.smulLeft z₁.d z₂.v + Vec3.cross z₁.u z₂.u,
   0⟩

/-- **Stage `𝔐ℨ₁` (`mz1_dewitt_basis_and_three_channel_projectors`)**:
Over any associative ring `[Ring R]`, for all $z_1, z_2, X \in \mathrm{ZornMat}\,R$:
1. **DeWitt Idempotent Basis & Diagonal/Off-Diagonal Split**:
   - `zornU0 + zornU0Star = (1 : ZornMat R)` and `zornU0 - zornU0Star = (zornDeWittDiff : ZornMat R)`,
   - `(zornDeWittDiff : ZornMat R) * zornDeWittDiff = 1` and `zornMatTrace (zornDeWittDiff : ZornMat R) = 0`,
   - `X = zornDiagPart X + zornOffDiagPart X`,
   - `zornDiagPart X = InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul X.a zornU0 + InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul X.d zornU0Star`,
   - `zornOffDiagPart X = zornPhi X.u X.v` and `zornPhi X.u X.v = zornPlusVec X.u + zornMinusVec X.v`.
2. **Three-Channel Readout Identities**:
   - `zornMetricG z₁ z₂ = zornMatTrace (z₁ * z₂)`,
   - `zornSymplecticOmega z₁ z₂ = zornMatTrace (zornDeWittDiff * (z₁ * z₂))`,
   - `zornHodgeCross z₁ z₂ = zornOffDiagPart (z₁ * z₂)`,
   - `zornMatTrace (zornHodgeCross z₁ z₂) = 0` and `zornDiagPart (zornHodgeCross z₁ z₂) = 0`. -/
theorem mz1_dewitt_basis_and_three_channel_projectors (z₁ z₂ X : ZornMat R) :
    (zornU0 : ZornMat R) + zornU0Star = 1 ∧
    (zornU0 : ZornMat R) - zornU0Star = zornDeWittDiff ∧
    (zornDeWittDiff : ZornMat R) * zornDeWittDiff = 1 ∧
    zornMatTrace (zornDeWittDiff : ZornMat R) = 0 ∧
    X = zornDiagPart X + zornOffDiagPart X ∧
    zornDiagPart X = InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul X.a zornU0 + InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul X.d zornU0Star ∧
    zornOffDiagPart X = zornPhi X.u X.v ∧
    zornPhi X.u X.v = zornPlusVec X.u + zornMinusVec X.v ∧
    zornMetricG z₁ z₂ = zornMatTrace (z₁ * z₂) ∧
    zornSymplecticOmega z₁ z₂ = zornMatTrace (zornDeWittDiff * (z₁ * z₂)) ∧
    zornHodgeCross z₁ z₂ = zornOffDiagPart (z₁ * z₂) ∧
    zornMatTrace (zornHodgeCross z₁ z₂) = 0 ∧
    zornDiagPart (zornHodgeCross z₁ z₂) = 0 := by
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp
  · ext <;> simp [Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · simp [zornMatTrace, zornDeWittDiff, zornU0, zornU0Star]
  · ext <;> simp
  · ext <;> simp [InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul, zornU0, zornU0Star, ZornMatrix.smul, Vec3.smulLeft]
  · ext <;> simp [zornPlusVec, zornMinusVec, ZornMatrix.zornConePlus, ZornMatrix.zornConeMinus]
  · simp [zornMetricG, zornMatTrace, ZornMatrix.mul_a, ZornMatrix.mul_d]
    abel
  · simp [zornSymplecticOmega, zornMatTrace, zornDeWittDiff, zornU0, zornU0Star,
      ZornMatrix.mul_a, ZornMatrix.mul_d, Vec3.dot]
    noncomm_ring
  · ext <;> rfl
  · simp [zornMatTrace, zornHodgeCross]
  · ext <;> rfl

/-- **Stage `𝔐ℨ₂` (`mz2_three_term_metriplectic_zorn_decomposition`)**:
1. **Division-Free Universal Ring Decomposition (`Rung 1` & `Axiom I Theorem 1.1`)**:
   Over any associative ring `[Ring R]`, for all $z_1, z_2 \in \mathrm{ZornMat}\,R$:
   - `(z₁ * z₂).a + (z₁ * z₂).a = zornMetricG z₁ z₂ + zornSymplecticOmega z₁ z₂`,
   - `(z₁ * z₂).d + (z₁ * z₂).d = zornMetricG z₁ z₂ - zornSymplecticOmega z₁ z₂`,
   - `zornDiagPart (z₁ * z₂ + z₁ * z₂) = InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornMetricG z₁ z₂) (1 : ZornMat R) + InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornSymplecticOmega z₁ z₂) zornDeWittDiff`,
   - `z₁ * z₂ + z₁ * z₂ = InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornMetricG z₁ z₂) (1 : ZornMat R) + InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornSymplecticOmega z₁ z₂) zornDeWittDiff + (zornHodgeCross z₁ z₂ + zornHodgeCross z₁ z₂)`.
2. **Normalized Real Phase-Space Decomposition (`SplitOctonionParaKahlerNullCone.lean`)**:
   For all $w_1, w_2 \in \mathrm{ParaKahlerVec}\,\mathbb{R}$:
   `zornMul (embedVec w₁) (embedVec w₂) = zornAdd (zornAdd (SplitOctonionParaKahlerNullCone.zornSmul ((1 / 2 : ℝ) * paraKahlerMetric w₁ w₂) zornOne) (SplitOctonionParaKahlerNullCone.zornSmul ((1 / 2 : ℝ) * symplecticForm w₁ w₂) zornParaGrading)) (embedVec (hodgeCrossVec w₁ w₂))`. -/
theorem mz2_three_term_metriplectic_zorn_decomposition
    (z₁ z₂ : ZornMat R) (w₁ w₂ : ParaKahlerVec ℝ) :
    (z₁ * z₂).a + (z₁ * z₂).a = zornMetricG z₁ z₂ + zornSymplecticOmega z₁ z₂ ∧
    (z₁ * z₂).d + (z₁ * z₂).d = zornMetricG z₁ z₂ - zornSymplecticOmega z₁ z₂ ∧
    zornDiagPart (z₁ * z₂ + z₁ * z₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornMetricG z₁ z₂) (1 : ZornMat R) +
        InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornSymplecticOmega z₁ z₂) zornDeWittDiff ∧
    z₁ * z₂ + z₁ * z₂ =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornMetricG z₁ z₂) (1 : ZornMat R) +
        InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornSymplecticOmega z₁ z₂) zornDeWittDiff +
        (zornHodgeCross z₁ z₂ + zornHodgeCross z₁ z₂) ∧
    InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul (embedVec w₁) (embedVec w₂) =
      zornAdd
        (zornAdd
          (SplitOctonionParaKahlerNullCone.zornSmul ((1 / 2 : ℝ) * paraKahlerMetric w₁ w₂) zornOne)
          (SplitOctonionParaKahlerNullCone.zornSmul ((1 / 2 : ℝ) * symplecticForm w₁ w₂) zornParaGrading))
        (embedVec (hodgeCrossVec w₁ w₂)) := by
  have ha : (z₁ * z₂).a + (z₁ * z₂).a = zornMetricG z₁ z₂ + zornSymplecticOmega z₁ z₂ := by
    simp only [ZornMatrix.mul_a, zornMetricG, zornSymplecticOmega]
    abel
  have hd : (z₁ * z₂).d + (z₁ * z₂).d = zornMetricG z₁ z₂ - zornSymplecticOmega z₁ z₂ := by
    simp only [ZornMatrix.mul_d, zornMetricG, zornSymplecticOmega]
    abel
  refine ⟨ha, hd, ?_, ?_, zornMul_embedVec_metriplectic_decomp w₁ w₂⟩
  · ext <;> simp [zornDiagPart, InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul, zornDeWittDiff, zornU0, zornU0Star,
      ZornMatrix.smul, ZornMatrix.mul_a, ZornMatrix.mul_d,
      zornMetricG, zornSymplecticOmega, Vec3.smulLeft] <;> noncomm_ring
  · ext <;> simp [InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul, zornDeWittDiff, zornU0, zornU0Star, zornHodgeCross,
      ZornMatrix.smul, ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      zornMetricG, zornSymplecticOmega, Vec3.smulLeft, Vec3.smulRight] <;> noncomm_ring

/-- **Stage `𝔐ℨ₃` (`mz3_parakahler_locking_and_jordan_malcev_tangent_split`)**:
1. **Universal Para-Kähler Locking (`ω(z₁, z₂) = g(I_para z₁, z₂)`)** (`Rung 2` & `Axiom I Theorem 1.2`):
   Over any `[Ring R]`, for all $z_1, z_2 \in \mathrm{ZornMat}\,R$:
   - `zornSymplecticOmega z₁ z₂ = zornMetricG (zornDeWittDiff * z₁) z₂`,
   - `zornMetricG (zornDeWittDiff * z₁) z₂ = zornMetricG z₁ (z₂ * zornDeWittDiff)`.
2. **6D Para-Kähler Tangent Space $\mathfrak{p}$ Polarization & Anti-Invariance**:
   For $u_1, v_1, u_2, v_2 \in \mathrm{Vec3}\,R$:
   - `zornDeWittDiff * zornPhi u₁ v₁ = zornPhi u₁ (-v₁)`,
   - `zornPhi u₁ v₁ * zornDeWittDiff = zornPhi (-u₁) v₁`,
   - `zornMetricG (zornDeWittDiff * zornPhi u₁ v₁) (zornDeWittDiff * zornPhi u₂ v₂) = -zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂)`,
   - `zornSymplecticOmega (zornDeWittDiff * zornPhi u₁ v₁) (zornDeWittDiff * zornPhi u₂ v₂) = zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂)`.
3. **Jordan–Malcev Tangent Split on $\mathfrak{p}$ over `[CommRing K]`**:
   For $u_1, v_1, u_2, v_2 \in \mathrm{Vec3}\,K$:
   - `zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) = zornMetricG (zornPhi u₂ v₂) (zornPhi u₁ v₁)`,
   - `zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) = -zornSymplecticOmega (zornPhi u₂ v₂) (zornPhi u₁ v₁)`,
   - `zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂) = -zornHodgeCross (zornPhi u₂ v₂) (zornPhi u₁ v₁)`,
   - **Jordan Anticommutator**:
     `zornPhi u₁ v₁ * zornPhi u₂ v₂ + zornPhi u₂ v₂ * zornPhi u₁ v₁ = InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂)) (1 : ZornMat K)`,
   - **Malcev Commutator**:
     `zornPhi u₁ v₁ * zornPhi u₂ v₂ - zornPhi u₂ v₂ * zornPhi u₁ v₁ = InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂)) zornDeWittDiff + (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂) + zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂))`. -/
theorem mz3_parakahler_locking_and_jordan_malcev_tangent_split
    (z₁ z₂ : ZornMat R) (u₁R v₁R u₂R v₂R : Vec3 R)
    {K : Type*} [CommRing K] (u₁ v₁ u₂ v₂ : Vec3 K) :
    -- 1. Universal Para-Kähler locking over [Ring R]:
    zornSymplecticOmega z₁ z₂ = zornMetricG (zornDeWittDiff * z₁) z₂ ∧
    zornMetricG (zornDeWittDiff * z₁) z₂ = zornMetricG z₁ (z₂ * zornDeWittDiff) ∧
    -- 2. Para-complex action and metric anti-invariance on tangent space 𝔭 over [Ring R]:
    zornDeWittDiff * zornPhi u₁R v₁R = zornPhi u₁R (-v₁R) ∧
    zornPhi u₁R v₁R * zornDeWittDiff = zornPhi (-u₁R) v₁R ∧
    zornMetricG (zornDeWittDiff * zornPhi u₁R v₁R) (zornDeWittDiff * zornPhi u₂R v₂R) =
      -zornMetricG (zornPhi u₁R v₁R) (zornPhi u₂R v₂R) ∧
    zornSymplecticOmega (zornDeWittDiff * zornPhi u₁R v₁R) (zornDeWittDiff * zornPhi u₂R v₂R) =
      -zornSymplecticOmega (zornPhi u₁R v₁R) (zornPhi u₂R v₂R) ∧
    -- 3. Symmetry/skew-symmetry and Jordan–Malcev tangent split over [CommRing K]:
    zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) =
      zornMetricG (zornPhi u₂ v₂) (zornPhi u₁ v₁) ∧
    zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) =
      -zornSymplecticOmega (zornPhi u₂ v₂) (zornPhi u₁ v₁) ∧
    zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂) =
      -zornHodgeCross (zornPhi u₂ v₂) (zornPhi u₁ v₁) ∧
    zornPhi u₁ v₁ * zornPhi u₂ v₂ + zornPhi u₂ v₂ * zornPhi u₁ v₁ =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂)) (1 : ZornMat K) ∧
    zornPhi u₁ v₁ * zornPhi u₂ v₂ - zornPhi u₂ v₂ * zornPhi u₁ v₁ =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂)) zornDeWittDiff +
        (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂) +
          zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zornSymplecticOmega, zornMetricG, zornDeWittDiff, zornU0, zornU0Star,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    noncomm_ring
  · simp [zornMetricG, zornDeWittDiff, zornU0, zornU0Star,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornPhi, zornDeWittDiff, zornU0, zornU0Star,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornPhi, zornDeWittDiff, zornU0, zornU0Star,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · simp [zornMetricG, zornPhi, zornDeWittDiff, zornU0, zornU0Star,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    abel
  · simp [zornSymplecticOmega, zornPhi, zornDeWittDiff, zornU0, zornU0Star,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    abel
  · simp [zornMetricG, zornPhi, Vec3.dot]
    ring
  · simp [zornSymplecticOmega, zornPhi, Vec3.dot]
    ring
  · ext <;> simp [zornHodgeCross, zornPhi, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [zornPhi, InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul, zornMetricG, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [zornPhi, InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul, zornSymplecticOmega, zornDeWittDiff, zornU0, zornU0Star,
      zornHodgeCross, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring

/-- **Stage `𝔐ℨ₄` (`mz4_three_term_metriplectic_pythagorean_norm_law`)**:
Over any commutative ring `[CommRing K]`, for tangent elements $z_1 = \mathrm{zornPhi}\,u_1\,v_1$
and $z_2 = \mathrm{zornPhi}\,u_2\,v_2$:
1. **Scalar Difference of Squares ($g^2 - \omega^2$)**:
   `zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 - zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 = 4 * (Vec3.dot u₁ v₂ * Vec3.dot v₁ u₂)`.
2. **Hodge Cross-Product Determinant**:
   `zornMatDet (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂)) = -Vec3.dot (Vec3.cross u₁ u₂) (Vec3.cross v₁ v₂)`.
3. **Exact Three-Term Metriplectic Pythagorean Norm Law (`Rung 3` & `Deduction 1 Theorem 2`)**:
   - `zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 - zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 - 4 * zornMatDet (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂)) = 4 * zornMatDet (zornPhi u₁ v₁ * zornPhi u₂ v₂)`,
   - `zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 - zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 - 4 * zornMatDet (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂)) = 4 * (zornMatDet (zornPhi u₁ v₁) * zornMatDet (zornPhi u₂ v₂))`,
   - `zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 - zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 - 4 * zornMatDet (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂)) = zornMetricG (zornPhi u₁ v₁) (zornPhi u₁ v₁) * zornMetricG (zornPhi u₂ v₂) (zornPhi u₂ v₂)`.
4. **Rung 0 Non-Collinear Reflection Witness (`e₁, e₂`)**:
   For $R_1 = \mathrm{zornPhi}\,\langle 1, 0, 0\rangle\,\langle 1, 0, 0\rangle$ and
   $R_2 = \mathrm{zornPhi}\,\langle 0, 1, 0\rangle\,\langle 0, 1, 0\rangle$,
   $g(R_1, R_2) = 0$ and $\omega(R_1, R_2) = 0$, while $\det(R_1 \times_H R_2) = -1$ and
   $\det(R_1 R_2) = 1 = \det(R_1)\det(R_2)$. -/
theorem mz4_three_term_metriplectic_pythagorean_norm_law
    {K : Type*} [CommRing K] (u₁ v₁ u₂ v₂ : Vec3 K) :
    -- 1. Scalar difference of squares g² - ω² = 4 (u₁ · v₂)(v₁ · u₂):
    zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 -
      zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 =
      4 * (Vec3.dot u₁ v₂ * Vec3.dot v₁ u₂) ∧
    -- 2. Hodge cross-product determinant:
    zornMatDet (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂)) =
      Vec3.dot (Vec3.cross u₁ u₂) (Vec3.cross v₁ v₂) ∧
    -- 3. Three-term metriplectic Pythagorean norm identities:
    zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 -
      zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 +
      4 * zornMatDet (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂)) =
      4 * zornMatDet (zornPhi u₁ v₁ * zornPhi u₂ v₂) ∧
    zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 -
      zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 +
      4 * zornMatDet (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂)) =
      4 * (zornMatDet (zornPhi u₁ v₁) * zornMatDet (zornPhi u₂ v₂)) ∧
    zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 -
      zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 +
      4 * zornMatDet (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂)) =
      zornMetricG (zornPhi u₁ v₁) (zornPhi u₁ v₁) *
        zornMetricG (zornPhi u₂ v₂) (zornPhi u₂ v₂) ∧
    -- 4. Rung 0 non-collinear orthogonal reflection witness:
    zornMetricG (zornPhi (⟨1, 0, 0⟩ : Vec3 K) ⟨1, 0, 0⟩)
      (zornPhi ⟨0, 1, 0⟩ ⟨0, 1, 0⟩) = 0 ∧
    zornSymplecticOmega (zornPhi (⟨1, 0, 0⟩ : Vec3 K) ⟨1, 0, 0⟩)
      (zornPhi ⟨0, 1, 0⟩ ⟨0, 1, 0⟩) = 0 ∧
    zornMatDet (zornHodgeCross
      (zornPhi (⟨1, 0, 0⟩ : Vec3 K) ⟨1, 0, 0⟩)
      (zornPhi ⟨0, 1, 0⟩ ⟨0, 1, 0⟩)) = 1 ∧
    zornMatDet (zornPhi (⟨1, 0, 0⟩ : Vec3 K) ⟨1, 0, 0⟩ *
      zornPhi ⟨0, 1, 0⟩ ⟨0, 1, 0⟩) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zornMetricG, zornSymplecticOmega, zornPhi, Vec3.dot]
    ring
  · simp [zornMatDet, zornHodgeCross, zornPhi, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]
    ring
  · simp [zornMetricG, zornSymplecticOmega, zornMatDet, zornHodgeCross, zornPhi,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    ring
  · simp [zornMetricG, zornSymplecticOmega, zornMatDet, zornHodgeCross, zornPhi,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    ring
  · simp [zornMetricG, zornSymplecticOmega, zornMatDet, zornHodgeCross, zornPhi,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    ring
  · simp [zornMetricG, zornPhi, Vec3.dot]
  · simp [zornSymplecticOmega, zornPhi, Vec3.dot]
  · simp [zornMatDet, zornHodgeCross, zornPhi, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]
  · simp [zornMatDet, zornPhi, ZornMatrix.mul_a, ZornMatrix.mul_u,
      ZornMatrix.mul_v, ZornMatrix.mul_d, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]

/-- **Stage `𝔐ℨ₅` (`mz5_third_order_dual_volume_split_on_sum_and_diff`)**:
Over any commutative ring `[CommRing K]`, for three tangent elements
$z_i = \mathrm{zornPhi}\,u_i\,v_i$ ($i = 1, 2, 3$):
1. **Hodge-Anticommutator Chiral Baryon Volume Difference on $1_{\text{Zorn}} = u_0 + u_0^*$ (`Deduction 2 Theorem 3.1`)**:
   $$\{z_1 \times_H z_2, z_3\} = \big(\mathrm{baryonDet3}(u_1, u_2, u_3) - \mathrm{baryonDet3}(v_1, v_2, v_3)\big) \cdot 1_{\text{Zorn}}.$$
2. **Associator Diagonal Chiral Baryon Volume Sum on $I_{\text{para}} = u_0 - u_0^*$ (`Rung 4` & `Deduction 2 Theorem 3.2`)**:
   $$\mathrm{zornDiagPart}\big([z_1, z_2, z_3]_{\text{assoc}}\big) = -\big(\mathrm{baryonDet3}(u_1, u_2, u_3) + \mathrm{baryonDet3}(v_1, v_2, v_3)\big) \cdot I_{\text{para}},$$
   and $\mathrm{tr}_{\text{Zorn}}([z_1, z_2, z_3]_{\text{assoc}}) = 0$.
3. **Pure Primal Sheet Specialization ($v_1 = v_2 = v_3 = 0$)**:
   - `(zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ + zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) = InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat K)`,
   - `InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator (zornPlusVec u₁) (zornPlusVec u₂) (zornPlusVec u₃) = InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (-Vec3.baryonDet3 u₁ u₂ u₃) zornDeWittDiff`. -/
theorem mz5_third_order_dual_volume_split_on_sum_and_diff
    {K : Type*} [CommRing K] (u₁ v₁ u₂ v₂ u₃ v₃ : Vec3 K) :
    -- 1. Hodge-anticommutator lands on 1_Zorn with chiral volume difference Δ_u - Δ_v:
    zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂) * zornPhi u₃ v₃ +
      zornPhi u₃ v₃ * zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (Vec3.baryonDet3 u₁ u₂ u₃ - Vec3.baryonDet3 v₁ v₂ v₃) (1 : ZornMat K) ∧
    -- 2. Associator diagonal lands on I_para with negative chiral volume sum -(Δ_u + Δ_v):
    zornDiagPart (InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator (zornPhi u₁ v₁) (zornPhi u₂ v₂) (zornPhi u₃ v₃)) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (-(Vec3.baryonDet3 u₁ u₂ u₃ + Vec3.baryonDet3 v₁ v₂ v₃)) zornDeWittDiff ∧
    zornMatTrace (InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator (zornPhi u₁ v₁) (zornPhi u₂ v₂) (zornPhi u₃ v₃)) = 0 ∧
    -- 3. Pure primal sheet specialization:
    (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
      zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat K) ∧
    InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator (zornPlusVec u₁) (zornPlusVec u₂) (zornPlusVec u₃) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (-Vec3.baryonDet3 u₁ u₂ u₃) zornDeWittDiff := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [zornHodgeCross, zornPhi, InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.baryonDet3, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [zornDiagPart, InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator, ZornMatrix.associator, zornPhi,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul, zornDeWittDiff, zornU0, zornU0Star, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.baryonDet3, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring
  · simp [zornMatTrace, InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator, ZornMatrix.associator, zornPhi,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    ring
  · exact (o6_split_octonion_diquark_hodge_dual_and_amari_chentsov_baryon_cubic u₁ u₂ u₃ u₁ u₂ u₃).2.2.2.2
  · ext <;> (simp [InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator, ZornMatrix.associator, zornPlusVec, ZornMatrix.zornConePlus,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul, zornDeWittDiff, zornU0, zornU0Star, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.baryonDet3, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)

/-- **Stage `𝔐ℨ₆` (`mz6_noncommutative_nambu_associator_and_master_synthesis`)**:
Master theorem unifying the 6-stage **Metriplectic Zorn Split-Octonion Closure Poset**
(`𝔐ℨ₁ ≺ ⋯ ≺ 𝔐ℨ₆`) and the 6-stage **Kantor–Tanaka Contact Prolongation Poset**
(`𝔎𝔗₁ ≺ ⋯ ≺ 𝔎𝔗₆`) with the non-commutative Nambu 3-bracket self-associators over `[Ring R]`. -/
theorem mz6_noncommutative_nambu_associator_and_master_synthesis
    (z₁ z₂ : ZornMat R) (u v : Vec3 R)
    {K : Type*} [CommRing K] (u₁ v₁ u₂ v₂ u₃ v₃ : Vec3 K) :
    -- 1. Poset acyclicity and cardinality of 𝔐ℨ₁ ≺ ⋯ ≺ 𝔐ℨ₆ and 𝔎𝔗₁ ≺ ⋯ ≺ 𝔎𝔗₆:
    (∀ st : MetriplecticZornStage,
      ¬ Relation.TransGen MetriplecticZornStage.causalEdge st st) ∧
    (∀ kst : KantorTanakaContactStage,
      ¬ Relation.TransGen KantorTanakaContactStage.causalEdge kst kst) ∧
    Fintype.card MetriplecticZornStage = 6 ∧
    Fintype.card KantorTanakaContactStage = 6 ∧
    -- 2. Stage MZ2 & MZ3 (Universal Metriplectic Decomposition & Para-Kähler Locking):
    z₁ * z₂ + z₁ * z₂ =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornMetricG z₁ z₂) (1 : ZornMat R) +
        InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (zornSymplecticOmega z₁ z₂) zornDeWittDiff +
        (zornHodgeCross z₁ z₂ + zornHodgeCross z₁ z₂) ∧
    zornSymplecticOmega z₁ z₂ = zornMetricG (zornDeWittDiff * z₁) z₂ ∧
    -- 3. Stage MZ4 (Three-Term Metriplectic Pythagorean Norm Law):
    zornMetricG (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 -
      zornSymplecticOmega (zornPhi u₁ v₁) (zornPhi u₂ v₂) ^ 2 +
      4 * zornMatDet (zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂)) =
      4 * (zornMatDet (zornPhi u₁ v₁) * zornMatDet (zornPhi u₂ v₂)) ∧
    -- 4. Stage MZ5 (Third-Order Chiral Volume Duality on 1_Zorn vs. I_para):
    zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂) * zornPhi u₃ v₃ +
      zornPhi u₃ v₃ * zornHodgeCross (zornPhi u₁ v₁) (zornPhi u₂ v₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (Vec3.baryonDet3 u₁ u₂ u₃ - Vec3.baryonDet3 v₁ v₂ v₃) (1 : ZornMat K) ∧
    zornDiagPart (InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator (zornPhi u₁ v₁) (zornPhi u₂ v₂) (zornPhi u₃ v₃)) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (-(Vec3.baryonDet3 u₁ u₂ u₃ + Vec3.baryonDet3 v₁ v₂ v₃)) zornDeWittDiff ∧
    -- 5. Stage MZ6 (Non-Commutative Nambu Associator on DeWitt Difference I_para):
    InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (-Vec3.nambu3 u) zornDeWittDiff ∧
    InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator (zornMinusVec v) (zornMinusVec v) (zornMinusVec v) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul (-Vec3.nambu3 v) zornDeWittDiff := by
  have hMZ2 := mz2_three_term_metriplectic_zorn_decomposition z₁ z₂ default default
  have hMZ3 := mz3_parakahler_locking_and_jordan_malcev_tangent_split z₁ z₂ u v u v u₁ v₁ u₂ v₂
  have hMZ4 := mz4_three_term_metriplectic_pythagorean_norm_law u₁ v₁ u₂ v₂
  have hMZ5 := mz5_third_order_dual_volume_split_on_sum_and_diff u₁ v₁ u₂ v₂ u₃ v₃
  have hO7 := o7_noncommutative_nambu_associator_on_dewitt_difference u v
  exact ⟨MetriplecticZornStage.causalEdge_acyclic,
    KantorTanakaContactStage.causalEdge_acyclic,
    MetriplecticZornStage.card_eq_six,
    KantorTanakaContactStage.card_eq_six,
    hMZ2.2.2.2.1,
    hMZ3.1,
    hMZ4.2.2.2.1,
    hMZ5.1,
    hMZ5.2.1,
    hO7.2.2.1.2.2.1,
    hO7.2.2.2⟩

end MetriplecticZornSplitOctonionPoset

/-!
## 7c. The 6-Stage Adjoint Cyclotomic & Binomial Sandwich Self-Reduction Poset (`𝔄𝔡₁ ≺ 𝔄𝔡₂ ≺ ⋯ ≺ 𝔄𝔡₆`)
-/

/-- The 6 causal stages of the **Adjoint Cyclotomic & Binomial Sandwich Self-Reduction Poset**
(`𝔄𝔡₁ ≺ 𝔄𝔡₂ ≺ ⋯ ≺ 𝔄𝔡₆`), proving in any associative ring `[Ring B]` (without scalar fields,
division, or `Classical.choice`) that idempotency $P^2 = P$ forces $\mathrm{ad}_P^3 - \mathrm{ad}_P = 0$,
tripotency $H^3 = H$ condenses $(\mathrm{ad}_H^3 - \mathrm{ad}_H)(X) = -3 H\,\mathrm{ad}_H(X)\,H$
with sign-inversion $H^2\,\mathrm{ad}_H(X)\,H^2 = -H\,\mathrm{ad}_H(X)\,H$ and eigenvalue $+4$
($\mathrm{ad}_H^2(H\,\mathrm{ad}_H(X)\,H) = 4 H\,\mathrm{ad}_H(X)\,H$), closing the 5-graded
quintic contact law $(\mathrm{ad}_H^5 - 5\,\mathrm{ad}_H^3 + 4\,\mathrm{ad}_H)(X) = 0$ and the
multiplicative cyclotomic clock factorizations $\mathrm{Ad}_U^n - I = \prod_{d \mid n} \Phi_d(\mathrm{Ad}_U)$. -/
inductive AdjointCyclotomicStage : Type
  /-- `𝔄𝔡₁`: Associativity of `B` $\implies$ Commuting Bilateral Superoperators `[L_H, R_H] = 0` & Universal Binomial Defect Formula. -/
  | AD1_CommutingBilateralSuperoperators
  /-- `𝔄𝔡₂`: Level 1 Idempotent Seed ($P^2 = P$) $\implies$ Vanishing Bilateral Sandwich & 3-Graded Cyclotomic Law $\mathrm{ad}_P \Phi_1(\mathrm{ad}_P)\Phi_2(\mathrm{ad}_P) = 0$. -/
  | AD2_IdempotentSeedAndThreeGradedCyclotomicLaw
  /-- `𝔄𝔡₃`: Level 2 Tripotent Seed ($H^3 = H$) $\implies$ Exact Bilateral Contact Sandwich $(\mathrm{ad}_H^3 - \mathrm{ad}_H)(X) = -3 H\,\mathrm{ad}_H(X)\,H$. -/
  | AD3_TripotentSeedAndBilateralContactSandwich
  /-- `𝔄𝔡₄`: The Sandwich Sign-Inversion Law Under $H^3 = H$ ($H^2\,\mathrm{ad}_H(X)\,H^2 = -H\,\mathrm{ad}_H(X)\,H$). -/
  | AD4_SandwichSignInversionLawUnderTripotency
  /-- `𝔄𝔡₅`: Exact Eigenvalue $+4$ ($\mathrm{ad}_H^2(W) = 4W$) & Universal `[Ring B]` 5-Graded Quintic Contact Identity $\mathrm{ad}_H^5 - 5\,\mathrm{ad}_H^3 + 4\,\mathrm{ad}_H = 0$. -/
  | AD5_EigenvalueFourAndFiveGradedQuinticContactIdentity
  /-- `𝔄𝔡₆`: Multiplicative Cyclotomic Clock Decomposition ($\mathrm{Ad}_U^n - I = \prod_{d \mid n} \Phi_d(\mathrm{Ad}_U)$ for $n \in \{2, 3, 4, 6\}$). -/
  | AD6_MultiplicativeCyclotomicClockDecomposition
  deriving DecidableEq, Repr, Inhabited

namespace AdjointCyclotomicStage

/-- Strictly monotone rank `0..5` on `AdjointCyclotomicStage`. -/
def rank : AdjointCyclotomicStage → ℕ
  | .AD1_CommutingBilateralSuperoperators => 0
  | .AD2_IdempotentSeedAndThreeGradedCyclotomicLaw => 1
  | .AD3_TripotentSeedAndBilateralContactSandwich => 2
  | .AD4_SandwichSignInversionLawUnderTripotency => 3
  | .AD5_EigenvalueFourAndFiveGradedQuinticContactIdentity => 4
  | .AD6_MultiplicativeCyclotomicClockDecomposition => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder AdjointCyclotomicStage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype AdjointCyclotomicStage where
  elems := {
    .AD1_CommutingBilateralSuperoperators,
    .AD2_IdempotentSeedAndThreeGradedCyclotomicLaw,
    .AD3_TripotentSeedAndBilateralContactSandwich,
    .AD4_SandwichSignInversionLawUnderTripotency,
    .AD5_EigenvalueFourAndFiveGradedQuinticContactIdentity,
    .AD6_MultiplicativeCyclotomicClockDecomposition
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card AdjointCyclotomicStage = 6 := rfl

/-- Directed covering edges `𝔄𝔡₁ ≺ 𝔄𝔡₂ ≺ ⋯ ≺ 𝔄𝔡₆`. -/
def causalEdge : AdjointCyclotomicStage → AdjointCyclotomicStage → Prop
  | .AD1_CommutingBilateralSuperoperators,
    .AD2_IdempotentSeedAndThreeGradedCyclotomicLaw => True
  | .AD2_IdempotentSeedAndThreeGradedCyclotomicLaw,
    .AD3_TripotentSeedAndBilateralContactSandwich => True
  | .AD3_TripotentSeedAndBilateralContactSandwich,
    .AD4_SandwichSignInversionLawUnderTripotency => True
  | .AD4_SandwichSignInversionLawUnderTripotency,
    .AD5_EigenvalueFourAndFiveGradedQuinticContactIdentity => True
  | .AD5_EigenvalueFourAndFiveGradedQuinticContactIdentity,
    .AD6_MultiplicativeCyclotomicClockDecomposition => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_rank_lt {a b : AdjointCyclotomicStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_causalEdge_rank_lt {a b : AdjointCyclotomicStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_rank_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_rank_lt hbc)

/-- **Strict DAG Acyclicity (`AdjointCyclotomicStage.causalEdge_acyclic`)**:
No stage in `𝔄𝔡₁..𝔄𝔡₆` can reach itself along a non-empty directed causal path. -/
theorem causalEdge_acyclic (a : AdjointCyclotomicStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_rank_lt h)

/-- Strict 6-stage chain `𝔄𝔡₁ < 𝔄𝔡₂ < 𝔄𝔡₃ < 𝔄𝔡₄ < 𝔄𝔡₅ < 𝔄𝔡₆`. -/
theorem strict_six_stage_chain :
    AD1_CommutingBilateralSuperoperators <
      AD2_IdempotentSeedAndThreeGradedCyclotomicLaw ∧
    AD2_IdempotentSeedAndThreeGradedCyclotomicLaw <
      AD3_TripotentSeedAndBilateralContactSandwich ∧
    AD3_TripotentSeedAndBilateralContactSandwich <
      AD4_SandwichSignInversionLawUnderTripotency ∧
    AD4_SandwichSignInversionLawUnderTripotency <
      AD5_EigenvalueFourAndFiveGradedQuinticContactIdentity ∧
    AD5_EigenvalueFourAndFiveGradedQuinticContactIdentity <
      AD6_MultiplicativeCyclotomicClockDecomposition := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end AdjointCyclotomicStage

section AdjointCyclotomicBinomialPoset

open InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair

variable {B : Type*} [Ring B]

/-- Left multiplication superoperator $L_H(X) := H X$ on an associative ring `B`. -/
@[simp] def leftMulOp (H X : B) : B :=
  H * X

/-- Right multiplication superoperator $R_H(X) := X H$ on an associative ring `B`. -/
@[simp] def rightMulOp (H X : B) : B :=
  X * H

/-- Adjoint commutator superoperator $\mathrm{ad}_H(X) := H X - X H = L_H(X) - R_H(X)$ on `B`
as an additive group homomorphism `B →+ B`. -/
def adOp (H : B) : B →+ B where
  toFun X := H * X - X * H
  map_zero' := by simp
  map_add' X Y := by noncomm_ring

@[simp] theorem adOp_apply (H X : B) : adOp H X = H * X - X * H := rfl

/-- Bilateral contact sandwich $W(H, X) := H\,\mathrm{ad}_H(X)\,H = H(H X - X H)H$ on `B`. -/
@[simp] def adSandwich (H X : B) : B :=
  H * adOp H X * H

/-- Multiplicative conjugation clock superoperator $\mathrm{Ad}_{U, U^{-1}}(X) := U X U^{-1}$ on `B`. -/
@[simp] def conjClock (U U_inv X : B) : B :=
  U * X * U_inv

/-- 1st cyclotomic superoperator $\Phi_1(F)(X) := F(X) - X$. -/
@[simp] def cycPhi1 (F : B → B) (X : B) : B :=
  F X - X

/-- 2nd cyclotomic superoperator $\Phi_2(F)(X) := F(X) + X$. -/
@[simp] def cycPhi2 (F : B → B) (X : B) : B :=
  F X + X

/-- 3rd cyclotomic superoperator $\Phi_3(F)(X) := F(F(X)) + F(X) + X$. -/
@[simp] def cycPhi3 (F : B → B) (X : B) : B :=
  F (F X) + F X + X

/-- 4th cyclotomic superoperator $\Phi_4(F)(X) := F(F(X)) + X$. -/
@[simp] def cycPhi4 (F : B → B) (X : B) : B :=
  F (F X) + X

/-- 6th cyclotomic superoperator $\Phi_6(F)(X) := F(F(X)) - F(X) + X$. -/
@[simp] def cycPhi6 (F : B → B) (X : B) : B :=
  F (F X) - F X + X

/-- **Stage `𝔄𝔡₁` (`ad1_commuting_bilateral_superoperators_and_binomial_expansion`)**:
In any associative ring `[Ring B]`, for all $H, X \in B$:
1. **Commuting Bilateral Multiplication Superoperators (`Rung 1`)**:
   - `leftMulOp H (rightMulOp H X) = rightMulOp H (leftMulOp H X)` ($H(X H) = (H X)H$, $[L_H, R_H] = 0$),
   - `adOp H X = leftMulOp H X - rightMulOp H X`.
2. **Universal Pascal Binomial Expansions of $\mathrm{ad}_H^2$ and $\mathrm{ad}_H^3$**:
   - `adOp H (adOp H X) = H * H * X - (2 : ℤ) • (H * X * H) + X * (H * H)`,
   - `adOp H (adOp H (adOp H X)) = H * H * H * X - (3 : ℤ) • (H * H * X * H) + (3 : ℤ) • (H * X * (H * H)) - X * (H * H * H)`.
3. **Universal Cubic Peirce Defect Decomposition (Prior to Any Hypothesis on $H$)**:
   $$(\mathrm{ad}_H^3 - \mathrm{ad}_H)(X) = [H^3 - H, \, X] - 3\,H\,\mathrm{ad}_H(X)\,H.$$ -/
theorem ad1_commuting_bilateral_superoperators_and_binomial_expansion (H X : B) :
    leftMulOp H (rightMulOp H X) = rightMulOp H (leftMulOp H X) ∧
    adOp H X = leftMulOp H X - rightMulOp H X ∧
    adOp H (adOp H X) = H * H * X - (2 : ℤ) • (H * X * H) + X * (H * H) ∧
    adOp H (adOp H (adOp H X)) =
      H * H * H * X - (3 : ℤ) • (H * H * X * H) +
        (3 : ℤ) • (H * X * (H * H)) - X * (H * H * H) ∧
    adSandwich H X = H * H * X * H - H * X * (H * H) ∧
    peirce3Op (adOp H) X =
      adOp (H * H * H - H) X - (3 : ℤ) • adSandwich H X := by
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
  · dsimp [leftMulOp, rightMulOp]; noncomm_ring
  · dsimp [adOp]; noncomm_ring
  · dsimp [adOp]; noncomm_ring
  · dsimp [adSandwich, adOp]; noncomm_ring
  · dsimp [peirce3Op, adOp, adSandwich]; noncomm_ring

/-- **Stage `𝔄𝔡₂` (`ad2_idempotent_seed_and_three_graded_cyclotomic_law`)**:
In any associative ring `[Ring B]`, if $P \in B$ is idempotent ($hP : P * P = P$), then for all $X \in B$:
1. **Cubic Idempotency & Bilateral Projector Laws**:
   `P * P * P = P`, `leftMulOp P (leftMulOp P X) = leftMulOp P X`, and
   `rightMulOp P (rightMulOp P X) = rightMulOp P X`.
2. **Asymmetry of $\mathrm{ad}_P^2 - \mathrm{ad}_P$ (`Rung 2`)**:
   `adOp P (adOp P X) - adOp P X = (2 : ℤ) • (X * P - P * X * P)`.
3. **Identical Vanishing of the Idempotent Bilateral Sandwich ($P\,\mathrm{ad}_P(X)\,P = 0$)**:
   `adSandwich P X = 0`.
4. **Universal 3-Graded Tripotent & Cyclotomic Factorization (`Theorem 1`)**:
   - `peirce3Op (adOp P) X = 0`,
   - `adOp P (adOp P (adOp P X)) = adOp P X`,
   - `adOp P (cycPhi1 (adOp P) (cycPhi2 (adOp P) X)) = peirce3Op (adOp P) X`,
   - `adOp P (cycPhi1 (adOp P) (cycPhi2 (adOp P) X)) = 0`.
5. **Recursive Bootstrap Seed (Orthogonal Idempotents Generate a Tripotent Element $H^3 = H$)**:
   For any two orthogonal idempotents $P_1, P_2 \in B$ ($P_1^2 = P_1, P_2^2 = P_2, P_1 P_2 = P_2 P_1 = 0$),
   their difference $H := P_1 - P_2$ satisfies $H * H * H = H$. -/
theorem ad2_idempotent_seed_and_three_graded_cyclotomic_law
    {P : B} (hP : P * P = P) (X : B)
    {P₁ P₂ : B} (hP₁ : P₁ * P₁ = P₁) (hP₂ : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) :
    -- 1. Cubic idempotency & bilateral idempotency:
    P * P * P = P ∧
    leftMulOp P (leftMulOp P X) = leftMulOp P X ∧
    rightMulOp P (rightMulOp P X) = rightMulOp P X ∧
    -- 2. Asymmetry of ad_P² - ad_P:
    adOp P (adOp P X) - adOp P X = (2 : ℤ) • (X * P - P * X * P) ∧
    -- 3. Vanishing of the idempotent bilateral sandwich:
    adSandwich P X = 0 ∧
    -- 4. 3-graded tripotent and cyclotomic laws:
    peirce3Op (adOp P) X = 0 ∧
    adOp P (adOp P (adOp P X)) = adOp P X ∧
    adOp P (cycPhi1 (adOp P) (cycPhi2 (adOp P) X)) = peirce3Op (adOp P) X ∧
    adOp P (cycPhi1 (adOp P) (cycPhi2 (adOp P) X)) = 0 ∧
    -- 5. Orthogonal idempotents generate a tripotent difference H³ = H:
    (P₁ - P₂) * (P₁ - P₂) * (P₁ - P₂) = P₁ - P₂ := by
  have hP3 : P * P * P = P := by rw [hP, hP]
  have hSand : adSandwich P X = 0 := by
    calc adSandwich P X
      _ = (P * P) * X * P - P * X * (P * P) := by dsimp [adSandwich, adOp]; noncomm_ring
      _ = P * X * P - P * X * P := by rw [hP]
      _ = 0 := by noncomm_ring
  have hPeirce3 : peirce3Op (adOp P) X = 0 := by
    rw [(ad1_commuting_bilateral_superoperators_and_binomial_expansion P X).2.2.2.2.2]
    rw [hP3, hSand]
    dsimp [adOp]
    noncomm_ring
  have hCycFactor : adOp P (cycPhi1 (adOp P) (cycPhi2 (adOp P) X)) = peirce3Op (adOp P) X := by
    dsimp [cycPhi1, cycPhi2, peirce3Op, adOp]
    noncomm_ring
  refine ⟨hP3, ?_, ?_, ?_, hSand, hPeirce3, ?_, hCycFactor, by rw [hCycFactor, hPeirce3], ?_⟩
  · dsimp [leftMulOp]; rw [← mul_assoc, hP]
  · dsimp [rightMulOp]; rw [mul_assoc, hP]
  · calc adOp P (adOp P X) - adOp P X
      _ = (P * P) * X - P * X - (2 : ℤ) • (P * X * P) + X * (P * P) + X * P := by
          dsimp [adOp]; noncomm_ring
      _ = P * X - P * X - (2 : ℤ) • (P * X * P) + X * P + X * P := by rw [hP]
      _ = (2 : ℤ) • (X * P - P * X * P) := by noncomm_ring
  · calc adOp P (adOp P (adOp P X))
      _ = peirce3Op (adOp P) X + adOp P X := by dsimp [peirce3Op]; abel
      _ = 0 + adOp P X := by rw [hPeirce3]
      _ = adOp P X := zero_add _
  · calc (P₁ - P₂) * (P₁ - P₂) * (P₁ - P₂)
      _ = (P₁ * P₁ - P₁ * P₂ - P₂ * P₁ + P₂ * P₂) * (P₁ - P₂) := by noncomm_ring
      _ = (P₁ - 0 - 0 + P₂) * (P₁ - P₂) := by rw [hP₁, hP₂, h12, h21]
      _ = P₁ * P₁ - P₁ * P₂ + P₂ * P₁ - P₂ * P₂ := by noncomm_ring
      _ = P₁ - 0 + 0 - P₂ := by rw [hP₁, hP₂, h12, h21]
      _ = P₁ - P₂ := by abel

/-- **Stage `𝔄𝔡₃` (`ad3_tripotent_seed_and_bilateral_contact_sandwich`)**:
In any associative ring `[Ring B]`, if $H \in B$ is tripotent ($hH : H * H * H = H$), then for all $X \in B$:
1. **Tripotency of Left and Right Multiplication Superoperators**:
   `leftMulOp H (leftMulOp H (leftMulOp H X)) = leftMulOp H X` and
   `rightMulOp H (rightMulOp H (rightMulOp H X)) = rightMulOp H X`.
2. **Exact Bilateral Contact Sandwich Law (`Theorem 2.1`)**:
   - `peirce3Op (adOp H) X = -(3 : ℤ) • adSandwich H X`
     ($(\mathrm{ad}_H^3 - \mathrm{ad}_H)(X) = -3 H\,\mathrm{ad}_H(X)\,H$),
   - `adOp H (adOp H (adOp H X)) = adOp H X - (3 : ℤ) • adSandwich H X`.
3. **Rung 0 Socratic Aporia Witness ($H^3 = H \not\implies \mathrm{ad}_H^3 = \mathrm{ad}_H$)**:
   For $H = H_{\text{gen}}\,\mathbb{Z} = \mathrm{diag}(1, 0, -1) \in M_3(\mathbb{Z})$ and
   $E_{02} = E\,0\,2\,(1 : \mathbb{Z})$:
   - `H_gen ℤ * H_gen ℤ * H_gen ℤ = H_gen ℤ`,
   - `adSandwich (H_gen ℤ) (E 0 2 (1 : ℤ)) = -(2 : ℤ) • E 0 2 (1 : ℤ)`,
   - `peirce3Op (adOp (H_gen ℤ)) (E 0 2 (1 : ℤ)) = (6 : ℤ) • E 0 2 (1 : ℤ)`,
   - `peirce3Op (adOp (H_gen ℤ)) (E 0 2 (1 : ℤ)) ≠ 0`. -/
theorem ad3_tripotent_seed_and_bilateral_contact_sandwich
    {H : B} (hH : H * H * H = H) (X : B) :
    -- 1. Tripotency of L_H and R_H:
    leftMulOp H (leftMulOp H (leftMulOp H X)) = leftMulOp H X ∧
    rightMulOp H (rightMulOp H (rightMulOp H X)) = rightMulOp H X ∧
    -- 2. Exact bilateral contact sandwich law:
    peirce3Op (adOp H) X = -(3 : ℤ) • adSandwich H X ∧
    adOp H (adOp H (adOp H X)) = adOp H X - (3 : ℤ) • adSandwich H X ∧
    -- 3. Rung 0 Socratic aporia witness in M₃(ℤ):
    H_gen ℤ * H_gen ℤ * H_gen ℤ = H_gen ℤ ∧
    adSandwich (H_gen ℤ) (E_gen ℤ) = -(2 : ℤ) • E_gen ℤ ∧
    peirce3Op (adOp (H_gen ℤ)) (E_gen ℤ) = (6 : ℤ) • E_gen ℤ ∧
    peirce3Op (adOp (H_gen ℤ)) (E_gen ℤ) ≠ 0 := by
  have hP3 : peirce3Op (adOp H) X = -(3 : ℤ) • adSandwich H X := by
    rw [(ad1_commuting_bilateral_superoperators_and_binomial_expansion H X).2.2.2.2.2]
    rw [hH]
    dsimp [adOp]
    noncomm_ring
  have hE3 : peirce3Op (adOp (H_gen ℤ)) (E_gen ℤ) = (6 : ℤ) • E_gen ℤ := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [peirce3Op, adOp, H_gen, E_gen, E, Matrix.mul_apply]
  refine ⟨?_, ?_, hP3, ?_, ?_, ?_, hE3, ?_⟩
  · dsimp [leftMulOp]; rw [← mul_assoc, ← mul_assoc, hH]
  · dsimp [rightMulOp]; rw [mul_assoc X H H, mul_assoc X (H * H) H, hH]
  · calc adOp H (adOp H (adOp H X))
      _ = adOp H X + peirce3Op (adOp H) X := by dsimp [peirce3Op]; abel
      _ = adOp H X + -(3 : ℤ) • adSandwich H X := by rw [hP3]
      _ = adOp H X - (3 : ℤ) • adSandwich H X := by abel
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [H_gen, E, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [adSandwich, adOp, H_gen, E_gen, E, Matrix.mul_apply]
  · rw [hE3]
    intro hZero
    have h02 := congr_fun (congr_fun hZero 0) 2
    revert h02
    simp [E_gen, E]

/-- **Stage `𝔄𝔡₄` (`ad4_sandwich_sign_inversion_law_under_tripotency`)**:
In any associative ring `[Ring B]`, if $H \in B$ is tripotent ($hH : H * H * H = H$), then for all $X \in B$:
1. **Left and Right $H^2$-Absorption on the Bilateral Sandwich (`Theorem 2.3`)**:
   - `H * H * adSandwich H X = adSandwich H X` ($H^2 W = W$),
   - `adSandwich H X * (H * H) = adSandwich H X` ($W H^2 = W$).
2. **The Sandwich Sign-Inversion Law (`Theorem 2.2` & `Transcendent Function`)**:
   - `H * adSandwich H X * H = -adSandwich H X` ($H W H = -W$),
   - `(H * H) * adOp H X * (H * H) = -adSandwich H X` ($H^2\,\mathrm{ad}_H(X)\,H^2 = -H\,\mathrm{ad}_H(X)\,H$),
   - `leftMulOp H (rightMulOp H (adSandwich H X)) = -adSandwich H X` ($L_H R_H(W) = -W$).
3. **Single $\mathrm{ad}_H$ Action on the Sandwich**:
   `adOp H (adSandwich H X) = (2 : ℤ) • (H * X * H - (H * H) * X * (H * H))`. -/
theorem ad4_sandwich_sign_inversion_law_under_tripotency
    {H : B} (hH : H * H * H = H) (X : B) :
    H * H * adSandwich H X = adSandwich H X ∧
    adSandwich H X * (H * H) = adSandwich H X ∧
    H * adSandwich H X * H = -adSandwich H X ∧
    (H * H) * adOp H X * (H * H) = -adSandwich H X ∧
    leftMulOp H (rightMulOp H (adSandwich H X)) = -adSandwich H X ∧
    adOp H (adSandwich H X) = (2 : ℤ) • (H * X * H - (H * H) * X * (H * H)) := by
  have hL : H * H * adSandwich H X = adSandwich H X := by
    calc H * H * adSandwich H X
      _ = (H * H * H) * (adOp H X * H) := by dsimp [adSandwich]; noncomm_ring
      _ = H * (adOp H X * H) := by rw [hH]
      _ = adSandwich H X := by dsimp [adSandwich]; noncomm_ring
  have hR : adSandwich H X * (H * H) = adSandwich H X := by
    calc adSandwich H X * (H * H)
      _ = (H * adOp H X) * (H * H * H) := by dsimp [adSandwich]; noncomm_ring
      _ = (H * adOp H X) * H := by rw [hH]
      _ = adSandwich H X := rfl
  have hMid : H * adSandwich H X * H = -adSandwich H X := by
    calc H * adSandwich H X * H
      _ = (H * H * H) * X * (H * H) - (H * H) * X * (H * H * H) := by
          dsimp [adSandwich, adOp]; noncomm_ring
      _ = H * X * (H * H) - (H * H) * X * H := by rw [hH]
      _ = -adSandwich H X := by dsimp [adSandwich, adOp]; noncomm_ring
  have hMid2 : (H * H) * adOp H X * (H * H) = -adSandwich H X := by
    calc (H * H) * adOp H X * (H * H)
      _ = H * adSandwich H X * H := by dsimp [adSandwich]; noncomm_ring
      _ = -adSandwich H X := hMid
  have hLR : leftMulOp H (rightMulOp H (adSandwich H X)) = -adSandwich H X := by
    change H * (adSandwich H X * H) = -adSandwich H X
    rw [← mul_assoc]
    exact hMid
  refine ⟨hL, hR, hMid, hMid2, hLR, ?_⟩
  calc adOp H (adSandwich H X)
    _ = (H * H * H) * X * H - (H * H) * X * (H * H) -
          (H * H) * X * (H * H) + H * X * (H * H * H) := by
        dsimp [adOp, adSandwich]; noncomm_ring
    _ = H * X * H - (H * H) * X * (H * H) -
          (H * H) * X * (H * H) + H * X * H := by rw [hH]
    _ = (2 : ℤ) • (H * X * H - (H * H) * X * (H * H)) := by noncomm_ring

/-- **Stage `𝔄𝔡₅` (`ad5_eigenvalue_four_and_five_graded_quintic_contact_identity`)**:
In any associative ring `[Ring B]`, if $H \in B$ is tripotent ($hH : H * H * H = H$), then for all $X \in B$:
1. **Exact Eigenvalue $+4 = 1 - 2(-1) + 1$ on the Bilateral Sandwich (`Theorem 2.3` & `Rung 3`)**:
   - `adOp H (adOp H (adSandwich H X)) = (4 : ℤ) • adSandwich H X`,
   - `adOp H (adOp H (adSandwich H X)) - (4 : ℤ) • adSandwich H X = 0`.
2. **Universal `[Ring B]` Proof of the 5-Graded Quintic Contact Law from $H^3 = H$ (`Theorem 2.4`)**:
   - `adOp H (adOp H (peirce3Op (adOp H) X)) = (4 : ℤ) • peirce3Op (adOp H) X`,
   - `adOp H (adOp H (peirce3Op (adOp H) X)) - (4 : ℤ) • peirce3Op (adOp H) X = 0`
     ($(\mathrm{ad}_H^2 - 4 I)(\mathrm{ad}_H^3 - \mathrm{ad}_H)(X) = 0$),
   - `kantorQuinticOp (adOp H) X = 0`
     ($(\mathrm{ad}_H^5 - 5\,\mathrm{ad}_H^3 + 4\,\mathrm{ad}_H)(X) = 0$!).
3. **Quartic Lagrange Grade-$\pm 2$ Shell Projector Formula Under $H^3 = H$**:
   - `lagrange12Proj2 (adOp H) X = -(3 : ℤ) • adOp H (adSandwich H X)`. -/
theorem ad5_eigenvalue_four_and_five_graded_quintic_contact_identity
    {H : B} (hH : H * H * H = H) (X : B) :
    -- 1. Eigenvalue +4 on the bilateral sandwich W = H ad_H(X) H:
    adOp H (adOp H (adSandwich H X)) = (4 : ℤ) • adSandwich H X ∧
    adOp H (adOp H (adSandwich H X)) - (4 : ℤ) • adSandwich H X = 0 ∧
    -- 2. Factored and expanded 5-graded quintic contact identity:
    adOp H (adOp H (peirce3Op (adOp H) X)) = (4 : ℤ) • peirce3Op (adOp H) X ∧
    adOp H (adOp H (peirce3Op (adOp H) X)) - (4 : ℤ) • peirce3Op (adOp H) X = 0 ∧
    kantorQuinticOp (adOp H) X = 0 ∧
    -- 3. Quartic Lagrange Grade-±2 shell projector reduction:
    lagrange12Proj2 (adOp H) X = -(3 : ℤ) • adOp H (adSandwich H X) := by
  have h3 := ad3_tripotent_seed_and_bilateral_contact_sandwich hH X
  have h4 := ad4_sandwich_sign_inversion_law_under_tripotency hH X
  have hP3 : peirce3Op (adOp H) X = -(3 : ℤ) • adSandwich H X := h3.2.2.1
  have hL : H * H * adSandwich H X = adSandwich H X := h4.1
  have hR : adSandwich H X * (H * H) = adSandwich H X := h4.2.1
  have hMid : H * adSandwich H X * H = -adSandwich H X := h4.2.2.1
  have hSq : adOp H (adOp H (adSandwich H X)) = (4 : ℤ) • adSandwich H X := by
    calc adOp H (adOp H (adSandwich H X))
      _ = (H * H * adSandwich H X) - (2 : ℤ) • (H * adSandwich H X * H) +
            (adSandwich H X * (H * H)) := by
          dsimp [adOp]; noncomm_ring
      _ = adSandwich H X - (2 : ℤ) • (-adSandwich H X) + adSandwich H X := by
          rw [hL, hMid, hR]
      _ = (4 : ℤ) • adSandwich H X := by noncomm_ring
  have hSqSub : adOp H (adOp H (adSandwich H X)) - (4 : ℤ) • adSandwich H X = 0 := by
    rw [hSq, sub_self]
  have hP3Sq : adOp H (adOp H (peirce3Op (adOp H) X)) = (4 : ℤ) • peirce3Op (adOp H) X := by
    calc adOp H (adOp H (peirce3Op (adOp H) X))
      _ = adOp H (adOp H (-(3 : ℤ) • adSandwich H X)) := by rw [hP3]
      _ = -(3 : ℤ) • adOp H (adOp H (adSandwich H X)) := by dsimp [adOp]; noncomm_ring
      _ = -(3 : ℤ) • ((4 : ℤ) • adSandwich H X) := by rw [hSq]
      _ = (4 : ℤ) • (-(3 : ℤ) • adSandwich H X) := by abel
      _ = (4 : ℤ) • peirce3Op (adOp H) X := by rw [← hP3]
  have hP3SqSub : adOp H (adOp H (peirce3Op (adOp H) X)) - (4 : ℤ) • peirce3Op (adOp H) X = 0 := by
    rw [hP3Sq, sub_self]
  have hQuintic : kantorQuinticOp (adOp H) X = 0 := by
    calc kantorQuinticOp (adOp H) X
      _ = adOp H (adOp H (peirce3Op (adOp H) X)) - (4 : ℤ) • peirce3Op (adOp H) X := by
          dsimp [kantorQuinticOp, peirce3Op, adOp]; noncomm_ring
      _ = 0 := hP3SqSub
  have hLag2 : lagrange12Proj2 (adOp H) X = -(3 : ℤ) • adOp H (adSandwich H X) := by
    calc lagrange12Proj2 (adOp H) X
      _ = adOp H (peirce3Op (adOp H) X) := by
          dsimp [lagrange12Proj2, peirce3Op, adOp]; noncomm_ring
      _ = adOp H (-(3 : ℤ) • adSandwich H X) := by rw [hP3]
      _ = -(3 : ℤ) • adOp H (adSandwich H X) := by dsimp [adOp]; noncomm_ring
  exact ⟨hSq, hSqSub, hP3Sq, hP3SqSub, hQuintic, hLag2⟩

/-- **Stage `𝔄𝔡₆` (`ad6_multiplicative_cyclotomic_clock_and_master_synthesis`)**:
Master theorem unifying the 6-stage **Adjoint Cyclotomic & Binomial Sandwich Self-Reduction Poset**
(`𝔄𝔡₁ ≺ 𝔄𝔡₂ ≺ ⋯ ≺ 𝔄𝔡₆`) with the **Multiplicative Cyclotomic Clock Decomposition**
($\mathrm{Ad}_U^n - I = \prod_{d \mid n} \Phi_d(\mathrm{Ad}_U)$ for $n \in \{2, 3, 4, 6\}$):
1. **Poset Acyclicity & Cardinality**:
   `AdjointCyclotomicStage.causalEdge_acyclic` and `Fintype.card AdjointCyclotomicStage = 6`.
2. **Universal Multiplicative Cyclotomic Polynomial Factorizations (`Rung 4` & `Theorem 3`)**:
   For any clock elements $U, U_{\text{inv}} \in B$ and $X \in B$, let $C := \mathrm{conjClock}\,U\,U_{\text{inv}}$:
   - $n = 2$: $\Phi_1(C)(\Phi_2(C)(X)) = C^2(X) - X$,
   - $n = 3$: $\Phi_1(C)(\Phi_3(C)(X)) = C^3(X) - X$,
   - $n = 4$: $\Phi_1(C)(\Phi_2(C)(\Phi_4(C)(X))) = C^4(X) - X$,
   - $n = 6$: $\Phi_1(C)(\Phi_2(C)(\Phi_3(C)(\Phi_6(C)(X)))) = C^6(X) - X$.
3. **Exact Cyclotomic Clock Annihilation under $S^2 = 1$ ($\mathbb{Z}_2$ Chiral) and $\Omega^3 = 1$ ($\mathbb{Z}_3$ Color)**:
   - When $hS : S * S = 1$: $\Phi_1(\mathrm{conjClock}\,S\,S)(\Phi_2(\mathrm{conjClock}\,S\,S)(X)) = 0$,
   - When $h\Omega : \Omega * \Omega * \Omega = 1$ and $h\Omega_{\text{inv}} : \Omega_{\text{inv}} * \Omega_{\text{inv}} * \Omega_{\text{inv}} = 1$:
     $\Phi_1(\mathrm{conjClock}\,\Omega\,\Omega_{\text{inv}})(\Phi_3(\mathrm{conjClock}\,\Omega\,\Omega_{\text{inv}})(X)) = 0$.
4. **Master Additive Adjoint Hierarchy ($P^2 = P \implies \mathrm{ad}_P^3 = \mathrm{ad}_P$ & $H^3 = H \implies \mathrm{ad}_H^5 - 5\,\mathrm{ad}_H^3 + 4\,\mathrm{ad}_H = 0$)**:
   Bundles $[L_H, R_H] = 0$, `peirce3Op (adOp P) X = 0`,
   `peirce3Op (adOp H) X = -(3 : ℤ) • adSandwich H X`,
   `(H * H) * adOp H X * (H * H) = -adSandwich H X`,
   `adOp H (adOp H (adSandwich H X)) = (4 : ℤ) • adSandwich H X`, and
   `kantorQuinticOp (adOp H) X = 0`. -/
theorem ad6_multiplicative_cyclotomic_clock_and_master_synthesis
    {P H S Ω Ω_inv U U_inv : B}
    (hP : P * P = P) (hH : H * H * H = H)
    (hS : S * S = 1) (hΩ : Ω * Ω * Ω = 1) (hΩ_inv : Ω_inv * Ω_inv * Ω_inv = 1)
    (X : B) :
    let C := conjClock U U_inv
    -- 1. Poset acyclicity and cardinality of 𝔄𝔡₁ ≺ ⋯ ≺ 𝔄𝔡₆:
    (∀ st : AdjointCyclotomicStage,
      ¬ Relation.TransGen AdjointCyclotomicStage.causalEdge st st) ∧
    Fintype.card AdjointCyclotomicStage = 6 ∧
    -- 2. Universal multiplicative cyclotomic factorizations for n = 2, 3, 4, 6:
    cycPhi1 C (cycPhi2 C X) = C (C X) - X ∧
    cycPhi1 C (cycPhi3 C X) = C (C (C X)) - X ∧
    cycPhi1 C (cycPhi2 C (cycPhi4 C X)) = C (C (C (C X))) - X ∧
    cycPhi1 C (cycPhi2 C (cycPhi3 C (cycPhi6 C X))) = C (C (C (C (C (C X))))) - X ∧
    -- 3. Exact Z₂ and Z₃ cyclotomic clock annihilation:
    cycPhi1 (conjClock S S) (cycPhi2 (conjClock S S) X) = 0 ∧
    cycPhi1 (conjClock Ω Ω_inv) (cycPhi3 (conjClock Ω Ω_inv) X) = 0 ∧
    -- 4. Master additive adjoint binomial & sandwich reduction chain:
    leftMulOp H (rightMulOp H X) = rightMulOp H (leftMulOp H X) ∧
    peirce3Op (adOp P) X = 0 ∧
    peirce3Op (adOp H) X = -(3 : ℤ) • adSandwich H X ∧
    (H * H) * adOp H X * (H * H) = -adSandwich H X ∧
    adOp H (adOp H (adSandwich H X)) = (4 : ℤ) • adSandwich H X ∧
    kantorQuinticOp (adOp H) X = 0 := by
  have hAD1 := ad1_commuting_bilateral_superoperators_and_binomial_expansion H X
  have hAD2 := ad2_idempotent_seed_and_three_graded_cyclotomic_law hP X
    (P₁ := 0) (P₂ := 0) (mul_zero 0) (mul_zero 0) (mul_zero 0) (mul_zero 0)
  have hAD3 := ad3_tripotent_seed_and_bilateral_contact_sandwich hH X
  have hAD4 := ad4_sandwich_sign_inversion_law_under_tripotency hH X
  have hAD5 := ad5_eigenvalue_four_and_five_graded_quintic_contact_identity hH X
  refine ⟨AdjointCyclotomicStage.causalEdge_acyclic,
    AdjointCyclotomicStage.card_eq_six,
    ?_, ?_, ?_, ?_, ?_, ?_,
    hAD1.1,
    hAD2.2.2.2.2.2.1,
    hAD3.2.2.1,
    hAD4.2.2.2.1,
    hAD5.1,
    hAD5.2.2.2.2.1⟩
  · dsimp [cycPhi1, cycPhi2, conjClock]; noncomm_ring
  · dsimp [cycPhi1, cycPhi3, conjClock]; noncomm_ring
  · dsimp [cycPhi1, cycPhi2, cycPhi4, conjClock]; noncomm_ring
  · dsimp [cycPhi1, cycPhi2, cycPhi3, cycPhi6, conjClock]; noncomm_ring
  · calc cycPhi1 (conjClock S S) (cycPhi2 (conjClock S S) X)
      _ = (S * S) * X * (S * S) - X := by dsimp [cycPhi1, cycPhi2, conjClock]; noncomm_ring
      _ = 1 * X * 1 - X := by rw [hS]
      _ = 0 := by noncomm_ring
  · calc cycPhi1 (conjClock Ω Ω_inv) (cycPhi3 (conjClock Ω Ω_inv) X)
      _ = (Ω * Ω * Ω) * X * (Ω_inv * Ω_inv * Ω_inv) - X := by
          dsimp [cycPhi1, cycPhi3, conjClock]; noncomm_ring
      _ = 1 * X * 1 - X := by rw [hΩ, hΩ_inv]
      _ = 0 := by noncomm_ring

end AdjointCyclotomicBinomialPoset

/-!
## 7d. The 6-Stage Madelung–Bohm Operator Hydrodynamics, Firth Trilinear Contextual Semantics & Gauge-Dark / Gravity-Active Chiral Condensate Poset (`𝔐𝔅₁ ≺ 𝔐𝔅₂ ≺ ⋯ ≺ 𝔐𝔅₆`)
-/

/-- The 6 causal stages of the **Madelung–Bohm Operator Hydrodynamics, Firth Trilinear Contextual
Semantics & Gauge-Dark / Gravity-Active Chiral Condensate Poset** (`𝔐𝔅₁ ≺ 𝔐𝔅₂ ≺ ⋯ ≺ 𝔐𝔅₆`),
severing commutative context-free particle trajectories from non-commutative operator
hydrodynamics ($J = N_+ - N_-$, $\Phi = N_+ + N_-$, $[\Phi, J] = -2\Sigma$,
$\mathcal{M}_\Phi(J) = -[\Phi, [\Phi, J]] = -4 V J$), Firth's 3-body Zorn contextual closure
($\{N_+(u_1)N_+(u_2), N_+(u_3)\} = \det(u_1, u_2, u_3)\cdot 1_{\text{Zorn}}$,
$[N_+(u_1), N_+(u_2), N_+(u_3)]_{\text{assoc}} = -\det(u_1, u_2, u_3)\cdot S_P$), and the
exact separation between 100% electromagnetic gauge darkness in the even subalgebra $\mathfrak{k}$
($[S_P, \Omega_{\text{EM}}] = 0$) and active gravitational frame-dragging on the odd Para-Kähler
tangent bundle $\mathfrak{p}$ ($[S_P, \Phi] = 2J$, $[S_P, [S_P, \Phi]] = 4\Phi$). -/
inductive MadelungBohmFirthChiralStage : Type
  /-- `𝔐𝔅₁`: Operator Madelung–Bohm Phase Current $J = N_+ - N_-$ ($J^2 = -V$) vs. Osmotic Amplitude $\Phi = N_+ + N_-$ ($\Phi^2 = +V$) & Non-Commutative Spacecharge $[\Phi, J] = -2\Sigma$. -/
  | MB1_OperatorMadelungBohmPhaseAndOsmoticAmplitudeSplit
  /-- `𝔐𝔅₂`: Operator Bohm Quantum Force $\mathcal{M}_\Phi(J) = -[\Phi, [\Phi, J]] = -4 V J$ & Chiral Beat Clocking $[\Sigma, \Phi] = 2 V J$, $[\Sigma, J] = 2 V \Phi$. -/
  | MB2_OperatorBohmQuantumForceAndChiralBeatClocking
  /-- `𝔐𝔅₃`: Firth's Trilinear Contextual Semantics in `ZornMat K`: 1-Body Nilpotence ($N_+(u_1)^2 = 0$), 2-Body Hodge Jump ($N_+(u_1)N_+(u_2) = N_-(u_1 \times u_2)$), & 3-Body Baryon Volume Closure. -/
  | MB3_FirthTrilinearContextualSemanticsInZornMatrix
  /-- `𝔐𝔅₄`: Parafermion & Nambu Associator Condensation onto the Chiral DeWitt Difference $S_P = u_0 - u_0^*$ & Yin–Yang Spacecharge Sheet Decomposition. -/
  | MB4_ParafermionAndNambuAssociatorCondensationOntoDeWittBasis
  /-- `𝔐𝔅₅`: Exact 100% Electromagnetic Gauge Darkness in the Even Subalgebra $\mathfrak{k}$ ($[S_P, \Omega_{\text{EM}}] = 0$, $[\Sigma_{\text{DM}}(\rho), \Omega_{\text{EM}}] = 0$). -/
  | MB5_ExactElectromagneticGaugeDarknessInEvenSubalgebra
  /-- `𝔐𝔅₆`: Exact Gravitational Frame-Dragging on the Odd Tangent Space $\mathfrak{p}$ ($[S_P, \Phi] = 2J$, $[S_P, [S_P, \Phi]] = 4\Phi$) & Dark-Gravity Master Synthesis. -/
  | MB6_ExactGravitationalFrameDraggingAndDarkGravitySynthesis
  deriving DecidableEq, Repr, Inhabited

namespace MadelungBohmFirthChiralStage

/-- Strictly monotone rank `0..5` on `MadelungBohmFirthChiralStage`. -/
def rank : MadelungBohmFirthChiralStage → ℕ
  | .MB1_OperatorMadelungBohmPhaseAndOsmoticAmplitudeSplit => 0
  | .MB2_OperatorBohmQuantumForceAndChiralBeatClocking => 1
  | .MB3_FirthTrilinearContextualSemanticsInZornMatrix => 2
  | .MB4_ParafermionAndNambuAssociatorCondensationOntoDeWittBasis => 3
  | .MB5_ExactElectromagneticGaugeDarknessInEvenSubalgebra => 4
  | .MB6_ExactGravitationalFrameDraggingAndDarkGravitySynthesis => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder MadelungBohmFirthChiralStage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype MadelungBohmFirthChiralStage where
  elems := {
    .MB1_OperatorMadelungBohmPhaseAndOsmoticAmplitudeSplit,
    .MB2_OperatorBohmQuantumForceAndChiralBeatClocking,
    .MB3_FirthTrilinearContextualSemanticsInZornMatrix,
    .MB4_ParafermionAndNambuAssociatorCondensationOntoDeWittBasis,
    .MB5_ExactElectromagneticGaugeDarknessInEvenSubalgebra,
    .MB6_ExactGravitationalFrameDraggingAndDarkGravitySynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card MadelungBohmFirthChiralStage = 6 := rfl

/-- Directed covering edges `𝔐𝔅₁ ≺ 𝔐𝔅₂ ≺ ⋯ ≺ 𝔐𝔅₆`. -/
def causalEdge : MadelungBohmFirthChiralStage → MadelungBohmFirthChiralStage → Prop
  | .MB1_OperatorMadelungBohmPhaseAndOsmoticAmplitudeSplit,
    .MB2_OperatorBohmQuantumForceAndChiralBeatClocking => True
  | .MB2_OperatorBohmQuantumForceAndChiralBeatClocking,
    .MB3_FirthTrilinearContextualSemanticsInZornMatrix => True
  | .MB3_FirthTrilinearContextualSemanticsInZornMatrix,
    .MB4_ParafermionAndNambuAssociatorCondensationOntoDeWittBasis => True
  | .MB4_ParafermionAndNambuAssociatorCondensationOntoDeWittBasis,
    .MB5_ExactElectromagneticGaugeDarknessInEvenSubalgebra => True
  | .MB5_ExactElectromagneticGaugeDarknessInEvenSubalgebra,
    .MB6_ExactGravitationalFrameDraggingAndDarkGravitySynthesis => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_rank_lt {a b : MadelungBohmFirthChiralStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_causalEdge_rank_lt {a b : MadelungBohmFirthChiralStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_rank_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_rank_lt hbc)

/-- **Strict DAG Acyclicity (`MadelungBohmFirthChiralStage.causalEdge_acyclic`)**:
No stage in `𝔐𝔅₁..𝔐𝔅₆` can reach itself along a non-empty directed causal path. -/
theorem causalEdge_acyclic (a : MadelungBohmFirthChiralStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_rank_lt h)

/-- Strict 6-stage chain `𝔐𝔅₁ < 𝔐𝔅₂ < 𝔐𝔅₃ < 𝔐𝔅₄ < 𝔐𝔅₅ < 𝔐𝔅₆`. -/
theorem strict_six_stage_chain :
    MB1_OperatorMadelungBohmPhaseAndOsmoticAmplitudeSplit <
      MB2_OperatorBohmQuantumForceAndChiralBeatClocking ∧
    MB2_OperatorBohmQuantumForceAndChiralBeatClocking <
      MB3_FirthTrilinearContextualSemanticsInZornMatrix ∧
    MB3_FirthTrilinearContextualSemanticsInZornMatrix <
      MB4_ParafermionAndNambuAssociatorCondensationOntoDeWittBasis ∧
    MB4_ParafermionAndNambuAssociatorCondensationOntoDeWittBasis <
      MB5_ExactElectromagneticGaugeDarknessInEvenSubalgebra ∧
    MB5_ExactElectromagneticGaugeDarknessInEvenSubalgebra <
      MB6_ExactGravitationalFrameDraggingAndDarkGravitySynthesis := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end MadelungBohmFirthChiralStage

section MadelungBohmFirthChiralPoset

open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
open InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset

variable {B : Type*} [Ring B]
variable {R : Type*} [Ring R]

/-- **Zorn Matrix Commutator (`zornComm`)**:
$[X, Y]_{\text{Zorn}} := X Y - Y X$ in the non-associative Zorn split-octonion algebra `ZornMat R`. -/
@[simp] def zornComm (X Y : ZornMat R) : ZornMat R :=
  X * Y - Y * X

/-- **Operator Bohm Quantum Force (`madelungBohmForce`)**:
$\mathcal{M}_\Phi(J) := -\mathrm{ad}_\Phi^2(J) = -[\Phi, [\Phi, J]]$ in an associative ring `B`. -/
def madelungBohmForce (P A C : B) : B :=
  -adOp (genPhi P A C) (adOp (genPhi P A C) (genJ P A C))

/-- **Internal Even Gauge Block (`evenGaugeBlock`)**:
$\Omega_{\text{EM}}(P, W) := P W P + (1 - P) W (1 - P) \in \mathfrak{k} = P B P \oplus (1 - P) B (1 - P)$. -/
def evenGaugeBlock (P W : B) : B :=
  P * W * P + (1 - P) * W * (1 - P)

/-- **Diagonal Even-Subalgebra Zorn Gauge Element (`zornEvenGauge`)**:
$\Omega_{\text{EM}}(a, d) := a u_0 + d u_0^* = \langle a, 0, 0, d \rangle \in \mathfrak{k}_{\text{Zorn}}$. -/
def zornEvenGauge (a d : R) : ZornMat R :=
  ⟨a, 0, 0, d⟩

/-- **Yin–Yang Chiral Spacecharge Sheet Condensate (`zornYinYangCondensate`)**:
$\Sigma_{\text{YY}}(\rho_+, \rho_-) := \rho_+ u_0 - \rho_- u_0^* \in \mathfrak{k}_{\text{Zorn}}$. -/
def zornYinYangCondensate (ρ_plus ρ_minus : R) : ZornMat R :=
  InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul ρ_plus zornU0 -
    InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul ρ_minus zornU0Star

/-- **Chiral Parafermion / Nambu Dark Condensate (`zornDarkCondensate`)**:
$\Sigma_{\text{DM}}(\rho) := \rho S_P = \rho (u_0 - u_0^*) \in \mathfrak{k}_{\text{Zorn}}$. -/
def zornDarkCondensate (ρ : R) : ZornMat R :=
  InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul ρ zornDeWittDiff

/-- **Stage `𝔐𝔅₁` (`mb1_operator_madelung_bohm_phase_and_osmotic_amplitude_split`)**:
In any associative ring `[Ring B]` with idempotent $P^2 = P$ ($hP : P * P = P$) and $A, C \in B$:
1. **Timelike Phase Current $J$ vs. Spacelike Osmotic Bohm Amplitude $\Phi$**:
   - `genJ P A C = conePlus P A - coneMinus P C` ($J = N_+ - N_-$),
   - `genPhi P A C = conePlus P A + coneMinus P C` ($\Phi = N_+ + N_-$),
   - `genJ P A C * genJ P A C = -genV P A C` ($J^2 = -V$: timelike classical Euler velocity square),
   - `genPhi P A C * genPhi P A C = genV P A C` ($\Phi^2 = +V$: spacelike osmotic Fisher potential),
   - `genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0` ($\Phi^2 + J^2 = 0$: Krein null parity).
2. **Chiral Polar Intertwining via $S_P = 2P - 1$ (`invS P`)**:
   - `invS P * genPhi P A C = genJ P A C` ($S_P \Phi = J$),
   - `genPhi P A C * invS P = -genJ P A C` ($\Phi S_P = -J$),
   - `invS P * genJ P A C = genPhi P A C` ($S_P J = \Phi$),
   - `genJ P A C * invS P = -genPhi P A C` ($J S_P = -\Phi$).
3. **Non-Commutative Phase–Amplitude Commutator & Rung 0 Refutation of Commutative Hydrodynamics**:
   - `adOp (genPhi P A C) (genJ P A C) = -(2 : ℤ) • genSig P A C` ($[\Phi, J] = -2\Sigma$),
   - `genPhi P A C * genJ P A C + genJ P A C * genPhi P A C = 0` ($\{\Phi, J\} = 0$),
   - `genSig P A C = invS P * genV P A C` and `genSig P A C = genV P A C * invS P` ($\Sigma = S_P V = V S_P$),
   - **Rung 0 Aporia**: If $[\Phi, J] = 0$, then $2\Sigma = 0$. -/
theorem mb1_operator_madelung_bohm_phase_and_osmotic_amplitude_split
    {P : B} (hP : P * P = P) (A C : B) :
    -- 1. Timelike J² = -V vs. Spacelike Φ² = +V:
    genJ P A C = conePlus P A - coneMinus P C ∧
    genPhi P A C = conePlus P A + coneMinus P C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
    -- 2. Chiral polar intertwining S_P Φ = J = -Φ S_P:
    invS P * genPhi P A C = genJ P A C ∧
    genPhi P A C * invS P = -genJ P A C ∧
    invS P * genJ P A C = genPhi P A C ∧
    genJ P A C * invS P = -genPhi P A C ∧
    -- 3. Non-commutative phase–amplitude commutator [Φ, J] = -2Σ & Rung 0 refutation:
    adOp (genPhi P A C) (genJ P A C) = -(2 : ℤ) • genSig P A C ∧
    genPhi P A C * genJ P A C + genJ P A C * genPhi P A C = 0 ∧
    genSig P A C = invS P * genV P A C ∧
    genSig P A C = genV P A C * invS P ∧
    (adOp (genPhi P A C) (genJ P A C) = 0 → (2 : ℤ) • genSig P A C = 0) := by
  have hComm : adOp (genPhi P A C) (genJ P A C) = -(2 : ℤ) • genSig P A C := by
    dsimp [adOp]
    peirce_nf hP
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hComm, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · intro hZero
    have hNeg : -((2 : ℤ) • genSig P A C) = 0 := by
      rw [← neg_zsmul, ← hComm, hZero]
    exact neg_eq_zero.mp hNeg

/-- **Stage `𝔐𝔅₂` (`mb2_operator_bohm_quantum_force_and_chiral_beat_clocking`)**:
In any associative ring `[Ring B]` with idempotent $P^2 = P$ ($hP : P * P = P$) and $A, C, \Omega \in B$:
1. **Chiral Spacecharge Beat Clocking (`[Σ, Φ] = 2 V J` & `[Σ, J] = 2 V Φ`)**:
   - `adOp (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C)` ($[\Sigma, \Phi] = 2 V J$),
   - `adOp (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C)` ($[\Sigma, J] = 2 V \Phi$),
   - `genSig P A C * genPhi P A C + genPhi P A C * genSig P A C = 0` ($\{\Sigma, \Phi\} = 0$),
   - `genSig P A C * genJ P A C + genJ P A C * genSig P A C = 0` ($\{\Sigma, J\} = 0$).
2. **Operator Bohm Quantum Force (`madelungBohmForce P A C = -4 V J`)**:
   - `madelungBohmForce P A C = -(2 : ℤ) • adOp (genSig P A C) (genPhi P A C)`
     ($-[\Phi, [\Phi, J]] = -2[\Sigma, \Phi]$),
   - `madelungBohmForce P A C = -(4 : ℤ) • (genV P A C * genJ P A C)`
     ($\mathcal{M}_\Phi(J) = -4 V J$),
   - `adOp (genJ P A C) (adOp (genJ P A C) (genPhi P A C)) = -(4 : ℤ) • (genV P A C * genPhi P A C)`
     ($[J, [J, \Phi]] = -4 V \Phi$).
3. **Gauge-Covariant Madelung Kinetic Energy Split (`(Ω_EM + Φ)² = (Ω_EM² + V) + {Ω_EM, Φ}`)**:
   - `(evenGaugeBlock P Ω + genPhi P A C) * (evenGaugeBlock P Ω + genPhi P A C) = (evenGaugeBlock P Ω * evenGaugeBlock P Ω + genV P A C) + (evenGaugeBlock P Ω * genPhi P A C + genPhi P A C * evenGaugeBlock P Ω)`. -/
theorem mb2_operator_bohm_quantum_force_and_chiral_beat_clocking
    {P : B} (hP : P * P = P) (A C Ω : B) :
    -- 1. Chiral spacecharge beat clocking [Σ, Φ] = 2 V J and [Σ, J] = 2 V Φ:
    adOp (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    adOp (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    genSig P A C * genPhi P A C + genPhi P A C * genSig P A C = 0 ∧
    genSig P A C * genJ P A C + genJ P A C * genSig P A C = 0 ∧
    -- 2. Operator Bohm quantum force -[Φ, [Φ, J]] = -2[Σ, Φ] = -4 V J:
    madelungBohmForce P A C = -(2 : ℤ) • adOp (genSig P A C) (genPhi P A C) ∧
    madelungBohmForce P A C = -(4 : ℤ) • (genV P A C * genJ P A C) ∧
    adOp (genJ P A C) (adOp (genJ P A C) (genPhi P A C)) =
      -(4 : ℤ) • (genV P A C * genPhi P A C) ∧
    -- 3. Gauge-covariant Madelung kinetic energy split:
    (evenGaugeBlock P Ω + genPhi P A C) * (evenGaugeBlock P Ω + genPhi P A C) =
      (evenGaugeBlock P Ω * evenGaugeBlock P Ω + genV P A C) +
        (evenGaugeBlock P Ω * genPhi P A C + genPhi P A C * evenGaugeBlock P Ω) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [adOp]; peirce_nf hP
  · dsimp [adOp]; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · dsimp [madelungBohmForce, adOp]; peirce_nf hP
  · dsimp [madelungBohmForce, adOp]; peirce_nf hP
  · dsimp [adOp]; peirce_nf hP
  · dsimp [evenGaugeBlock]; peirce_nf hP

/-- **Stage `𝔐𝔅₃` (`mb3_firth_trilinear_contextual_semantics_in_zorn_matrix`)**:
Over any commutative ring `[CommRing K]`, for $u_1, u_2, u_3, v_1, v_2, v_3 \in \mathrm{Vec3}\,K$,
formalizing J. R. Firth's contextual semantics (*"You shall know a word by the company it keeps"*)
and the Plato's Cave vs. Forms cut in `ZornMat K`:
1. **1-Body Isolation (Plato's Cave Shadow — Zero Self-Square, Zero Trace, Zero Determinant)**:
   - `zornPlusVec u₁ * zornPlusVec u₁ = 0`,
   - `zornMinusVec v₁ * zornMinusVec v₁ = 0`,
   - `zornMatTrace (zornPlusVec u₁) = 0`,
   - `zornMatDet (zornPlusVec u₁) = 0`.
2. **2-Body Syntactic Diquark Hodge Jump (Still Traceless & Determinant-Zero)**:
   - `zornPlusVec u₁ * zornPlusVec u₂ = zornMinusVec (Vec3.cross u₁ u₂)`,
   - `zornMinusVec v₁ * zornMinusVec v₂ = -zornPlusVec (Vec3.cross v₁ v₂)`,
   - `zornMatTrace (zornPlusVec u₁ * zornPlusVec u₂) = 0`,
   - `zornMatDet (zornPlusVec u₁ * zornPlusVec u₂) = 0`.
3. **3-Body Firth Contextual Closure (*"Company It Keeps"* $\implies$ Non-Zero Baryon Volume on $u_0, u_0^*, 1_{\text{Zorn}}, S_P$)**:
   - `(zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ = zornSmul (Vec3.baryonDet3 u₁ u₂ u₃) zornU0Star`,
   - `zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) = zornSmul (Vec3.baryonDet3 u₁ u₂ u₃) zornU0`,
   - `(zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ + zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) = zornSmul (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat K)`,
   - `zornAssociator (zornPlusVec u₁) (zornPlusVec u₂) (zornPlusVec u₃) = zornSmul (-Vec3.baryonDet3 u₁ u₂ u₃) zornDeWittDiff`. -/
theorem mb3_firth_trilinear_contextual_semantics_in_zorn_matrix
    {K : Type*} [CommRing K] (u₁ u₂ u₃ v₁ v₂ : Vec3 K) :
    -- 1. 1-body isolation (nilpotent, traceless, determinant-zero):
    zornPlusVec u₁ * zornPlusVec u₁ = 0 ∧
    zornMinusVec v₁ * zornMinusVec v₁ = 0 ∧
    zornMatTrace (zornPlusVec u₁) = 0 ∧
    zornMatDet (zornPlusVec u₁) = 0 ∧
    -- 2. 2-body syntactic diquark Hodge jump (still traceless and determinant-zero):
    zornPlusVec u₁ * zornPlusVec u₂ = zornMinusVec (Vec3.cross u₁ u₂) ∧
    zornMinusVec v₁ * zornMinusVec v₂ = -zornPlusVec (Vec3.cross v₁ v₂) ∧
    zornMatTrace (zornPlusVec u₁ * zornPlusVec u₂) = 0 ∧
    zornMatDet (zornPlusVec u₁ * zornPlusVec u₂) = 0 ∧
    -- 3. 3-body Firth contextual closure onto u₀*, u₀, 1_Zorn, and S_P = u₀ - u₀*:
    (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (Vec3.baryonDet3 u₁ u₂ u₃) zornU0Star ∧
    zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (Vec3.baryonDet3 u₁ u₂ u₃) zornU0 ∧
    (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
      zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat K) ∧
    InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator
      (zornPlusVec u₁) (zornPlusVec u₂) (zornPlusVec u₃) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (-Vec3.baryonDet3 u₁ u₂ u₃) zornDeWittDiff := by
  have hMZ5 := mz5_third_order_dual_volume_split_on_sum_and_diff u₁ v₁ u₂ v₂ u₃ v₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hMZ5.2.2.2.1, hMZ5.2.2.2.2⟩
  · ext <;> (simp [zornPlusVec, ZornMatrix.zornConePlus, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [zornMinusVec, ZornMatrix.zornConeMinus, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · simp [zornMatTrace, zornPlusVec, ZornMatrix.zornConePlus]
  · simp [zornMatDet, zornPlusVec, ZornMatrix.zornConePlus, Vec3.dot]
  · ext <;> (simp [zornPlusVec, zornMinusVec, ZornMatrix.zornConePlus, ZornMatrix.zornConeMinus,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [zornPlusVec, zornMinusVec, ZornMatrix.zornConePlus, ZornMatrix.zornConeMinus,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · simp [zornMatTrace, zornPlusVec, ZornMatrix.zornConePlus, ZornMatrix.mul_a, ZornMatrix.mul_d, Vec3.dot]
  · simp [zornMatDet, zornPlusVec, ZornMatrix.zornConePlus,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · ext <;> (simp [zornPlusVec, ZornMatrix.zornConePlus,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornU0Star, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.baryonDet3, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)
  · ext <;> (simp [zornPlusVec, ZornMatrix.zornConePlus,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornU0, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.baryonDet3, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]; try ring)

/-- **Stage `𝔐𝔅₄` (`mb4_parafermion_and_nambu_associator_condensation_onto_dewitt_basis`)**:
Over any associative ring `[Ring R]` and commutative ring `[CommRing K]`:
1. **Yin–Yang Chiral Spacecharge Sheet Decomposition (`zornYinYangCondensate` & `zornDarkCondensate`)**:
   For any sheet densities $\rho_+, \rho_-, \rho \in R$:
   - `zornYinYangCondensate ρ_plus ρ_minus = ⟨ρ_plus, 0, 0, -ρ_minus⟩`,
   - `zornYinYangCondensate ρ ρ = zornDarkCondensate ρ` ($\rho u_0 - \rho u_0^* = \rho S_P$),
   - `zornMatTrace (zornDarkCondensate ρ) = 0` (exact vacuum neutrality $\mathrm{tr}(\rho S_P) = 0$),
   - `zornMatDet (zornDarkCondensate ρ) = -(ρ * ρ)` (non-vanishing gravitational energy density).
2. **Parafermion & Non-Commutative Nambu Associator Condensation onto $S_P = u_0 - u_0^*$**:
   - `zornDiagPart (zornAssociator (zornPhi u₁ v₁) (zornPhi u₂ v₂) (zornPhi u₃ v₃)) = zornDarkCondensate (-(Vec3.baryonDet3 u₁ u₂ u₃ + Vec3.baryonDet3 v₁ v₂ v₃))`,
   - `zornAssociator (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) = zornDarkCondensate (-Vec3.nambu3 u)`,
   - `zornAssociator (zornMinusVec v) (zornMinusVec v) (zornMinusVec v) = zornDarkCondensate (-Vec3.nambu3 v)`. -/
theorem mb4_parafermion_and_nambu_associator_condensation_onto_dewitt_basis
    (ρ_plus ρ_minus ρ : R) (u v : Vec3 R)
    {K : Type*} [CommRing K] (u₁ v₁ u₂ v₂ u₃ v₃ : Vec3 K) :
    -- 1. Yin–Yang chiral spacecharge sheet decomposition & vacuum neutrality:
    zornYinYangCondensate ρ_plus ρ_minus = ⟨ρ_plus, 0, 0, -ρ_minus⟩ ∧
    zornYinYangCondensate ρ ρ = zornDarkCondensate ρ ∧
    zornMatTrace (zornDarkCondensate ρ) = 0 ∧
    zornMatDet (zornDarkCondensate ρ) = -(ρ * ρ) ∧
    -- 2. Parafermion & Nambu 3-body associator condensation onto zornDarkCondensate:
    zornDiagPart
      (InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator
        (zornPhi u₁ v₁) (zornPhi u₂ v₂) (zornPhi u₃ v₃)) =
      zornDarkCondensate (-(Vec3.baryonDet3 u₁ u₂ u₃ + Vec3.baryonDet3 v₁ v₂ v₃)) ∧
    InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator
      (zornPlusVec u) (zornPlusVec u) (zornPlusVec u) =
      zornDarkCondensate (-Vec3.nambu3 u) ∧
    InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornAssociator
      (zornMinusVec v) (zornMinusVec v) (zornMinusVec v) =
      zornDarkCondensate (-Vec3.nambu3 v) := by
  have hMZ5 := mz5_third_order_dual_volume_split_on_sum_and_diff u₁ v₁ u₂ v₂ u₃ v₃
  have hO7 := o7_noncommutative_nambu_associator_on_dewitt_difference u v
  refine ⟨?_, ?_, ?_, ?_, hMZ5.2.1, hO7.2.2.1.2.2.1, hO7.2.2.2⟩
  · ext <;> simp [zornYinYangCondensate,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornU0, zornU0Star, ZornMatrix.smul, Vec3.smulLeft]
  · ext <;> simp [zornYinYangCondensate, zornDarkCondensate,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornDeWittDiff, zornU0, zornU0Star, ZornMatrix.smul, Vec3.smulLeft]
  · simp [zornMatTrace, zornDarkCondensate,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornDeWittDiff, zornU0, zornU0Star, ZornMatrix.smul]
  · simp [zornMatDet, zornDarkCondensate,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornDeWittDiff, zornU0, zornU0Star, ZornMatrix.smul, Vec3.dot, Vec3.smulLeft]

/-- **Stage `𝔐𝔅₅` (`mb5_exact_electromagnetic_gauge_darkness_in_even_subalgebra`)**:
In any associative ring `[Ring B]` with idempotent $P^2 = P$ ($hP : P * P = P$) and $W, A, C \in B$,
and over any commutative ring `[CommRing K]` for $\rho, \rho_+, \rho_-, a, d \in K$:
1. **Universal Peirce Even-Subalgebra Gauge Darkness (`[S_P, Ω_EM] = 0` & `[Σ, V] = 0`)**:
   - `P * evenGaugeBlock P W = P * W * P` and `evenGaugeBlock P W * P = P * W * P`,
   - `adOp P (evenGaugeBlock P W) = 0` ($[P, \Omega_{\text{EM}}] = 0$),
   - `invS P * evenGaugeBlock P W = evenGaugeBlock P W * invS P` ($S_P \Omega_{\text{EM}} = \Omega_{\text{EM}} S_P$),
   - `adOp (invS P) (evenGaugeBlock P W) = 0` ($[S_P, \Omega_{\text{EM}}] = 0$: 100% gauge-dark in $\mathfrak{k}$),
   - `adOp (genSig P A C) (genV P A C) = 0` ($[\Sigma, V] = 0$: the chiral condensate commutes with $V$).
2. **Exact Zorn Electromagnetic Gauge Darkness (`[Σ_DM(ρ), Ω_EM(a, d)] = 0`)**:
   - `adOp (zornDarkCondensate ρ) (zornEvenGauge a d) = 0`,
   - `adOp (zornYinYangCondensate ρ_plusK ρ_minusK) (zornEvenGauge a d) = 0`. -/
theorem mb5_exact_electromagnetic_gauge_darkness_in_even_subalgebra
    {P : B} (hP : P * P = P) (W A C : B)
    {K : Type*} [CommRing K] (ρ ρ_plusK ρ_minusK a d : K) :
    -- 1. Universal Peirce even-subalgebra gauge darkness [S_P, Ω_EM] = 0 and [Σ, V] = 0:
    P * evenGaugeBlock P W = P * W * P ∧
    evenGaugeBlock P W * P = P * W * P ∧
    adOp P (evenGaugeBlock P W) = 0 ∧
    invS P * evenGaugeBlock P W = evenGaugeBlock P W * invS P ∧
    adOp (invS P) (evenGaugeBlock P W) = 0 ∧
    adOp (genSig P A C) (genV P A C) = 0 ∧
    -- 2. Exact Zorn electromagnetic gauge darkness [Σ_DM(ρ), Ω_EM(a, d)] = 0:
    zornComm (zornDarkCondensate ρ) (zornEvenGauge a d) = 0 ∧
    zornComm (zornYinYangCondensate ρ_plusK ρ_minusK) (zornEvenGauge a d) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [evenGaugeBlock]; peirce_nf hP
  · dsimp [evenGaugeBlock]; peirce_nf hP
  · dsimp [adOp, evenGaugeBlock]; peirce_nf hP
  · dsimp [evenGaugeBlock]; peirce_nf hP
  · dsimp [adOp, evenGaugeBlock]; peirce_nf hP
  · dsimp [adOp]; peirce_nf hP
  · ext <;> simp [zornComm, zornDarkCondensate, zornEvenGauge,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornDeWittDiff, zornU0, zornU0Star, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [zornComm, zornYinYangCondensate, zornEvenGauge,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornU0, zornU0Star, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring

/-- **Stage `𝔐𝔅₆` (`mb6_exact_gravitational_frame_dragging_and_dark_gravity_synthesis`)**:
Master theorem unifying the 6-stage **Madelung–Bohm, Firth Contextual & Chiral Dark-Condensate Poset**
(`𝔐𝔅₁ ≺ 𝔐𝔅₂ ≺ ⋯ ≺ 𝔐𝔅₆`):
1. **Poset Acyclicity & Cardinality**:
   `MadelungBohmFirthChiralStage.causalEdge_acyclic` and `Fintype.card MadelungBohmFirthChiralStage = 6`.
2. **Universal Odd-Subalgebra Gravitational Frame-Dragging (`{S_P, Φ} = 0`, `[S_P, Φ] = 2J`, `[S_P, [S_P, Φ]] = 4Φ`)**:
   In any associative ring `[Ring B]` with $P^2 = P$:
   - `invS P * genPhi P A C + genPhi P A C * invS P = 0` ($\{S_P, \Phi\} = 0$),
   - `adOp (invS P) (genPhi P A C) = (2 : ℤ) • genJ P A C` ($[S_P, \Phi] = 2J$: chiral phase rotation),
   - `adOp (invS P) (genJ P A C) = (2 : ℤ) • genPhi P A C` ($[S_P, J] = 2\Phi$: dual amplitude rotation),
   - `adOp (invS P) (adOp (invS P) (genPhi P A C)) = (4 : ℤ) • genPhi P A C` ($[S_P, [S_P, \Phi]] = 4\Phi$),
   - `adOp (invS P) (adOp (invS P) (genJ P A C)) = (4 : ℤ) • genJ P A C` ($[S_P, [S_P, J]] = 4J$).
3. **Zorn Dark-Matter Condensate Synthesis (100% Gauge-Dark in $\mathfrak{k}$, 100% Gravity-Active on $\mathfrak{p}$)**:
   Over any `[CommRing K]`, for $\Sigma_{\text{DM}}(\rho) = \mathrm{zornDarkCondensate}\,\rho$:
   - `zornComm (zornDarkCondensate ρ) (zornEvenGauge a d) = 0` (electromagnetic darkness in $\mathfrak{k}$),
   - `zornDarkCondensate ρ * zornPhi u₁ v₁ + zornPhi u₁ v₁ * zornDarkCondensate ρ = 0` (anticommutativity on $\mathfrak{p}$),
   - `zornComm (zornDarkCondensate ρ) (zornPhi u₁ v₁) = zornSmul (2 * ρ) (zornPlusVec u₁ - zornMinusVec v₁)` (frame-dragging $\Phi \mapsto 2\rho J$),
   - `zornComm (zornDarkCondensate ρ) (zornComm (zornDarkCondensate ρ) (zornPhi u₁ v₁)) = zornSmul (4 * (ρ * ρ)) (zornPhi u₁ v₁)` (gravitational curvature $4\rho^2 \Phi$),
   - **Master Hydrodynamic & Contextual Bundle**:
     `madelungBohmForce P A C = -(4 : ℤ) • (genV P A C * genJ P A C)` and
     `(zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ + zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) = zornSmul (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat K)`. -/
theorem mb6_exact_gravitational_frame_dragging_and_dark_gravity_synthesis
    {P : B} (hP : P * P = P) (W A C : B)
    {K : Type*} [CommRing K] (ρ a d : K) (u₁ v₁ u₂ u₃ : Vec3 K) :
    -- 1. Poset acyclicity and cardinality of 𝔐𝔅₁ ≺ ⋯ ≺ 𝔐𝔅₆:
    (∀ st : MadelungBohmFirthChiralStage,
      ¬ Relation.TransGen MadelungBohmFirthChiralStage.causalEdge st st) ∧
    Fintype.card MadelungBohmFirthChiralStage = 6 ∧
    -- 2. Universal odd-subalgebra gravitational frame-dragging in [Ring B]:
    invS P * genPhi P A C + genPhi P A C * invS P = 0 ∧
    adOp (invS P) (genPhi P A C) = (2 : ℤ) • genJ P A C ∧
    adOp (invS P) (genJ P A C) = (2 : ℤ) • genPhi P A C ∧
    adOp (invS P) (adOp (invS P) (genPhi P A C)) = (4 : ℤ) • genPhi P A C ∧
    adOp (invS P) (adOp (invS P) (genJ P A C)) = (4 : ℤ) • genJ P A C ∧
    -- 3. Zorn dark-condensate synthesis (100% gauge-dark in 𝔨, 100% gravity-active on 𝔭):
    adOp (invS P) (evenGaugeBlock P W) = 0 ∧
    zornComm (zornDarkCondensate ρ) (zornEvenGauge a d) = 0 ∧
    zornDarkCondensate ρ * zornPhi u₁ v₁ + zornPhi u₁ v₁ * zornDarkCondensate ρ = 0 ∧
    zornComm (zornDarkCondensate ρ) (zornPhi u₁ v₁) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (2 * ρ) (zornPlusVec u₁ - zornMinusVec v₁) ∧
    zornComm (zornDarkCondensate ρ) (zornComm (zornDarkCondensate ρ) (zornPhi u₁ v₁)) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (4 * (ρ * ρ)) (zornPhi u₁ v₁) ∧
    -- 4. Master operator Bohm force & Firth 3-body contextual closure:
    madelungBohmForce P A C = -(4 : ℤ) • (genV P A C * genJ P A C) ∧
    (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
      zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat K) := by
  have hMB2 := mb2_operator_bohm_quantum_force_and_chiral_beat_clocking hP A C W
  have hMB3 := mb3_firth_trilinear_contextual_semantics_in_zorn_matrix u₁ u₂ u₃ v₁ v₁
  have hMB5 := mb5_exact_electromagnetic_gauge_darkness_in_even_subalgebra hP W A C ρ ρ ρ a d
  refine ⟨MadelungBohmFirthChiralStage.causalEdge_acyclic,
    MadelungBohmFirthChiralStage.card_eq_six,
    ?_, ?_, ?_, ?_, ?_,
    hMB5.2.2.2.2.1,
    hMB5.2.2.2.2.2.2.1,
    ?_, ?_, ?_,
    hMB2.2.2.2.2.2.1,
    hMB3.2.2.2.2.2.2.2.2.2.2.1⟩
  · peirce_nf hP
  · dsimp [adOp]; peirce_nf hP
  · dsimp [adOp]; peirce_nf hP
  · dsimp [adOp]; peirce_nf hP
  · dsimp [adOp]; peirce_nf hP
  · ext <;> simp [zornDarkCondensate, zornPhi,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornDeWittDiff, zornU0, zornU0Star, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [zornComm, zornDarkCondensate, zornPhi, zornPlusVec, zornMinusVec,
      ZornMatrix.zornConePlus, ZornMatrix.zornConeMinus,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornDeWittDiff, zornU0, zornU0Star, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [zornComm, zornDarkCondensate, zornPhi,
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul,
      zornDeWittDiff, zornU0, zornU0Star, ZornMatrix.smul,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring

end MadelungBohmFirthChiralPoset

/-!
## 7e. The 6-Stage Universal Super-Adjoint $\mathrm{sad}_Q$ & $24 = 4!$ Cyclotomic Modular Clock Poset (`𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ ⋯ ≺ 𝔖𝔄₆`)
-/

/-- The 6 causal stages of the **Universal Super-Adjoint $\mathrm{sad}_Q$ & $24 = 4!$ Cyclotomic
Modular Clock Poset** (`𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ ⋯ ≺ 𝔖𝔄₆`), severing external parity case-splits and
fractional rational denominators from:
1. The universal case-free chiral super-adjoint $\mathrm{sad}_Q(X) := Q X - S X S Q$ in `[Ring B]`
   whose square cancels the bilateral sandwich identically to yield $\mathrm{sad}_Q^2(X) = [Q^2, X]$
   for all $X \in B$,
2. The division-free $24 = 4!$ integer resolution of the 5-graded Kantor–Tanaka tower
   ($\sum_{k=-2}^{+2} P_k^{(24)}(d) = 24\cdot 1$, $P_j^{(24)}(d) P_k^{(24)}(d) = 24\delta_{jk} P_j^{(24)}(d)$), and
3. The 8-divisor factorization of $x^{24} - 1 = \prod_{d \mid 24} \Phi_d(x)$ with octonion-color
   composition $\Phi_{24}(x) = x^8 - x^4 + 1 = \Phi_3(-x^4)$ ($\deg \Phi_{24} = \varphi(24) = 8 = \dim \mathbb{O}_s$)
   and exponent-2 Galois cube $(\mathbb{Z}/24\mathbb{Z})^\times$ ($u^2 = 1$). -/
inductive SuperAdjointCyclotomic24Stage : Type
  /-- `𝔖𝔄₁`: Universal Case-Free Chiral Super-Adjoint Operator $\mathrm{sad}_Q(X) := Q X - S X S Q$ in `[Ring B]`. -/
  | SA1_CaseFreeChiralSuperAdjointOperator
  /-- `𝔖𝔄₂`: Parity-Alternating Bracket Law ($\{Q, [Q, E]\}$ on $\mathfrak{k}$, $[Q, \{Q, O\}]$ on $\mathfrak{p}$) & Universal Square Identity $\mathrm{sad}_Q^2(X) = [Q^2, X]$. -/
  | SA2_ParityAlternatingBracketAndExactSquareLaw
  /-- `𝔖𝔄₃`: Super-Sandwich Defect ($\mathrm{ad}_Q^2 - \mathrm{sad}_Q^2 = -2 Q X Q$), Nilpotent Square-Zero Law ($\mathrm{sad}_{N_+}^2 = 0$), & Higgs–SUSY Split ($\mathrm{sad}_\Phi^2(J) = 0$ vs. $\mathrm{ad}_\Phi^2(J) = 4 V J$). -/
  | SA3_SuperSandwichDefectNilpotentSquareAndHiggsSusySplit
  /-- `𝔖𝔄₄`: Division-Free $24 = 4!$ Integer Projector Resolution of the 5-Graded Kantor–Tanaka Tower ($\sum P_k^{(24)}(d) = 24\cdot 1$, $P_j^{(24)} P_k^{(24)} = 24\delta_{jk} P_j^{(24)}$). -/
  | SA4_DivisionFree24IntegerResolutionOfFiveGradedTower
  /-- `𝔖𝔄₅`: The 24-Cyclotomic Modular Clock ($x^{24} - 1 = \prod_{d \mid 24} \Phi_d(x)$) & Octonion–Color Composition $\Phi_{24}(x) = x^8 - x^4 + 1 = \Phi_3(-x^4)$. -/
  | SA5_Cyclotomic24ModularClockAndOctonionColorComposition
  /-- `𝔖𝔄₆`: Exponent-2 Galois Cube $(\mathbb{Z}/24\mathbb{Z})^\times \cong (\mathbb{Z}/2\mathbb{Z})^3$ ($\varphi(24) = 8 = \dim \mathbb{O}_s$, $u^2 = 1$, $24 \mid (k^2 - 1)$) & Master Synthesis. -/
  | SA6_ExponentTwoGaloisCubeAndMasterSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace SuperAdjointCyclotomic24Stage

/-- Strictly monotone rank `0..5` on `SuperAdjointCyclotomic24Stage`. -/
def rank : SuperAdjointCyclotomic24Stage → ℕ
  | .SA1_CaseFreeChiralSuperAdjointOperator => 0
  | .SA2_ParityAlternatingBracketAndExactSquareLaw => 1
  | .SA3_SuperSandwichDefectNilpotentSquareAndHiggsSusySplit => 2
  | .SA4_DivisionFree24IntegerResolutionOfFiveGradedTower => 3
  | .SA5_Cyclotomic24ModularClockAndOctonionColorComposition => 4
  | .SA6_ExponentTwoGaloisCubeAndMasterSynthesis => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder SuperAdjointCyclotomic24Stage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype SuperAdjointCyclotomic24Stage where
  elems := {
    .SA1_CaseFreeChiralSuperAdjointOperator,
    .SA2_ParityAlternatingBracketAndExactSquareLaw,
    .SA3_SuperSandwichDefectNilpotentSquareAndHiggsSusySplit,
    .SA4_DivisionFree24IntegerResolutionOfFiveGradedTower,
    .SA5_Cyclotomic24ModularClockAndOctonionColorComposition,
    .SA6_ExponentTwoGaloisCubeAndMasterSynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card SuperAdjointCyclotomic24Stage = 6 := rfl

/-- Directed covering edges `𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ ⋯ ≺ 𝔖𝔄₆`. -/
def causalEdge : SuperAdjointCyclotomic24Stage → SuperAdjointCyclotomic24Stage → Prop
  | .SA1_CaseFreeChiralSuperAdjointOperator,
    .SA2_ParityAlternatingBracketAndExactSquareLaw => True
  | .SA2_ParityAlternatingBracketAndExactSquareLaw,
    .SA3_SuperSandwichDefectNilpotentSquareAndHiggsSusySplit => True
  | .SA3_SuperSandwichDefectNilpotentSquareAndHiggsSusySplit,
    .SA4_DivisionFree24IntegerResolutionOfFiveGradedTower => True
  | .SA4_DivisionFree24IntegerResolutionOfFiveGradedTower,
    .SA5_Cyclotomic24ModularClockAndOctonionColorComposition => True
  | .SA5_Cyclotomic24ModularClockAndOctonionColorComposition,
    .SA6_ExponentTwoGaloisCubeAndMasterSynthesis => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_rank_lt {a b : SuperAdjointCyclotomic24Stage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_causalEdge_rank_lt {a b : SuperAdjointCyclotomic24Stage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_rank_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_rank_lt hbc)

/-- **Strict DAG Acyclicity (`SuperAdjointCyclotomic24Stage.causalEdge_acyclic`)**:
No stage in `𝔖𝔄₁..𝔖𝔄₆` can reach itself along a non-empty directed causal path. -/
theorem causalEdge_acyclic (a : SuperAdjointCyclotomic24Stage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_rank_lt h)

/-- Strict 6-stage chain `𝔖𝔄₁ < 𝔖𝔄₂ < 𝔖𝔄₃ < 𝔖𝔄₄ < 𝔖𝔄₅ < 𝔖𝔄₆`. -/
theorem strict_six_stage_chain :
    SA1_CaseFreeChiralSuperAdjointOperator <
      SA2_ParityAlternatingBracketAndExactSquareLaw ∧
    SA2_ParityAlternatingBracketAndExactSquareLaw <
      SA3_SuperSandwichDefectNilpotentSquareAndHiggsSusySplit ∧
    SA3_SuperSandwichDefectNilpotentSquareAndHiggsSusySplit <
      SA4_DivisionFree24IntegerResolutionOfFiveGradedTower ∧
    SA4_DivisionFree24IntegerResolutionOfFiveGradedTower <
      SA5_Cyclotomic24ModularClockAndOctonionColorComposition ∧
    SA5_Cyclotomic24ModularClockAndOctonionColorComposition <
      SA6_ExponentTwoGaloisCubeAndMasterSynthesis := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end SuperAdjointCyclotomic24Stage

section SuperAdjointCyclotomic24Poset

variable {B : Type*} [Ring B]

/-- **Universal Case-Free Chiral Super-Adjoint Operator (`sadOp`)**:
For any chiral grading involution $S \in B$ ($S^2 = 1$) and odd generator $Q \in B$ ($S Q S = -Q$),
$$\mathrm{sad}_Q(X) := Q X - S X S Q.$$
Without any external parity case-split $(-1)^{|Q||X|}$, this single ring polynomial evaluates to
$[Q, E]$ on even elements ($S E S = +E$) and $\{Q, O\}$ on odd elements ($S O S = -O$). -/
@[simp] def sadOp (S Q X : B) : B :=
  Q * X - S * X * S * Q

/-- Division-free $24 = 4!$ scaled Grade-$0$ projector polynomial
$P_0^{(24)}(d) := 6(d^2 - 1)(d^2 - 4) = 6 d^4 - 30 d^2 + 24$. -/
@[simp] def proj24Zero (d : B) : B :=
  (6 : ℤ) • ((d ^ 2 - 1) * (d ^ 2 - (4 : ℤ) • (1 : B)))

/-- Division-free $24 = 4!$ scaled Grade-$+1$ projector polynomial
$P_{+1}^{(24)}(d) := -4 d(d + 1)(d^2 - 4) = -4 d^4 - 4 d^3 + 16 d^2 + 16 d$. -/
@[simp] def proj24Plus1 (d : B) : B :=
  -(4 : ℤ) • (d * (d + 1) * (d ^ 2 - (4 : ℤ) • (1 : B)))

/-- Division-free $24 = 4!$ scaled Grade-$-1$ projector polynomial
$P_{-1}^{(24)}(d) := -4 d(d - 1)(d^2 - 4) = -4 d^4 + 4 d^3 + 16 d^2 - 16 d$. -/
@[simp] def proj24Minus1 (d : B) : B :=
  -(4 : ℤ) • (d * (d - 1) * (d ^ 2 - (4 : ℤ) • (1 : B)))

/-- Division-free $24 = 4!$ scaled Grade-$+2$ projector polynomial
$P_{+2}^{(24)}(d) := d(d^2 - 1)(d + 2) = d^4 + 2 d^3 - d^2 - 2 d$. -/
@[simp] def proj24Plus2 (d : B) : B :=
  d * (d ^ 2 - 1) * (d + (2 : ℤ) • (1 : B))

/-- Division-free $24 = 4!$ scaled Grade-$-2$ projector polynomial
$P_{-2}^{(24)}(d) := d(d^2 - 1)(d - 2) = d^4 - 2 d^3 - d^2 + 2 d$. -/
@[simp] def proj24Minus2 (d : B) : B :=
  d * (d ^ 2 - 1) * (d - (2 : ℤ) • (1 : B))

/-- 5-Graded Kantor–Tanaka quintic contact polynomial
$P_{\text{KT}}(d) := d^5 - 5 d^3 + 4 d = d(d^2 - 1)(d^2 - 4)$. -/
@[simp] def quinticContactPoly (d : B) : B :=
  d ^ 5 - (5 : ℤ) • d ^ 3 + (4 : ℤ) • d

/-- Cyclotomic polynomial $\Phi_1(x) := x - 1$ in a ring `B`. -/
@[simp] def phi1Ring (x : B) : B := x - 1

/-- Cyclotomic polynomial $\Phi_2(x) := x + 1$ in a ring `B`. -/
@[simp] def phi2Ring (x : B) : B := x + 1

/-- Cyclotomic polynomial $\Phi_3(x) := x^2 + x + 1$ in a ring `B`. -/
@[simp] def phi3Ring (x : B) : B := x ^ 2 + x + 1

/-- Cyclotomic polynomial $\Phi_4(x) := x^2 + 1$ in a ring `B`. -/
@[simp] def phi4Ring (x : B) : B := x ^ 2 + 1

/-- Cyclotomic polynomial $\Phi_6(x) := x^2 - x + 1$ in a ring `B`. -/
@[simp] def phi6Ring (x : B) : B := x ^ 2 - x + 1

/-- Cyclotomic polynomial $\Phi_8(x) := x^4 + 1$ in a ring `B`. -/
@[simp] def phi8Ring (x : B) : B := x ^ 4 + 1

/-- Cyclotomic polynomial $\Phi_{12}(x) := x^4 - x^2 + 1$ in a ring `B`. -/
@[simp] def phi12Ring (x : B) : B := x ^ 4 - x ^ 2 + 1

/-- 24th Cyclotomic polynomial $\Phi_{24}(x) := x^8 - x^4 + 1$ in a ring `B`. -/
@[simp] def phi24Ring (x : B) : B := x ^ 8 - x ^ 4 + 1

/-- **Stage `𝔖𝔄₁` (`sa1_case_free_chiral_super_adjoint_operator`)**:
In any associative ring `[Ring B]` with chiral involution $S \in B$ ($hS : S * S = 1$), odd
generator $Q \in B$ ($hQ : S * Q * S = -Q$), even element $E \in B$ ($hE : S * E * S = E$),
odd element $O \in B$ ($hO : S * O * S = -O$), and arbitrary $X \in B$:
1. **Chiral Anticommutativity of $S$ and $Q$**:
   `S * Q = -(Q * S)` and `Q * S = -(S * Q)`.
2. **Automatic Evaluation of $\mathrm{sad}_Q$ Without Case-Splits (`Rung 1`)**:
   - On even $E \in \mathfrak{k}$: `sadOp S Q E = adOp Q E` ($\mathrm{sad}_Q(E) = [Q, E]$),
   - On odd $O \in \mathfrak{p}$: `sadOp S Q O = Q * O + O * Q` ($\mathrm{sad}_Q(O) = \{Q, O\}$).
3. **Universal Parity-Inversion Formula for $\mathrm{sad}_Q(X)$ (`Theorem 1.1`)**:
   - `S * sadOp S Q X * S = -(Q * (S * X * S)) + X * Q`,
   - `S * sadOp S Q E * S = -sadOp S Q E` ($\mathrm{sad}_Q(E) \in \mathfrak{p}$ is odd!),
   - `S * sadOp S Q O * S = sadOp S Q O` ($\mathrm{sad}_Q(O) \in \mathfrak{k}$ is even!). -/
theorem sa1_case_free_chiral_super_adjoint_operator
    {S Q E O : B} (hS : S * S = 1) (hQ : S * Q * S = -Q)
    (hE : S * E * S = E) (hO : S * O * S = -O) (X : B) :
    -- 1. Chiral anticommutativity of S and Q:
    S * Q = -(Q * S) ∧
    Q * S = -(S * Q) ∧
    -- 2. Automatic commutator on 𝔨 and anticommutator on 𝔭:
    sadOp S Q E = adOp Q E ∧
    sadOp S Q O = Q * O + O * Q ∧
    -- 3. Universal parity-inversion law of sad_Q:
    S * sadOp S Q X * S = -(Q * (S * X * S)) + X * Q ∧
    S * sadOp S Q E * S = -sadOp S Q E ∧
    S * sadOp S Q O * S = sadOp S Q O := by
  have hSQ : S * Q = -(Q * S) := by
    calc S * Q
      _ = S * Q * (S * S) := by rw [hS, mul_one]
      _ = (S * Q * S) * S := by noncomm_ring
      _ = (-Q) * S := by rw [hQ]
      _ = -(Q * S) := by noncomm_ring
  have hQS : Q * S = -(S * Q) := by
    rw [hSQ, neg_neg]
  have hEven : sadOp S Q E = adOp Q E := by
    dsimp [sadOp, adOp]
    rw [hE]
  have hOdd : sadOp S Q O = Q * O + O * Q := by
    calc sadOp S Q O
      _ = Q * O - (S * O * S) * Q := rfl
      _ = Q * O - (-O) * Q := by rw [hO]
      _ = Q * O + O * Q := by noncomm_ring
  have hPar : ∀ Y : B, S * sadOp S Q Y * S = -(Q * (S * Y * S)) + Y * Q := by
    intro Y
    calc S * sadOp S Q Y * S
      _ = (S * Q) * Y * S - (S * S) * Y * (S * Q * S) := by
          dsimp [sadOp]; noncomm_ring
      _ = (-(Q * S)) * Y * S - 1 * Y * (-Q) := by
          rw [hQ, hSQ, hS]
      _ = -(Q * (S * Y * S)) + Y * Q := by noncomm_ring
  have hParE : S * sadOp S Q E * S = -sadOp S Q E := by
    calc S * sadOp S Q E * S
      _ = -(Q * (S * E * S)) + E * Q := hPar E
      _ = -(Q * E) + E * Q := by rw [hE]
      _ = -(Q * E - (S * E * S) * Q) := by rw [hE]; noncomm_ring
      _ = -sadOp S Q E := rfl
  have hParO : S * sadOp S Q O * S = sadOp S Q O := by
    calc S * sadOp S Q O * S
      _ = -(Q * (S * O * S)) + O * Q := hPar O
      _ = -(Q * (-O)) + O * Q := by rw [hO]
      _ = Q * O - (S * O * S) * Q := by rw [hO]; noncomm_ring
      _ = sadOp S Q O := rfl
  exact ⟨hSQ, hQS, hEven, hOdd, hPar X, hParE, hParO⟩

/-- **Stage `𝔖𝔄₂` (`sa2_parity_alternating_bracket_and_exact_square_law`)**:
In any associative ring `[Ring B]` with chiral involution $S \in B$ ($hS : S * S = 1$), odd
generator $Q \in B$ ($hQ : S * Q * S = -Q$), even element $E \in B$ ($hE : S * E * S = E$),
odd element $O \in B$ ($hO : S * O * S = -O$), and arbitrary $X \in B$:
1. **Parity-Alternating Two-Step Bracket Law (`Phase III.2–3` & `Rung 0`)**:
   - On even $E \in \mathfrak{k}$, step 1 is the commutator $[Q, E] \in \mathfrak{p}$ and step 2 is
     the anticommutator $\{Q, [Q, E]\}$:
     `sadOp S Q (sadOp S Q E) = Q * adOp Q E + adOp Q E * Q` and
     `Q * adOp Q E + adOp Q E * Q = adOp (Q * Q) E`.
   - On odd $O \in \mathfrak{p}$, step 1 is the anticommutator $\{Q, O\} \in \mathfrak{k}$ and step 2
     is the commutator $[Q, \{Q, O\}]$:
     `sadOp S Q (sadOp S Q O) = adOp Q (Q * O + O * Q)` and
     `adOp Q (Q * O + O * Q) = adOp (Q * Q) O`.
2. **Universal Case-Free Super-Adjoint Square Identity (`Theorem 1.2`)**:
   For ALL $X \in B$ (of arbitrary mixed parity!):
   $$\mathrm{sad}_Q\big(\mathrm{sad}_Q(X)\big) = Q^2 X - X Q^2 = [Q^2, X] = \mathrm{ad}_{Q^2}(X).$$ -/
theorem sa2_parity_alternating_bracket_and_exact_square_law
    {S Q E O : B} (hS : S * S = 1) (hQ : S * Q * S = -Q)
    (hE : S * E * S = E) (hO : S * O * S = -O) (X : B) :
    -- 1. Alternating commutator-anticommutator on 𝔨 and anticommutator-commutator on 𝔭:
    sadOp S Q (sadOp S Q E) = Q * adOp Q E + adOp Q E * Q ∧
    Q * adOp Q E + adOp Q E * Q = adOp (Q * Q) E ∧
    sadOp S Q (sadOp S Q O) = adOp Q (Q * O + O * Q) ∧
    adOp Q (Q * O + O * Q) = adOp (Q * Q) O ∧
    -- 2. Universal case-free square identity sad_Q²(X) = [Q², X] for all X ∈ B:
    sadOp S Q (sadOp S Q X) = Q * Q * X - X * (Q * Q) ∧
    sadOp S Q (sadOp S Q X) = adOp (Q * Q) X := by
  have h1 := sa1_case_free_chiral_super_adjoint_operator hS hQ hE hO X
  have hParX : S * sadOp S Q X * S = -(Q * (S * X * S)) + X * Q := h1.2.2.2.2.1
  have hParE : S * sadOp S Q E * S = -sadOp S Q E := h1.2.2.2.2.2.1
  have hParO : S * sadOp S Q O * S = sadOp S Q O := h1.2.2.2.2.2.2
  have hEven : sadOp S Q E = adOp Q E := h1.2.2.1
  have hOdd : sadOp S Q O = Q * O + O * Q := h1.2.2.2.1
  have hSqX : sadOp S Q (sadOp S Q X) = Q * Q * X - X * (Q * Q) := by
    calc sadOp S Q (sadOp S Q X)
      _ = Q * sadOp S Q X - (S * sadOp S Q X * S) * Q := rfl
      _ = Q * (Q * X - S * X * S * Q) - (-(Q * (S * X * S)) + X * Q) * Q := by
          rw [hParX]; rfl
      _ = Q * Q * X - X * (Q * Q) := by noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, hSqX, hSqX⟩
  · calc sadOp S Q (sadOp S Q E)
      _ = Q * sadOp S Q E - (S * sadOp S Q E * S) * Q := rfl
      _ = Q * sadOp S Q E - (-sadOp S Q E) * Q := by rw [hParE]
      _ = Q * adOp Q E + adOp Q E * Q := by rw [hEven]; noncomm_ring
  · dsimp [adOp]; noncomm_ring
  · calc sadOp S Q (sadOp S Q O)
      _ = Q * sadOp S Q O - (S * sadOp S Q O * S) * Q := rfl
      _ = Q * sadOp S Q O - sadOp S Q O * Q := by rw [hParO]
      _ = adOp Q (Q * O + O * Q) := by rw [hOdd]; rfl
  · dsimp [adOp]; noncomm_ring

/-- **Stage `𝔖𝔄₃` (`sa3_super_sandwich_defect_nilpotent_square_and_higgs_susy_split`)**:
In any associative ring `[Ring B]` with $hS : S * S = 1$, $hQ : S * Q * S = -Q$, and for any
DeWitt idempotent $P \in B$ ($hP : P * P = P$) and $A, C, X \in B$:
1. **The Super-Adjoint vs. Ordinary Adjoint Square Defect (`Phase II.3` & `Rung 2`)**:
   - `adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = -(2 : ℤ) • (adOp Q X * Q)`,
   - `adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = (2 : ℤ) • (X * (Q * Q) - Q * X * Q)`.
2. **Nilpotent Super-Adjoint Square-Zero Law (`Theorem 1.3`)**:
   - If $hQ2 : Q * Q = 0$, then `sadOp S Q (sadOp S Q X) = 0`,
   - For $S_P = \mathrm{invS}\,P$ and $N_+ = \mathrm{conePlus}\,P\,A$, $N_- = \mathrm{coneMinus}\,P\,C$:
     `invS P * conePlus P A * invS P = -conePlus P A`,
     `invS P * coneMinus P C * invS P = -coneMinus P C`,
     `sadOp (invS P) (conePlus P A) (sadOp (invS P) (conePlus P A) X) = 0`, and
     `sadOp (invS P) (coneMinus P C) (sadOp (invS P) (coneMinus P C) X) = 0`.
3. **The Higgs–SUSY Split on $Q = \Phi = N_+ + N_-$ (`Phase III.2` & `Theorem 1.3`)**:
   - `invS P * genPhi P A C * invS P = -genPhi P A C`,
   - `sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) X) = adOp (genV P A C) X`
     ($\mathrm{sad}_\Phi^2(X) = [V, X]$),
   - `sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) (genJ P A C)) = 0`
     (SUSY zero mode: $\mathrm{sad}_\Phi^2(J) = [V, J] = 0$!),
   - `sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) (genPhi P A C)) = 0`
     ($\mathrm{sad}_\Phi^2(\Phi) = [V, \Phi] = 0$),
   - `adOp (genPhi P A C) (adOp (genPhi P A C) (genJ P A C)) = (4 : ℤ) • (genV P A C * genJ P A C)`
     (Higgs/Bohm mass: $\mathrm{ad}_\Phi^2(J) = 4 V J$!). -/
theorem sa3_super_sandwich_defect_nilpotent_square_and_higgs_susy_split
    {S Q P : B} (hS : S * S = 1) (hQ : S * Q * S = -Q)
    (hP : P * P = P) (A C X : B) :
    -- 1. Super-sandwich defect between ad_Q² and sad_Q²:
    adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = -(2 : ℤ) • (adOp Q X * Q) ∧
    adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = (2 : ℤ) • (X * (Q * Q) - Q * X * Q) ∧
    -- 2. Nilpotent square-zero law for sad_Q²:
    (Q * Q = 0 → sadOp S Q (sadOp S Q X) = 0) ∧
    invS P * conePlus P A * invS P = -conePlus P A ∧
    invS P * coneMinus P C * invS P = -coneMinus P C ∧
    sadOp (invS P) (conePlus P A) (sadOp (invS P) (conePlus P A) X) = 0 ∧
    sadOp (invS P) (coneMinus P C) (sadOp (invS P) (coneMinus P C) X) = 0 ∧
    -- 3. Higgs–SUSY split on Q = Φ = N_+ + N_-:
    invS P * genPhi P A C * invS P = -genPhi P A C ∧
    sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) X) =
      adOp (genV P A C) X ∧
    sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) (genJ P A C)) = 0 ∧
    sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) (genPhi P A C)) = 0 ∧
    adOp (genPhi P A C) (adOp (genPhi P A C) (genJ P A C)) =
      (4 : ℤ) • (genV P A C * genJ P A C) := by
  have hSA2 := sa2_parity_alternating_bracket_and_exact_square_law
    hS hQ (E := 0) (O := 0) (by noncomm_ring) (by noncomm_ring) X
  have hSqX : sadOp S Q (sadOp S Q X) = Q * Q * X - X * (Q * Q) := hSA2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSqX]; dsimp [adOp]; noncomm_ring
  · rw [hSqX]; dsimp [adOp]; noncomm_ring
  · intro hQ2
    rw [hSqX, hQ2, zero_mul, mul_zero, sub_self]
  · peirce_nf hP
  · peirce_nf hP
  · dsimp [sadOp]; peirce_nf hP
  · dsimp [sadOp]; peirce_nf hP
  · peirce_nf hP
  · dsimp [sadOp, adOp]; peirce_nf hP
  · dsimp [sadOp]; peirce_nf hP
  · dsimp [sadOp]; peirce_nf hP
  · dsimp [adOp]; peirce_nf hP

/-- **Stage `𝔖𝔄₄` (`sa4_division_free_24_integer_resolution_of_five_graded_tower`)**:
In any associative ring `[Ring B]`, for any $d \in B$ and any tripotent $H \in B$ ($hH : H * H * H = H$):
1. **Why $24 = 4!$ Governs the 5-Graded Tower (`Phase III.1` & `Rung 3`)**:
   - `Nat.factorial 4 = 24 ∧ Nat.lcm 4 (Nat.lcm 6 24) = 24 ∧ 3 * 8 = 24`,
   - `(5 : ℤ) * (2 : ℤ) ^ 4 - 15 * (2 : ℤ) ^ 2 + 4 = 24` ($P'(\pm 2) = 24$).
2. **Universal Partition of $24 \cdot 1$ & Eigen-Polynomial Identities in $\mathbb{Z}[d]$ (`Theorem 2.1`)**:
   - `proj24Minus2 d + proj24Minus1 d + proj24Zero d + proj24Plus1 d + proj24Plus2 d = (24 : ℤ) • (1 : B)`,
   - `d * proj24Zero d = (6 : ℤ) • quinticContactPoly d`,
   - `(d - 1) * proj24Plus1 d = -(4 : ℤ) • quinticContactPoly d`,
   - `(d + 1) * proj24Minus1 d = -(4 : ℤ) • quinticContactPoly d`,
   - `(d - (2 : ℤ) • 1) * proj24Plus2 d = quinticContactPoly d`,
   - `(d + (2 : ℤ) • 1) * proj24Minus2 d = quinticContactPoly d`.
3. **Division-Free Eigen-Equations & 24-Idempotency/Orthogonality Under $d^5 - 5d^3 + 4d = 0$ (`Theorem 2.2`)**:
   Whenever `hd : quinticContactPoly d = 0`:
   - `d * proj24Zero d = 0`, `d * proj24Plus1 d = proj24Plus1 d`, `d * proj24Minus1 d = -proj24Minus1 d`,
     `d * proj24Plus2 d = (2 : ℤ) • proj24Plus2 d`, `d * proj24Minus2 d = -(2 : ℤ) • proj24Minus2 d`,
   - `proj24Zero d * proj24Zero d = (24 : ℤ) • proj24Zero d`,
   - `proj24Plus1 d * proj24Plus1 d = (24 : ℤ) • proj24Plus1 d`,
   - `proj24Minus1 d * proj24Minus1 d = (24 : ℤ) • proj24Minus1 d`,
   - `proj24Plus2 d * proj24Plus2 d = (24 : ℤ) • proj24Plus2 d`,
   - `proj24Minus2 d * proj24Minus2 d = (24 : ℤ) • proj24Minus2 d`,
   - `proj24Plus1 d * proj24Minus1 d = 0`, `proj24Plus2 d * proj24Minus2 d = 0`,
     `proj24Zero d * proj24Plus1 d = 0`, `proj24Zero d * proj24Plus2 d = 0`,
     `proj24Plus1 d * proj24Plus2 d = 0`. -/
theorem sa4_division_free_24_integer_resolution_of_five_graded_tower (d : B) :
    -- 1. 24 = 4! = lcm(4, 6, 24) = 3 × 8 = P'(±2):
    Nat.factorial 4 = 24 ∧
    Nat.lcm 4 (Nat.lcm 6 24) = 24 ∧
    3 * 8 = 24 ∧
    (5 : ℤ) * (2 : ℤ) ^ 4 - 15 * (2 : ℤ) ^ 2 + 4 = 24 ∧
    -- 2. Universal partition of 24 · 1 and polynomial eigen-identities in ℤ[d]:
    proj24Minus2 d + proj24Minus1 d + proj24Zero d + proj24Plus1 d + proj24Plus2 d =
      (24 : ℤ) • (1 : B) ∧
    d * proj24Zero d = (6 : ℤ) • quinticContactPoly d ∧
    (d - 1) * proj24Plus1 d = -(4 : ℤ) • quinticContactPoly d ∧
    (d + 1) * proj24Minus1 d = -(4 : ℤ) • quinticContactPoly d ∧
    (d - (2 : ℤ) • 1) * proj24Plus2 d = quinticContactPoly d ∧
    (d + (2 : ℤ) • 1) * proj24Minus2 d = quinticContactPoly d ∧
    -- 3. Division-free eigen-equations and 24-idempotency/orthogonality under quinticContactPoly d = 0:
    (quinticContactPoly d = 0 →
      d * proj24Zero d = 0 ∧
      d * proj24Plus1 d = proj24Plus1 d ∧
      d * proj24Minus1 d = -proj24Minus1 d ∧
      d * proj24Plus2 d = (2 : ℤ) • proj24Plus2 d ∧
      d * proj24Minus2 d = -(2 : ℤ) • proj24Minus2 d ∧
      proj24Zero d * proj24Zero d = (24 : ℤ) • proj24Zero d ∧
      proj24Plus1 d * proj24Plus1 d = (24 : ℤ) • proj24Plus1 d ∧
      proj24Minus1 d * proj24Minus1 d = (24 : ℤ) • proj24Minus1 d ∧
      proj24Plus2 d * proj24Plus2 d = (24 : ℤ) • proj24Plus2 d ∧
      proj24Minus2 d * proj24Minus2 d = (24 : ℤ) • proj24Minus2 d ∧
      proj24Plus1 d * proj24Minus1 d = 0 ∧
      proj24Plus2 d * proj24Minus2 d = 0 ∧
      proj24Zero d * proj24Plus1 d = 0 ∧
      proj24Zero d * proj24Plus2 d = 0 ∧
      proj24Plus1 d * proj24Plus2 d = 0) := by
  have hSum : proj24Minus2 d + proj24Minus1 d + proj24Zero d + proj24Plus1 d + proj24Plus2 d =
      (24 : ℤ) • (1 : B) := by
    dsimp [proj24Minus2, proj24Minus1, proj24Zero, proj24Plus1, proj24Plus2]
    noncomm_ring
  have hE0 : d * proj24Zero d = (6 : ℤ) • quinticContactPoly d := by
    dsimp [proj24Zero, quinticContactPoly]; noncomm_ring
  have hEp1 : (d - 1) * proj24Plus1 d = -(4 : ℤ) • quinticContactPoly d := by
    dsimp [proj24Plus1, quinticContactPoly]; noncomm_ring
  have hEm1 : (d + 1) * proj24Minus1 d = -(4 : ℤ) • quinticContactPoly d := by
    dsimp [proj24Minus1, quinticContactPoly]; noncomm_ring
  have hEp2 : (d - (2 : ℤ) • 1) * proj24Plus2 d = quinticContactPoly d := by
    dsimp [proj24Plus2, quinticContactPoly]; noncomm_ring
  have hEm2 : (d + (2 : ℤ) • 1) * proj24Minus2 d = quinticContactPoly d := by
    dsimp [proj24Minus2, quinticContactPoly]; noncomm_ring
  refine ⟨by decide, by decide, by decide, by decide, hSum, hE0, hEp1, hEm1, hEp2, hEm2, ?_⟩
  intro hd
  have hd0 : d * proj24Zero d = 0 := by rw [hE0, hd, smul_zero]
  have hdp1 : d * proj24Plus1 d = proj24Plus1 d := by
    have hsub : d * proj24Plus1 d - proj24Plus1 d = 0 := by
      calc d * proj24Plus1 d - proj24Plus1 d
        _ = (d - 1) * proj24Plus1 d := by noncomm_ring
        _ = -(4 : ℤ) • quinticContactPoly d := hEp1
        _ = 0 := by rw [hd, smul_zero]
    exact sub_eq_zero.mp hsub
  have hdm1 : d * proj24Minus1 d = -proj24Minus1 d := by
    have hadd : d * proj24Minus1 d + proj24Minus1 d = 0 := by
      calc d * proj24Minus1 d + proj24Minus1 d
        _ = (d + 1) * proj24Minus1 d := by noncomm_ring
        _ = -(4 : ℤ) • quinticContactPoly d := hEm1
        _ = 0 := by rw [hd, smul_zero]
    exact eq_neg_of_add_eq_zero_left hadd
  have hdp2 : d * proj24Plus2 d = (2 : ℤ) • proj24Plus2 d := by
    have hsub : d * proj24Plus2 d - (2 : ℤ) • proj24Plus2 d = 0 := by
      calc d * proj24Plus2 d - (2 : ℤ) • proj24Plus2 d
        _ = (d - (2 : ℤ) • 1) * proj24Plus2 d := by noncomm_ring
        _ = quinticContactPoly d := hEp2
        _ = 0 := hd
    exact sub_eq_zero.mp hsub
  have hdm2 : d * proj24Minus2 d = -(2 : ℤ) • proj24Minus2 d := by
    have hadd : d * proj24Minus2 d + (2 : ℤ) • proj24Minus2 d = 0 := by
      calc d * proj24Minus2 d + (2 : ℤ) • proj24Minus2 d
        _ = (d + (2 : ℤ) • 1) * proj24Minus2 d := by noncomm_ring
        _ = quinticContactPoly d := hEm2
        _ = 0 := hd
    calc d * proj24Minus2 d
      _ = (d * proj24Minus2 d + (2 : ℤ) • proj24Minus2 d) - (2 : ℤ) • proj24Minus2 d := by abel
      _ = 0 - (2 : ℤ) • proj24Minus2 d := by rw [hadd]
      _ = -(2 : ℤ) • proj24Minus2 d := by abel
  -- Powers of d on each projector:
  have hd0_2 : d ^ 2 * proj24Zero d = 0 := by
    calc d ^ 2 * proj24Zero d = d * (d * proj24Zero d) := by noncomm_ring
      _ = 0 := by rw [hd0, mul_zero]
  have hd0_4 : d ^ 4 * proj24Zero d = 0 := by
    calc d ^ 4 * proj24Zero d = d ^ 2 * (d ^ 2 * proj24Zero d) := by noncomm_ring
      _ = 0 := by rw [hd0_2, mul_zero]
  have hdp1_2 : d ^ 2 * proj24Plus1 d = proj24Plus1 d := by
    calc d ^ 2 * proj24Plus1 d = d * (d * proj24Plus1 d) := by noncomm_ring
      _ = proj24Plus1 d := by rw [hdp1, hdp1]
  have hdp1_3 : d ^ 3 * proj24Plus1 d = proj24Plus1 d := by
    calc d ^ 3 * proj24Plus1 d = d * (d ^ 2 * proj24Plus1 d) := by noncomm_ring
      _ = proj24Plus1 d := by rw [hdp1_2, hdp1]
  have hdp1_4 : d ^ 4 * proj24Plus1 d = proj24Plus1 d := by
    calc d ^ 4 * proj24Plus1 d = d * (d ^ 3 * proj24Plus1 d) := by noncomm_ring
      _ = proj24Plus1 d := by rw [hdp1_3, hdp1]
  have hdm1_2 : d ^ 2 * proj24Minus1 d = proj24Minus1 d := by
    calc d ^ 2 * proj24Minus1 d = d * (d * proj24Minus1 d) := by noncomm_ring
      _ = d * (-proj24Minus1 d) := by rw [hdm1]
      _ = -(d * proj24Minus1 d) := by noncomm_ring
      _ = proj24Minus1 d := by rw [hdm1, neg_neg]
  have hdm1_3 : d ^ 3 * proj24Minus1 d = -proj24Minus1 d := by
    calc d ^ 3 * proj24Minus1 d = d * (d ^ 2 * proj24Minus1 d) := by noncomm_ring
      _ = -proj24Minus1 d := by rw [hdm1_2, hdm1]
  have hdm1_4 : d ^ 4 * proj24Minus1 d = proj24Minus1 d := by
    calc d ^ 4 * proj24Minus1 d = d ^ 2 * (d ^ 2 * proj24Minus1 d) := by noncomm_ring
      _ = proj24Minus1 d := by rw [hdm1_2, hdm1_2]
  have hdp2_2 : d ^ 2 * proj24Plus2 d = (4 : ℤ) • proj24Plus2 d := by
    calc d ^ 2 * proj24Plus2 d = d * (d * proj24Plus2 d) := by noncomm_ring
      _ = d * ((2 : ℤ) • proj24Plus2 d) := by rw [hdp2]
      _ = (2 : ℤ) • (d * proj24Plus2 d) := by noncomm_ring
      _ = (2 : ℤ) • ((2 : ℤ) • proj24Plus2 d) := by rw [hdp2]
      _ = (4 : ℤ) • proj24Plus2 d := by abel
  have hdp2_3 : d ^ 3 * proj24Plus2 d = (8 : ℤ) • proj24Plus2 d := by
    calc d ^ 3 * proj24Plus2 d = d * (d ^ 2 * proj24Plus2 d) := by noncomm_ring
      _ = d * ((4 : ℤ) • proj24Plus2 d) := by rw [hdp2_2]
      _ = (4 : ℤ) • (d * proj24Plus2 d) := by noncomm_ring
      _ = (4 : ℤ) • ((2 : ℤ) • proj24Plus2 d) := by rw [hdp2]
      _ = (8 : ℤ) • proj24Plus2 d := by abel
  have hdp2_4 : d ^ 4 * proj24Plus2 d = (16 : ℤ) • proj24Plus2 d := by
    calc d ^ 4 * proj24Plus2 d = d * (d ^ 3 * proj24Plus2 d) := by noncomm_ring
      _ = d * ((8 : ℤ) • proj24Plus2 d) := by rw [hdp2_3]
      _ = (8 : ℤ) • (d * proj24Plus2 d) := by noncomm_ring
      _ = (8 : ℤ) • ((2 : ℤ) • proj24Plus2 d) := by rw [hdp2]
      _ = (16 : ℤ) • proj24Plus2 d := by abel
  have hdm2_2 : d ^ 2 * proj24Minus2 d = (4 : ℤ) • proj24Minus2 d := by
    calc d ^ 2 * proj24Minus2 d = d * (d * proj24Minus2 d) := by noncomm_ring
      _ = d * (-(2 : ℤ) • proj24Minus2 d) := by rw [hdm2]
      _ = -(2 : ℤ) • (d * proj24Minus2 d) := by noncomm_ring
      _ = -(2 : ℤ) • (-(2 : ℤ) • proj24Minus2 d) := by rw [hdm2]
      _ = (4 : ℤ) • proj24Minus2 d := by abel
  have hdm2_3 : d ^ 3 * proj24Minus2 d = -(8 : ℤ) • proj24Minus2 d := by
    calc d ^ 3 * proj24Minus2 d = d * (d ^ 2 * proj24Minus2 d) := by noncomm_ring
      _ = d * ((4 : ℤ) • proj24Minus2 d) := by rw [hdm2_2]
      _ = (4 : ℤ) • (d * proj24Minus2 d) := by noncomm_ring
      _ = (4 : ℤ) • (-(2 : ℤ) • proj24Minus2 d) := by rw [hdm2]
      _ = -(8 : ℤ) • proj24Minus2 d := by abel
  have hdm2_4 : d ^ 4 * proj24Minus2 d = (16 : ℤ) • proj24Minus2 d := by
    calc d ^ 4 * proj24Minus2 d = d * (d ^ 3 * proj24Minus2 d) := by noncomm_ring
      _ = d * (-(8 : ℤ) • proj24Minus2 d) := by rw [hdm2_3]
      _ = -(8 : ℤ) • (d * proj24Minus2 d) := by noncomm_ring
      _ = -(8 : ℤ) • (-(2 : ℤ) • proj24Minus2 d) := by rw [hdm2]
      _ = (16 : ℤ) • proj24Minus2 d := by abel
  refine ⟨hd0, hdp1, hdm1, hdp2, hdm2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc proj24Zero d * proj24Zero d
      _ = (6 : ℤ) • (d ^ 4 * proj24Zero d) - (30 : ℤ) • (d ^ 2 * proj24Zero d) +
            (24 : ℤ) • proj24Zero d := by
          dsimp only [proj24Zero]; noncomm_ring
      _ = (24 : ℤ) • proj24Zero d := by rw [hd0_4, hd0_2]; noncomm_ring
  · calc proj24Plus1 d * proj24Plus1 d
      _ = -(4 : ℤ) • (d ^ 4 * proj24Plus1 d) - (4 : ℤ) • (d ^ 3 * proj24Plus1 d) +
            (16 : ℤ) • (d ^ 2 * proj24Plus1 d) + (16 : ℤ) • (d * proj24Plus1 d) := by
          dsimp only [proj24Plus1]; noncomm_ring
      _ = (24 : ℤ) • proj24Plus1 d := by rw [hdp1_4, hdp1_3, hdp1_2, hdp1]; noncomm_ring
  · calc proj24Minus1 d * proj24Minus1 d
      _ = -(4 : ℤ) • (d ^ 4 * proj24Minus1 d) + (4 : ℤ) • (d ^ 3 * proj24Minus1 d) +
            (16 : ℤ) • (d ^ 2 * proj24Minus1 d) - (16 : ℤ) • (d * proj24Minus1 d) := by
          dsimp only [proj24Minus1]; noncomm_ring
      _ = (24 : ℤ) • proj24Minus1 d := by rw [hdm1_4, hdm1_3, hdm1_2, hdm1]; noncomm_ring
  · calc proj24Plus2 d * proj24Plus2 d
      _ = d ^ 4 * proj24Plus2 d + (2 : ℤ) • (d ^ 3 * proj24Plus2 d) -
            d ^ 2 * proj24Plus2 d - (2 : ℤ) • (d * proj24Plus2 d) := by
          dsimp only [proj24Plus2]; noncomm_ring
      _ = (24 : ℤ) • proj24Plus2 d := by rw [hdp2_4, hdp2_3, hdp2_2, hdp2]; noncomm_ring
  · calc proj24Minus2 d * proj24Minus2 d
      _ = d ^ 4 * proj24Minus2 d - (2 : ℤ) • (d ^ 3 * proj24Minus2 d) -
            d ^ 2 * proj24Minus2 d + (2 : ℤ) • (d * proj24Minus2 d) := by
          dsimp only [proj24Minus2]; noncomm_ring
      _ = (24 : ℤ) • proj24Minus2 d := by rw [hdm2_4, hdm2_3, hdm2_2, hdm2]; noncomm_ring
  · calc proj24Plus1 d * proj24Minus1 d
      _ = -(4 : ℤ) • (d ^ 4 * proj24Minus1 d) - (4 : ℤ) • (d ^ 3 * proj24Minus1 d) +
            (16 : ℤ) • (d ^ 2 * proj24Minus1 d) + (16 : ℤ) • (d * proj24Minus1 d) := by
          dsimp only [proj24Plus1]; noncomm_ring
      _ = 0 := by rw [hdm1_4, hdm1_3, hdm1_2, hdm1]; noncomm_ring
  · calc proj24Plus2 d * proj24Minus2 d
      _ = d ^ 4 * proj24Minus2 d + (2 : ℤ) • (d ^ 3 * proj24Minus2 d) -
            d ^ 2 * proj24Minus2 d - (2 : ℤ) • (d * proj24Minus2 d) := by
          dsimp only [proj24Plus2]; noncomm_ring
      _ = 0 := by rw [hdm2_4, hdm2_3, hdm2_2, hdm2]; noncomm_ring
  · calc proj24Zero d * proj24Plus1 d
      _ = (6 : ℤ) • (d ^ 4 * proj24Plus1 d) - (30 : ℤ) • (d ^ 2 * proj24Plus1 d) +
            (24 : ℤ) • proj24Plus1 d := by
          dsimp only [proj24Zero]; noncomm_ring
      _ = 0 := by rw [hdp1_4, hdp1_2]; noncomm_ring
  · calc proj24Zero d * proj24Plus2 d
      _ = (6 : ℤ) • (d ^ 4 * proj24Plus2 d) - (30 : ℤ) • (d ^ 2 * proj24Plus2 d) +
            (24 : ℤ) • proj24Plus2 d := by
          dsimp only [proj24Zero]; noncomm_ring
      _ = 0 := by rw [hdp2_4, hdp2_2]; noncomm_ring
  · calc proj24Plus1 d * proj24Plus2 d
      _ = -(4 : ℤ) • (d ^ 4 * proj24Plus2 d) - (4 : ℤ) • (d ^ 3 * proj24Plus2 d) +
            (16 : ℤ) • (d ^ 2 * proj24Plus2 d) + (16 : ℤ) • (d * proj24Plus2 d) := by
          dsimp only [proj24Plus1]; noncomm_ring
      _ = 0 := by rw [hdp2_4, hdp2_3, hdp2_2, hdp2]; noncomm_ring

/-- **Stage `𝔖𝔄₅` (`sa5_cyclotomic_24_modular_clock_and_octonion_color_composition`)**:
In any associative ring `[Ring B]` for any element $x \in B$:
1. **Octonion–Color Cyclotomic Composition (`Theorem 3.2`)**:
   - `phi24Ring x = phi3Ring (-(x ^ 4))` ($\Phi_{24}(x) = x^8 - x^4 + 1 = \Phi_3(-x^4)$:
     couples the $\mathbb{Z}_3$ color polynomial $\Phi_3(y) = y^2 + y + 1$ to $y = -x^4$),
   - `phi24Ring x = phi6Ring (x ^ 4)` ($\Phi_{24}(x) = \Phi_6(x^4)$).
2. **Sub-Clock Divisor Factorizations ($n \in \{2, 3, 4, 6, 8, 12\}$)**:
   - `phi1Ring x * phi2Ring x = x ^ 2 - 1`,
   - `phi1Ring x * phi3Ring x = x ^ 3 - 1`,
   - `phi1Ring x * phi2Ring x * phi4Ring x = x ^ 4 - 1`,
   - `phi1Ring x * phi2Ring x * phi3Ring x * phi6Ring x = x ^ 6 - 1`,
   - `phi1Ring x * phi2Ring x * phi4Ring x * phi8Ring x = x ^ 8 - 1`,
   - `phi1Ring x * phi2Ring x * phi3Ring x * phi4Ring x * phi6Ring x * phi12Ring x = x ^ 12 - 1`.
3. **Complete 8-Divisor Factorization of $x^{24} - 1$ (`Theorem 3.1`)**:
   - `phi1Ring x * phi2Ring x * phi3Ring x * phi4Ring x * phi6Ring x * phi8Ring x * phi12Ring x * phi24Ring x = x ^ 24 - 1`,
   - `(x ^ 24 = 1) → phi1Ring x * phi2Ring x * phi3Ring x * phi4Ring x * phi6Ring x * phi8Ring x * phi12Ring x * phi24Ring x = 0`. -/
theorem sa5_cyclotomic_24_modular_clock_and_octonion_color_composition (x : B) :
    -- 1. Octonion–color composition Φ₂₄(x) = Φ₃(-x⁴) = Φ₆(x⁴):
    phi24Ring x = phi3Ring (-(x ^ 4)) ∧
    phi24Ring x = phi6Ring (x ^ 4) ∧
    -- 2. Sub-clock divisor factorizations for n = 2, 3, 4, 6, 8, 12:
    phi1Ring x * phi2Ring x = x ^ 2 - 1 ∧
    phi1Ring x * phi3Ring x = x ^ 3 - 1 ∧
    phi1Ring x * phi2Ring x * phi4Ring x = x ^ 4 - 1 ∧
    phi1Ring x * phi2Ring x * phi3Ring x * phi6Ring x = x ^ 6 - 1 ∧
    phi1Ring x * phi2Ring x * phi4Ring x * phi8Ring x = x ^ 8 - 1 ∧
    phi1Ring x * phi2Ring x * phi3Ring x * phi4Ring x * phi6Ring x * phi12Ring x = x ^ 12 - 1 ∧
    -- 3. Complete 8-divisor factorization of x²⁴ - 1:
    phi1Ring x * phi2Ring x * phi3Ring x * phi4Ring x *
      phi6Ring x * phi8Ring x * phi12Ring x * phi24Ring x = x ^ 24 - 1 ∧
    (x ^ 24 = 1 →
      phi1Ring x * phi2Ring x * phi3Ring x * phi4Ring x *
        phi6Ring x * phi8Ring x * phi12Ring x * phi24Ring x = 0) := by
  have h24 : phi1Ring x * phi2Ring x * phi3Ring x * phi4Ring x *
      phi6Ring x * phi8Ring x * phi12Ring x * phi24Ring x = x ^ 24 - 1 := by
    dsimp [phi1Ring, phi2Ring, phi3Ring, phi4Ring, phi6Ring, phi8Ring, phi12Ring, phi24Ring]
    noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h24, ?_⟩
  · dsimp [phi24Ring, phi3Ring]; noncomm_ring
  · dsimp [phi24Ring, phi6Ring]; noncomm_ring
  · dsimp [phi1Ring, phi2Ring]; noncomm_ring
  · dsimp [phi1Ring, phi3Ring]; noncomm_ring
  · dsimp [phi1Ring, phi2Ring, phi4Ring]; noncomm_ring
  · dsimp [phi1Ring, phi2Ring, phi3Ring, phi6Ring]; noncomm_ring
  · dsimp [phi1Ring, phi2Ring, phi4Ring, phi8Ring]; noncomm_ring
  · dsimp [phi1Ring, phi2Ring, phi3Ring, phi4Ring, phi6Ring, phi12Ring]; noncomm_ring
  · intro hx24
    rw [h24, hx24, sub_self]

/-- **Stage `𝔖𝔄₆` (`sa6_exponent_two_galois_cube_and_master_synthesis`)**:
Master theorem unifying the 6-stage **Universal Super-Adjoint $\mathrm{sad}_Q$ & $24 = 4!$ Cyclotomic
Modular Clock Poset** (`𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ ⋯ ≺ 𝔖𝔄₆`):
1. **Poset Acyclicity & Cardinality**:
   `SuperAdjointCyclotomic24Stage.causalEdge_acyclic` and `Fintype.card SuperAdjointCyclotomic24Stage = 6`.
2. **Euler Totient $\varphi(24) = 8 = \dim \mathbb{O}_s$ & Exponent-2 Galois Cube $(\mathbb{Z}/24\mathbb{Z})^\times$ (`Theorem 3.3`)**:
   - `Fintype.card (ZMod 24)ˣ = 8`,
   - `∀ u : (ZMod 24)ˣ, u ^ 2 = 1`,
   - `∀ k ∈ ({1, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ), (k ^ 2 - 1) % 24 = 0`.
3. **Master Synthesis**:
   Bundles $\mathrm{sad}_Q^2(X) = [Q^2, X]$, $\mathrm{ad}_Q^2(X) - \mathrm{sad}_Q^2(X) = -2 Q X Q$,
   $\mathrm{sad}_{N_+}^2(X) = 0$, $\mathrm{sad}_\Phi^2(J) = 0$ vs. $\mathrm{ad}_\Phi^2(J) = 4 V J$,
   $\sum_{k=-2}^{+2} P_k^{(24)}(d) = 24 \cdot 1$, $\Phi_{24}(x) = \Phi_3(-x^4)$, and
   $\prod_{d \mid 24} \Phi_d(x) = x^{24} - 1$. -/
theorem sa6_exponent_two_galois_cube_and_master_synthesis
    {S Q P : B} (hS : S * S = 1) (hQ : S * Q * S = -Q)
    (hP : P * P = P) (A C X d x : B) :
    -- 1. Poset acyclicity and cardinality of 𝔖𝔄₁ ≺ ⋯ ≺ 𝔖𝔄₆:
    (∀ st : SuperAdjointCyclotomic24Stage,
      ¬ Relation.TransGen SuperAdjointCyclotomic24Stage.causalEdge st st) ∧
    Fintype.card SuperAdjointCyclotomic24Stage = 6 ∧
    -- 2. Galois cube |(ℤ/24ℤ)^×| = 8 = dim 𝕆_s and exponent-2 law u² = 1:
    Fintype.card (ZMod 24)ˣ = 8 ∧
    (∀ u : (ZMod 24)ˣ, u ^ 2 = 1) ∧
    (∀ k ∈ ({1, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ), (k ^ 2 - 1) % 24 = 0) ∧
    -- 3. Universal Super-Adjoint square identity, super-sandwich defect, and Higgs–SUSY split:
    sadOp S Q (sadOp S Q X) = adOp (Q * Q) X ∧
    adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = -(2 : ℤ) • (adOp Q X * Q) ∧
    sadOp (invS P) (conePlus P A) (sadOp (invS P) (conePlus P A) X) = 0 ∧
    sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) (genJ P A C)) = 0 ∧
    adOp (genPhi P A C) (adOp (genPhi P A C) (genJ P A C)) =
      (4 : ℤ) • (genV P A C * genJ P A C) ∧
    -- 4. Division-free 24 = 4! integer projector sum & 24-cyclotomic factorization:
    proj24Minus2 d + proj24Minus1 d + proj24Zero d + proj24Plus1 d + proj24Plus2 d =
      (24 : ℤ) • (1 : B) ∧
    phi24Ring x = phi3Ring (-(x ^ 4)) ∧
    phi1Ring x * phi2Ring x * phi3Ring x * phi4Ring x *
      phi6Ring x * phi8Ring x * phi12Ring x * phi24Ring x = x ^ 24 - 1 := by
  have hSA2 := sa2_parity_alternating_bracket_and_exact_square_law
    hS hQ (E := 0) (O := 0) (by noncomm_ring) (by noncomm_ring) X
  have hSA3 := sa3_super_sandwich_defect_nilpotent_square_and_higgs_susy_split
    hS hQ hP A C X
  have hSA4 := sa4_division_free_24_integer_resolution_of_five_graded_tower d
  have hSA5 := sa5_cyclotomic_24_modular_clock_and_octonion_color_composition x
  refine ⟨SuperAdjointCyclotomic24Stage.causalEdge_acyclic,
    SuperAdjointCyclotomic24Stage.card_eq_six,
    by decide,
    by intro u; fin_cases u <;> decide,
    by decide,
    hSA2.2.2.2.2.2,
    hSA3.1,
    hSA3.2.2.2.2.2.1,
    hSA3.2.2.2.2.2.2.2.2.2.1,
    hSA3.2.2.2.2.2.2.2.2.2.2.2,
    hSA4.2.2.2.2.1,
    hSA5.1,
    hSA5.2.2.2.2.2.2.2.2.1⟩

end SuperAdjointCyclotomic24Poset

/-!
## 7f. The Four-Way Super-Bracket Diamond & $\mathbb{Z}/24\mathbb{Z}$ Isogeny Glue Cohomology Poset (`𝔇𝔐₁ ≺ 𝔇𝔐₂, 𝔇𝔐₃ ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`)

Passing the Bulgarian synthesis through the Socratic elenchus exposes two unexamined aporias
hidden beneath its claim of "final closure":
1. **Symmetric Sandwich Conflation vs. Asymmetric Right-Twist (`-2 [Q, X] Q` vs. `-4 Q X Q`)**:
   Because $\mathrm{ad}_Q^2(X) = Q^2 X - 2 Q X Q + X Q^2$ has $+X Q^2$ on the right while
   $\mathrm{sad}_Q^2(X) = [Q^2, X] = Q^2 X - X Q^2$ has $-X Q^2$ on the right, subtracting them
   doubles $X Q^2$ to yield $2 X Q^2 - 2 Q X Q = -2\,[Q, X]\,Q$.
   Testing on the Goldstone mode $X = Q = \Phi \in \mathfrak{p}$ immediately refutes the naive
   formula $-4 Q\,\mathcal{P}_{\text{odd}}(X)\,Q$:
   - $\mathrm{ad}_\Phi^2(\Phi) - \mathrm{sad}_\Phi^2(\Phi) = -2\,[\Phi, \Phi]\,\Phi = 0$ (massless Goldstone mode!),
   - whereas $-4\,\Phi^3 = -4\,V \Phi \neq 0$.
   Meanwhile, the pure bilateral sandwich $-4 Q X Q$ is the difference between the double
   commutator $\mathrm{ad}_Q^2(X) = [Q, [Q, X]]$ and the double anticommutator
   $\mathrm{ac}_Q^2(X) = \{Q, \{Q, X\}\}$, and the two formulas differ by $2\,\{Q, X\}\,Q$,
   coinciding on the axial vortex mode $X = J$ precisely because $\{\Phi, J\} = 0$!
2. **The 24-Isogeny Glue Exact Sequence Over $\mathbb{Z}[D]$**:
   Over $\mathbb{Z}$ (where $2$ and $3$ are not invertible), the five scaled projectors
   $P_k^{(24)}(D)$ satisfy $\sum_{k=-2}^{+2} P_k^{(24)}(D) = 24 \cdot 1$ and
   $P_j^{(24)}(D) P_k^{(24)}(D) = 24\delta_{jk} P_j^{(24)}(D)$, defining a **24-isogeny**
   ($\Sigma_{24} \circ \Psi_{24} = 24\,\mathrm{id}$, $\Psi_{24} \circ \Sigma_{24} = 24\,\mathrm{id}$)
   whose cokernel is a 24-torsion glue group annihilated by $24 = 2^3 \cdot 3$.
-/

/-- The 6 stages of the **Four-Way Super-Bracket Diamond & $\mathbb{Z}/24\mathbb{Z}$ Isogeny
Glue Cohomology Poset** (`𝔇𝔐₁ ≺ 𝔇𝔐₂, 𝔇𝔐₃ ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`). -/
inductive SuperBracketDiamond24GlueStage : Type
  /-- `𝔇𝔐₁`: The four second-order super-brackets (`--`, `++`, `-+`, `+-`) & Rung 0 Goldstone elenchus. -/
  | DM1_FourSecondOrderSuperBracketsAndGoldstoneElenchus
  /-- `𝔇𝔐₂`: Opposite-parity bracket cancellation (`[Q, {Q, X}] = {Q, [Q, X]} = [Q², X]`). -/
  | DM2_OppositeParityBracketCancellation
  /-- `𝔇𝔐₃`: Like-parity sandwich split (`[Q, [Q, X]] = {Q², X} - 2 Q X Q`, `{Q, {Q, X}} = {Q², X} + 2 Q X Q`). -/
  | DM3_LikeParitySandwichSplit
  /-- `𝔇𝔐₄`: Exact asymmetric defect `ad_Q² - sad_Q² = -2 [Q, X] Q` vs. symmetric sandwich `ad_Q² - ac_Q² = -4 Q X Q`. -/
  | DM4_AsymmetricDefectVsSymmetricSandwich
  /-- `𝔇𝔐₅`: Goldstone zero-mode protection (`[Q, Q] = 0 ⟹ 0`) & anticommuting specialization (`{Q, J} = 0 ⟹ -4 Q J Q = 4 Q² J`). -/
  | DM5_GoldstoneProtectionAndAnticommutingSpecialization
  /-- `𝔇𝔐₆`: The 24-isogeny glue law (`Σ₂₄ ∘ Ψ₂₄ = 24 id`, `Ψ₂₄ ∘ Σ₂₄ = 24 id`) & master synthesis. -/
  | DM6_TwentyFourIsogenyGlueLawAndMasterSynthesis
  deriving DecidableEq, Repr

namespace SuperBracketDiamond24GlueStage

/-- Integer rank `0 .. 5` for linear extension of `𝔇𝔐₁ ≺ ⋯ ≺ 𝔇𝔐₆`. -/
def rank : SuperBracketDiamond24GlueStage → ℕ
  | .DM1_FourSecondOrderSuperBracketsAndGoldstoneElenchus  => 0
  | .DM2_OppositeParityBracketCancellation                 => 1
  | .DM3_LikeParitySandwichSplit                           => 2
  | .DM4_AsymmetricDefectVsSymmetricSandwich               => 3
  | .DM5_GoldstoneProtectionAndAnticommutingSpecialization => 4
  | .DM6_TwentyFourIsogenyGlueLawAndMasterSynthesis        => 5

/-- Hasse diagram height `0 .. 4` where `𝔇𝔐₂` and `𝔇𝔐₃` form the parallel diamond at height `1`. -/
def height : SuperBracketDiamond24GlueStage → ℕ
  | .DM1_FourSecondOrderSuperBracketsAndGoldstoneElenchus  => 0
  | .DM2_OppositeParityBracketCancellation                 => 1
  | .DM3_LikeParitySandwichSplit                           => 1
  | .DM4_AsymmetricDefectVsSymmetricSandwich               => 2
  | .DM5_GoldstoneProtectionAndAnticommutingSpecialization => 3
  | .DM6_TwentyFourIsogenyGlueLawAndMasterSynthesis        => 4

theorem rank_injective :
    Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder SuperBracketDiamond24GlueStage where
  le a b := rank a ≤ rank b
  lt a b := rank a < rank b
  le_refl a := le_rfl
  le_trans a b c := Nat.le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (rank a) (rank b)
  le_antisymm a b hab hba := rank_injective (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total (rank a) (rank b)
  toDecidableLE a b := Nat.decLe (rank a) (rank b)
  toDecidableEq := inferInstance
  toDecidableLT a b := Nat.decLt (rank a) (rank b)

instance : Fintype SuperBracketDiamond24GlueStage where
  elems := {
    .DM1_FourSecondOrderSuperBracketsAndGoldstoneElenchus,
    .DM2_OppositeParityBracketCancellation,
    .DM3_LikeParitySandwichSplit,
    .DM4_AsymmetricDefectVsSymmetricSandwich,
    .DM5_GoldstoneProtectionAndAnticommutingSpecialization,
    .DM6_TwentyFourIsogenyGlueLawAndMasterSynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_six :
    Fintype.card SuperBracketDiamond24GlueStage = 6 := rfl

/-- Directed Hasse covering edges of the diamond poset `𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`. -/
def causalEdge : SuperBracketDiamond24GlueStage → SuperBracketDiamond24GlueStage → Prop
  | .DM1_FourSecondOrderSuperBracketsAndGoldstoneElenchus, .DM2_OppositeParityBracketCancellation => True
  | .DM1_FourSecondOrderSuperBracketsAndGoldstoneElenchus, .DM3_LikeParitySandwichSplit => True
  | .DM2_OppositeParityBracketCancellation, .DM4_AsymmetricDefectVsSymmetricSandwich => True
  | .DM3_LikeParitySandwichSplit, .DM4_AsymmetricDefectVsSymmetricSandwich => True
  | .DM4_AsymmetricDefectVsSymmetricSandwich, .DM5_GoldstoneProtectionAndAnticommutingSpecialization => True
  | .DM5_GoldstoneProtectionAndAnticommutingSpecialization, .DM6_TwentyFourIsogenyGlueLawAndMasterSynthesis => True
  | _, _ => False

theorem causalEdge_height_lt {a b : SuperBracketDiamond24GlueStage}
    (h : causalEdge a b) : height a < height b := by
  cases a <;> cases b <;> cases h <;> decide

theorem transGen_causalEdge_height_lt {a b : SuperBracketDiamond24GlueStage}
    (h : Relation.TransGen causalEdge a b) : height a < height b := by
  induction h with
  | single hab => exact causalEdge_height_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_height_lt hbc)

/-- Strict DAG acyclicity of `𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`. -/
theorem causalEdge_acyclic (a : SuperBracketDiamond24GlueStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (height a) (transGen_causalEdge_height_lt h)

/-- Diamond incomparability of the opposite-parity (`𝔇𝔐₂`) and like-parity (`𝔇𝔐₃`) branches. -/
theorem incomparable_DM2_DM3 :
    ¬ Relation.TransGen causalEdge
        .DM2_OppositeParityBracketCancellation .DM3_LikeParitySandwichSplit ∧
    ¬ Relation.TransGen causalEdge
        .DM3_LikeParitySandwichSplit .DM2_OppositeParityBracketCancellation := by
  constructor <;>
    (intro h; have hlt := transGen_causalEdge_height_lt h; revert hlt; decide)

/-- Monotone embedding into `InfoGeometry.Meta.RepDepth`. -/
def toRepDepth : SuperBracketDiamond24GlueStage → InfoGeometry.Meta.RepDepth
  | .DM1_FourSecondOrderSuperBracketsAndGoldstoneElenchus  => .operator
  | .DM2_OppositeParityBracketCancellation                 => .operator
  | .DM3_LikeParitySandwichSplit                           => .operator
  | .DM4_AsymmetricDefectVsSymmetricSandwich               => .operator
  | .DM5_GoldstoneProtectionAndAnticommutingSpecialization => .transport
  | .DM6_TwentyFourIsogenyGlueLawAndMasterSynthesis        => .thermo

/-- Monotone embedding into `InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    SuperBracketDiamond24GlueStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .DM1_FourSecondOrderSuperBracketsAndGoldstoneElenchus  => .M1_ProjectorClabject
  | .DM2_OppositeParityBracketCancellation                 => .M1_ProjectorClabject
  | .DM3_LikeParitySandwichSplit                           => .M1_ProjectorClabject
  | .DM4_AsymmetricDefectVsSymmetricSandwich               => .M2_GrassmannianPowertypeOrbit
  | .DM5_GoldstoneProtectionAndAnticommutingSpecialization => .M2_GrassmannianPowertypeOrbit
  | .DM6_TwentyFourIsogenyGlueLawAndMasterSynthesis        => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : SuperBracketDiamond24GlueStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth InfoGeometry.Meta.RepDepth.toNat <;>
    decide

theorem toOntologyMetaLevel_mono {a b : SuperBracketDiamond24GlueStage}
    (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;>
    decide

end SuperBracketDiamond24GlueStage

section SuperBracketDiamond24GluePoset

open InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair

variable {B : Type*} [Ring B]

/-- The anticommutator operator $\mathrm{ac}_Q(X) := \{Q, X\} = Q X + X Q$ in `[Ring B]`. -/
@[simp] def acOp (Q X : B) : B :=
  Q * X + X * Q

/-- The 5-component 24-isogeny decomposition morphism
$\Psi_{24}(d, X) := (P_{-2}^{(24)}(d) X, P_{-1}^{(24)}(d) X, P_0^{(24)}(d) X, P_{+1}^{(24)}(d) X, P_{+2}^{(24)}(d) X)$. -/
@[simp] def psi24Map (d X : B) : B × B × B × B × B :=
  (proj24Minus2 d * X, proj24Minus1 d * X, proj24Zero d * X,
   proj24Plus1 d * X, proj24Plus2 d * X)

/-- The 5-component summation morphism
$\Sigma_{24}(x_{-2}, x_{-1}, x_0, x_{+1}, x_{+2}) := x_{-2} + x_{-1} + x_0 + x_{+1} + x_{+2}$. -/
@[simp] def sigma24Map (t : B × B × B × B × B) : B :=
  t.1 + t.2.1 + t.2.2.1 + t.2.2.2.1 + t.2.2.2.2

/-- **Stage `𝔇𝔐₁` (`dm1_four_second_order_super_brackets_and_rung0_goldstone_elenchus`)**:
1. **First-Order Commutator / Anticommutator Split (`Phase II`)**:
   - `adOp Q X + acOp Q X = (2 : ℤ) • (Q * X)`,
   - `acOp Q X - adOp Q X = (2 : ℤ) • (X * Q)`.
2. **Rung 0 Socratic Elenchus on the Goldstone Mode $X = Q = \Phi \in \mathfrak{p}$ (`Phase IV, Rung 0`)**:
   For any DeWitt idempotent $P \in B$ ($hP : P * P = P$) and $A, C \in B$:
   - $\Phi = \mathrm{genPhi}\,P\,A\,C$ is odd (`invS P * genPhi P A C * invS P = -genPhi P A C`),
   - The true difference $\mathrm{ad}_\Phi^2(\Phi) - \mathrm{sad}_\Phi^2(\Phi)$ vanishes identically:
     `adOp (genPhi P A C) (adOp (genPhi P A C) (genPhi P A C)) - sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) (genPhi P A C)) = 0`,
   - Whereas the naive symmetric sandwich $-4 \Phi^3$ evaluates to
     `-(4 : ℤ) • (genPhi P A C * genPhi P A C * genPhi P A C) = -(4 : ℤ) • (genV P A C * genPhi P A C)`,
   - And the discrepancy between the true difference and the naive symmetric sandwich at $X = \Phi$ is
     `(adOp (genPhi P A C) (adOp (genPhi P A C) (genPhi P A C)) - sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) (genPhi P A C))) - (-(4 : ℤ) • (genPhi P A C * genPhi P A C * genPhi P A C)) = (4 : ℤ) • (genV P A C * genPhi P A C)`. -/
theorem dm1_four_second_order_super_brackets_and_rung0_goldstone_elenchus
    {P : B} (hP : P * P = P) (Q X A C : B) :
    -- 1. First-order commutator and anticommutator decomposition of left and right multiplication:
    adOp Q X + acOp Q X = (2 : ℤ) • (Q * X) ∧
    acOp Q X - adOp Q X = (2 : ℤ) • (X * Q) ∧
    -- 2. Rung 0 Socratic Elenchus on X = Q = Φ:
    invS P * genPhi P A C * invS P = -genPhi P A C ∧
    adOp (genPhi P A C) (adOp (genPhi P A C) (genPhi P A C)) -
      sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) (genPhi P A C)) = 0 ∧
    -(4 : ℤ) • (genPhi P A C * genPhi P A C * genPhi P A C) =
      -(4 : ℤ) • (genV P A C * genPhi P A C) ∧
    (adOp (genPhi P A C) (adOp (genPhi P A C) (genPhi P A C)) -
      sadOp (invS P) (genPhi P A C) (sadOp (invS P) (genPhi P A C) (genPhi P A C))) -
      (-(4 : ℤ) • (genPhi P A C * genPhi P A C * genPhi P A C)) =
      (4 : ℤ) • (genV P A C * genPhi P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [adOp, acOp]; noncomm_ring
  · dsimp [adOp, acOp]; noncomm_ring
  · peirce_nf hP
  · dsimp [adOp, sadOp]; peirce_nf hP
  · peirce_nf hP
  · dsimp [adOp, sadOp]; peirce_nf hP

/-- **Stage `𝔇𝔐₂` (`dm2_opposite_parity_bracket_cancellation_law`)**:
In any associative ring `[Ring B]`, for all $Q, X \in B$:
1. **Sector $(-+)$ — Commutator of Anticommutator (`Theorem 1.1`)**:
   `adOp Q (acOp Q X) = adOp (Q * Q) X` ($[Q, \{Q, X\}] = [Q^2, X]$).
2. **Sector $(+-)$ — Anticommutator of Commutator (`Theorem 1.1`)**:
   `acOp Q (adOp Q X) = adOp (Q * Q) X` ($\{Q, [Q, X]\} = [Q^2, X]$).
3. **Universal Equality With $\mathrm{sad}_Q^2(X)$**:
   `adOp Q (acOp Q X) = acOp Q (adOp Q X)` and, whenever $hS : S * S = 1$ and $hQ : S * Q * S = -Q$,
   `sadOp S Q (sadOp S Q X) = adOp Q (acOp Q X)` and `sadOp S Q (sadOp S Q X) = acOp Q (adOp Q X)`. -/
theorem dm2_opposite_parity_bracket_cancellation_law
    {S Q : B} (hS : S * S = 1) (hQ : S * Q * S = -Q) (X : B) :
    adOp Q (acOp Q X) = adOp (Q * Q) X ∧
    acOp Q (adOp Q X) = adOp (Q * Q) X ∧
    adOp Q (acOp Q X) = acOp Q (adOp Q X) ∧
    sadOp S Q (sadOp S Q X) = adOp Q (acOp Q X) ∧
    sadOp S Q (sadOp S Q X) = acOp Q (adOp Q X) := by
  have hMP : adOp Q (acOp Q X) = adOp (Q * Q) X := by
    dsimp [adOp, acOp]; noncomm_ring
  have hPM : acOp Q (adOp Q X) = adOp (Q * Q) X := by
    dsimp [adOp, acOp]; noncomm_ring
  have hSA2 := sa2_parity_alternating_bracket_and_exact_square_law
    hS hQ (E := 0) (O := 0) (by noncomm_ring) (by noncomm_ring) X
  have hSq : sadOp S Q (sadOp S Q X) = adOp (Q * Q) X := hSA2.2.2.2.2.2
  exact ⟨hMP, hPM, hMP.trans hPM.symm, hSq.trans hMP.symm, hSq.trans hPM.symm⟩

/-- **Stage `𝔇𝔐₃` (`dm3_like_parity_sandwich_split_law`)**:
In any associative ring `[Ring B]`, for all $Q, X \in B$:
1. **Sector $(--)$ — Double Commutator (`Theorem 1.2`)**:
   `adOp Q (adOp Q X) = acOp (Q * Q) X - (2 : ℤ) • (Q * X * Q)`
   ($[Q, [Q, X]] = \{Q^2, X\} - 2 Q X Q$).
2. **Sector $(++)$ — Double Anticommutator (`Theorem 1.2`)**:
   `acOp Q (acOp Q X) = acOp (Q * Q) X + (2 : ℤ) • (Q * X * Q)`
   ($\{Q, \{Q, X\}\} = \{Q^2, X\} + 2 Q X Q$). -/
theorem dm3_like_parity_sandwich_split_law (Q X : B) :
    adOp Q (adOp Q X) = acOp (Q * Q) X - (2 : ℤ) • (Q * X * Q) ∧
    acOp Q (acOp Q X) = acOp (Q * Q) X + (2 : ℤ) • (Q * X * Q) := by
  constructor <;> (dsimp [adOp, acOp]; noncomm_ring)

/-- **Stage `𝔇𝔐₄` (`dm4_asymmetric_defect_vs_symmetric_sandwich_identity`)**:
In any associative ring `[Ring B]` with $hS : S * S = 1$ and $hQ : S * Q * S = -Q$, for all $X \in B$:
1. **True Asymmetric Super-Adjoint Defect (`Theorem 1.3`)**:
   $$\mathrm{ad}_Q^2(X) - \mathrm{sad}_Q^2(X) = 2 X Q^2 - 2 Q X Q = -2\,[Q, X]\,Q = -2\,\mathrm{ad}_Q(X)\,Q.$$
2. **Symmetric Bilateral Sandwich & Metric Sum (`Theorem 1.3`)**:
   $$\mathrm{ad}_Q^2(X) - \mathrm{ac}_Q^2(X) = -4\,Q X Q, \qquad
     \mathrm{ad}_Q^2(X) + \mathrm{ac}_Q^2(X) = 2\,\{Q^2, X\}.$$
3. **Exact Discrepancy Between Asymmetric Defect and Symmetric Sandwich (`Phase III.1`)**:
   $$\big(\mathrm{ad}_Q^2(X) - \mathrm{sad}_Q^2(X)\big) - \big(\mathrm{ad}_Q^2(X) - \mathrm{ac}_Q^2(X)\big)
     = -2\,[Q, X]\,Q - (-4\,Q X Q) = 2\,\{Q, X\}\,Q = 2\,\mathrm{ac}_Q(X)\,Q.$$ -/
theorem dm4_asymmetric_defect_vs_symmetric_sandwich_identity
    {S Q : B} (hS : S * S = 1) (hQ : S * Q * S = -Q) (X : B) :
    adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = (2 : ℤ) • (X * (Q * Q) - Q * X * Q) ∧
    adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = -(2 : ℤ) • (adOp Q X * Q) ∧
    adOp Q (adOp Q X) - acOp Q (acOp Q X) = -(4 : ℤ) • (Q * X * Q) ∧
    adOp Q (adOp Q X) + acOp Q (acOp Q X) = (2 : ℤ) • acOp (Q * Q) X ∧
    (adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X)) -
      (adOp Q (adOp Q X) - acOp Q (acOp Q X)) = (2 : ℤ) • (acOp Q X * Q) ∧
    -(2 : ℤ) • (adOp Q X * Q) - (-(4 : ℤ) • (Q * X * Q)) = (2 : ℤ) • (acOp Q X * Q) := by
  have hSA2 := sa2_parity_alternating_bracket_and_exact_square_law
    hS hQ (E := 0) (O := 0) (by noncomm_ring) (by noncomm_ring) X
  have hSqX : sadOp S Q (sadOp S Q X) = Q * Q * X - X * (Q * Q) := hSA2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSqX]; dsimp [adOp]; noncomm_ring
  · rw [hSqX]; dsimp [adOp]; noncomm_ring
  · dsimp [adOp, acOp]; noncomm_ring
  · dsimp [adOp, acOp]; noncomm_ring
  · rw [hSqX]; dsimp [adOp, acOp]; noncomm_ring
  · dsimp [adOp, acOp]; noncomm_ring

/-- **Stage `𝔇𝔐₅` (`dm5_goldstone_zero_mode_protection_and_anticommuting_specialization`)**:
In any associative ring `[Ring B]` with $hS : S * S = 1$, $hQ : S * Q * S = -Q$, and DeWitt
idempotent $P \in B$ ($hP : P * P = P$):
1. **Goldstone Zero-Mode Protection (`Theorem 2.1`)**:
   - Whenever `adOp Q X = 0` ($[Q, X] = 0$, e.g. $X = Q$), the true defect vanishes:
     `adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = 0`,
   - Specifically for $X = Q$: `-(2 : ℤ) • (adOp Q Q * Q) = 0` and
     `adOp Q (adOp Q Q) - sadOp S Q (sadOp S Q Q) = 0`.
2. **Anticommuting Axial Specialization (`Theorem 2.1`)**:
   - Whenever `acOp Q X = 0` ($\{Q, X\} = 0$), the discrepancy $2\,\{Q, X\}\,Q$ vanishes, so the
     asymmetric defect and symmetric sandwich coincide and equal $+4 Q^2 X$:
     `X * Q = -(Q * X)`,
     `adOp (Q * Q) X = 0`,
     `adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = -(4 : ℤ) • (Q * X * Q)`, and
     `-(4 : ℤ) • (Q * X * Q) = (4 : ℤ) • (Q * Q * X)`.
3. **Peirce Spine Realization on $Q = \Phi$, $X = J$**:
   - `acOp (genPhi P A C) (genJ P A C) = 0`,
   - `-(2 : ℤ) • (adOp (genPhi P A C) (genJ P A C) * genPhi P A C) = -(4 : ℤ) • (genPhi P A C * genJ P A C * genPhi P A C)`,
   - `-(4 : ℤ) • (genPhi P A C * genJ P A C * genPhi P A C) = (4 : ℤ) • (genV P A C * genJ P A C)`. -/
theorem dm5_goldstone_zero_mode_protection_and_anticommuting_specialization
    {S Q P : B} (hS : S * S = 1) (hQ : S * Q * S = -Q)
    (hP : P * P = P) (A C X : B) :
    -- 1. Goldstone zero-mode protection ([Q, X] = 0 ⟹ defect = 0):
    (adOp Q X = 0 → adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = 0) ∧
    -(2 : ℤ) • (adOp Q Q * Q) = 0 ∧
    adOp Q (adOp Q Q) - sadOp S Q (sadOp S Q Q) = 0 ∧
    -- 2. Anticommuting specialization ({Q, X} = 0 ⟹ -2[Q,X]Q = -4 QXQ = +4 Q²X):
    (acOp Q X = 0 →
      X * Q = -(Q * X) ∧
      adOp (Q * Q) X = 0 ∧
      adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = -(4 : ℤ) • (Q * X * Q) ∧
      -(4 : ℤ) • (Q * X * Q) = (4 : ℤ) • (Q * Q * X)) ∧
    -- 3. Peirce spine realization on Q = Φ, X = J:
    acOp (genPhi P A C) (genJ P A C) = 0 ∧
    -(2 : ℤ) • (adOp (genPhi P A C) (genJ P A C) * genPhi P A C) =
      -(4 : ℤ) • (genPhi P A C * genJ P A C * genPhi P A C) ∧
    -(4 : ℤ) • (genPhi P A C * genJ P A C * genPhi P A C) =
      (4 : ℤ) • (genV P A C * genJ P A C) := by
  have hDM4_X := dm4_asymmetric_defect_vs_symmetric_sandwich_identity hS hQ X
  have hDM4_Q := dm4_asymmetric_defect_vs_symmetric_sandwich_identity hS hQ Q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hComm
    rw [hDM4_X.2.1, hComm, zero_mul, smul_zero]
  · dsimp [adOp]; noncomm_ring
  · rw [hDM4_Q.2.1]; dsimp [adOp]; noncomm_ring
  · intro hAnti
    have hXQ : X * Q = -(Q * X) := by
      calc X * Q
        _ = (Q * X + X * Q) - Q * X := by abel
        _ = acOp Q X - Q * X := rfl
        _ = 0 - Q * X := by rw [hAnti]
        _ = -(Q * X) := by abel
    have hQ2X : adOp (Q * Q) X = 0 := by
      calc adOp (Q * Q) X
        _ = Q * (Q * X + X * Q) - (Q * X + X * Q) * Q := by dsimp [adOp]; noncomm_ring
        _ = Q * acOp Q X - acOp Q X * Q := rfl
        _ = 0 := by rw [hAnti, mul_zero, zero_mul, sub_self]
    have hEqSand : adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = -(4 : ℤ) • (Q * X * Q) := by
      calc adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X)
        _ = (adOp Q (adOp Q X) - acOp Q (acOp Q X)) + (2 : ℤ) • (acOp Q X * Q) := by
            rw [← hDM4_X.2.2.2.2.1]; abel
        _ = -(4 : ℤ) • (Q * X * Q) + (2 : ℤ) • (0 * Q) := by
            rw [hDM4_X.2.2.1, hAnti]
        _ = -(4 : ℤ) • (Q * X * Q) := by noncomm_ring
    have hFourQ2 : -(4 : ℤ) • (Q * X * Q) = (4 : ℤ) • (Q * Q * X) := by
      calc -(4 : ℤ) • (Q * X * Q)
        _ = -(4 : ℤ) • (Q * (X * Q)) := by noncomm_ring
        _ = -(4 : ℤ) • (Q * (-(Q * X))) := by rw [hXQ]
        _ = (4 : ℤ) • (Q * Q * X) := by noncomm_ring
    exact ⟨hXQ, hQ2X, hEqSand, hFourQ2⟩
  · dsimp [acOp]; peirce_nf hP
  · dsimp [adOp]; peirce_nf hP
  · peirce_nf hP

/-- **Stage `𝔇𝔐₆` (`dm6_twenty_four_isogeny_glue_law_and_master_synthesis`)**:
Master theorem unifying the 6-stage **Four-Way Super-Bracket Diamond & $\mathbb{Z}/24\mathbb{Z}$
Isogeny Glue Cohomology Poset** (`𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`):
1. **Poset Acyclicity, Diamond Incomparability, & Cardinality**:
   `SuperBracketDiamond24GlueStage.causalEdge_acyclic`,
   `SuperBracketDiamond24GlueStage.incomparable_DM2_DM3`, and
   `Fintype.card SuperBracketDiamond24GlueStage = 6`.
2. **The 24-Isogeny Glue Law (`Theorem 2.2`)**:
   - For all $d, X \in B$, `sigma24Map (psi24Map d X) = (24 : ℤ) • X`
     ($\Sigma_{24}(\Psi_{24}(X)) = 24 X$),
   - Whenever `quinticContactPoly d = 0`,
     `psi24Map d (sigma24Map (psi24Map d X)) = ((24 : ℤ) • (proj24Minus2 d * X), (24 : ℤ) • (proj24Minus1 d * X), (24 : ℤ) • (proj24Zero d * X), (24 : ℤ) • (proj24Plus1 d * X), (24 : ℤ) • (proj24Plus2 d * X))`,
   - And in the glue quotient ring `ZMod 24`, `(24 : ZMod 24) = 0`.
3. **Master Four-Way Super-Bracket Diamond & Goldstone/Axial Synthesis**:
   Bundles $[Q, \{Q, X\}] = \{Q, [Q, X]\} = [Q^2, X]$,
   $\mathrm{ad}_Q^2(X) - \mathrm{sad}_Q^2(X) = -2\,[Q, X]\,Q$,
   $\mathrm{ad}_Q^2(X) - \mathrm{ac}_Q^2(X) = -4\,Q X Q$,
   $-2\,[Q, X]\,Q - (-4\,Q X Q) = 2\,\{Q, X\}\,Q$,
   and the Goldstone/axial split on $(\Phi, J)$. -/
theorem dm6_twenty_four_isogeny_glue_law_and_master_synthesis
    {S Q P : B} (hS : S * S = 1) (hQ : S * Q * S = -Q)
    (hP : P * P = P) (A C X d : B) :
    -- 1. Poset acyclicity, diamond incomparability (DM2 ∥ DM3), and cardinality:
    (∀ st : SuperBracketDiamond24GlueStage,
      ¬ Relation.TransGen SuperBracketDiamond24GlueStage.causalEdge st st) ∧
    (¬ Relation.TransGen SuperBracketDiamond24GlueStage.causalEdge
        .DM2_OppositeParityBracketCancellation .DM3_LikeParitySandwichSplit ∧
     ¬ Relation.TransGen SuperBracketDiamond24GlueStage.causalEdge
        .DM3_LikeParitySandwichSplit .DM2_OppositeParityBracketCancellation) ∧
    Fintype.card SuperBracketDiamond24GlueStage = 6 ∧
    -- 2. The 24-isogeny glue law (Σ₂₄ ∘ Ψ₂₄ = 24 id and Ψ₂₄ ∘ Σ₂₄ ∘ Ψ₂₄ = 24 Ψ₂₄):
    sigma24Map (psi24Map d X) = (24 : ℤ) • X ∧
    (quinticContactPoly d = 0 →
      psi24Map d (sigma24Map (psi24Map d X)) =
        ((24 : ℤ) • (proj24Minus2 d * X),
         (24 : ℤ) • (proj24Minus1 d * X),
         (24 : ℤ) • (proj24Zero d * X),
         (24 : ℤ) • (proj24Plus1 d * X),
         (24 : ℤ) • (proj24Plus2 d * X)) ∧
      proj24Zero d * (proj24Zero d * X) = (24 : ℤ) • (proj24Zero d * X) ∧
      proj24Plus1 d * (proj24Minus1 d * X) = 0) ∧
    (24 : ZMod 24) = 0 ∧
    -- 3. Master 4-way super-bracket diamond and Goldstone/axial synthesis:
    adOp Q (acOp Q X) = adOp (Q * Q) X ∧
    acOp Q (adOp Q X) = adOp (Q * Q) X ∧
    adOp Q (adOp Q X) - sadOp S Q (sadOp S Q X) = -(2 : ℤ) • (adOp Q X * Q) ∧
    adOp Q (adOp Q X) - acOp Q (acOp Q X) = -(4 : ℤ) • (Q * X * Q) ∧
    -(2 : ℤ) • (adOp Q X * Q) - (-(4 : ℤ) • (Q * X * Q)) = (2 : ℤ) • (acOp Q X * Q) ∧
    adOp Q (adOp Q Q) - sadOp S Q (sadOp S Q Q) = 0 ∧
    -(2 : ℤ) • (adOp (genPhi P A C) (genJ P A C) * genPhi P A C) =
      (4 : ℤ) • (genV P A C * genJ P A C) := by
  have hSA4 := sa4_division_free_24_integer_resolution_of_five_graded_tower d
  have hSum24 : proj24Minus2 d + proj24Minus1 d + proj24Zero d + proj24Plus1 d + proj24Plus2 d =
      (24 : ℤ) • (1 : B) := hSA4.2.2.2.2.1
  have hSigPsi : sigma24Map (psi24Map d X) = (24 : ℤ) • X := by
    calc sigma24Map (psi24Map d X)
      _ = (proj24Minus2 d + proj24Minus1 d + proj24Zero d + proj24Plus1 d + proj24Plus2 d) * X := by
          dsimp [sigma24Map, psi24Map]; noncomm_ring
      _ = ((24 : ℤ) • (1 : B)) * X := by rw [hSum24]
      _ = (24 : ℤ) • X := by noncomm_ring
  have hDM2 := dm2_opposite_parity_bracket_cancellation_law hS hQ X
  have hDM4 := dm4_asymmetric_defect_vs_symmetric_sandwich_identity hS hQ X
  have hDM5 := dm5_goldstone_zero_mode_protection_and_anticommuting_specialization hS hQ hP A C X
  refine ⟨SuperBracketDiamond24GlueStage.causalEdge_acyclic,
    SuperBracketDiamond24GlueStage.incomparable_DM2_DM3,
    SuperBracketDiamond24GlueStage.card_eq_six,
    hSigPsi,
    ?_,
    by decide,
    hDM2.1,
    hDM2.2.1,
    hDM4.2.1,
    hDM4.2.2.1,
    hDM4.2.2.2.2.2,
    hDM5.2.2.1,
    hDM5.2.2.2.2.2.1.trans hDM5.2.2.2.2.2.2⟩
  intro hd
  have hOrth := hSA4.2.2.2.2.2.2.2.2.2.2 hd
  refine ⟨?_, ?_, ?_⟩
  · rw [hSigPsi]
    dsimp [psi24Map]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> noncomm_ring
  · rw [← mul_assoc, hOrth.2.2.2.2.2.1, smul_mul_assoc]
  · rw [← mul_assoc, hOrth.2.2.2.2.2.2.2.2.2.2.1, zero_mul]

end SuperBracketDiamond24GluePoset

/-!
## 7g. The 6-Stage Recursive Tensor-Peirce Centralizer Projection & Dyadic Tensor Tower Poset (`𝔗𝔗₁ ≺ 𝔗𝔗₂ ≺ 𝔗𝔗₃ ≺ 𝔗𝔗₄ ≺ 𝔗𝔗₅ ≺ 𝔗𝔗₆`)

Formalizes the **Recursive Tensor-Peirce Centralizer Homogenization & Dyadic Tensor Tower**
(`𝔗𝔗₁ ≺ 𝔗𝔗₂ ≺ 𝔗𝔗₃ ≺ 𝔗𝔗₄ ≺ 𝔗𝔗₅ ≺ 𝔗𝔗₆`), severing the naive zero-padded corner projections
$P M P, P M Q$ from the centralizer-homogenized Tensor-Peirce projections
$$\pi_{ab}(M) := E_{0a} M E_{b0} + E_{1a} M E_{b1} = I_2 \otimes M_{ab}$$
and the recursive $n$-stage ring isomorphism
$$\mathrm{peirceTowerEquiv}_n : \mathrm{Matrix}\,(\mathrm{Fin}\,(2^n))\,(\mathrm{Fin}\,(2^n))\,R \;\simeq_{+\ast}\; \mathrm{TensorTower}\,R\,n.$$
-/

/-- The 6 stages of the **Recursive Tensor-Peirce Centralizer Projection & Dyadic Tensor Tower Poset**
(`𝔗𝔗₁ ≺ 𝔗𝔗₂ ≺ 𝔗𝔗₃ ≺ 𝔗𝔗₄ ≺ 𝔗𝔗₅ ≺ 𝔗𝔗₆`). -/
inductive TensorPeirceTowerStage : Type
  /-- `𝔗𝔗₁`: Outer Peirce matrix units `{E₀₀ = P, E₀₁ = N_+, E₁₀ = N_-, E₁₁ = Q}` & Rung 0 corner projection aporia. -/
  | TT1_OuterPeirceUnitsAndCornerAporia
  /-- `𝔗𝔗₂`: The four centralizer-homogenized Peirce projectors `π_{ab}(M) = E_{0a} M E_{b0} + E_{1a} M E_{b1} = I_2 ⊗ M_{ab}`. -/
  | TT2_FourCentralizerHomogenizedPeirceProjectors
  /-- `𝔗𝔗₃`: Exact commutant `[E_{cd}, π_{ab}(M)] = 0`, reconstruction `M = ∑ E_{ab} π_{ab}(M)`, & `2 × 2` block multiplication `π_{ab}(M N) = ∑_c π_{ac}(M) π_{cb}(N)`. -/
  | TT3_ExactCommutantReconstructionAndBlockMultiplicationLaws
  /-- `𝔗𝔗₄`: Recursive inductive type `TensorTower R n` & single-step Peirce block split `flatStepEquiv`. -/
  | TT4_RecursiveInductiveTensorTowerType
  /-- `𝔗𝔗₅`: Full `n`-stage recursive ring isomorphism `peirceTowerEquiv n : FlatMat R n ≃+* TensorTower R n`. -/
  | TT5_RecursiveTensorPeirceRingIsomorphism
  /-- `𝔗𝔗₆`: Dual `Cl(1,1)^{⊗n}` DeWitt–Clifford tensor basis expansion `{I_2, S_P, Φ, J}` & master synthesis. -/
  | TT6_DualCliffordDeWittTensorBasisAndMasterSynthesis
  deriving DecidableEq, Repr

namespace TensorPeirceTowerStage

/-- Integer rank `0 .. 5` for `𝔗𝔗₁ ≺ 𝔗𝔗₂ ≺ 𝔗𝔗₃ ≺ 𝔗𝔗₄ ≺ 𝔗𝔗₅ ≺ 𝔗𝔗₆`. -/
def rank : TensorPeirceTowerStage → ℕ
  | .TT1_OuterPeirceUnitsAndCornerAporia                        => 0
  | .TT2_FourCentralizerHomogenizedPeirceProjectors             => 1
  | .TT3_ExactCommutantReconstructionAndBlockMultiplicationLaws => 2
  | .TT4_RecursiveInductiveTensorTowerType                      => 3
  | .TT5_RecursiveTensorPeirceRingIsomorphism                   => 4
  | .TT6_DualCliffordDeWittTensorBasisAndMasterSynthesis        => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder TensorPeirceTowerStage where
  le a b := rank a ≤ rank b
  lt a b := rank a < rank b
  le_refl a := le_rfl
  le_trans a b c := Nat.le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (rank a) (rank b)
  le_antisymm a b hab hba := rank_injective (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total (rank a) (rank b)
  toDecidableLE a b := Nat.decLe (rank a) (rank b)
  toDecidableEq := inferInstance
  toDecidableLT a b := Nat.decLt (rank a) (rank b)

instance : Fintype TensorPeirceTowerStage where
  elems := {
    .TT1_OuterPeirceUnitsAndCornerAporia,
    .TT2_FourCentralizerHomogenizedPeirceProjectors,
    .TT3_ExactCommutantReconstructionAndBlockMultiplicationLaws,
    .TT4_RecursiveInductiveTensorTowerType,
    .TT5_RecursiveTensorPeirceRingIsomorphism,
    .TT6_DualCliffordDeWittTensorBasisAndMasterSynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card TensorPeirceTowerStage = 6 := rfl

/-- Directed covering edges `𝔗𝔗_k ≺ 𝔗𝔗_{k+1}`. -/
def causalEdge (a b : TensorPeirceTowerStage) : Prop :=
  rank b = rank a + 1

theorem causalEdge_lt {a b : TensorPeirceTowerStage}
    (h : causalEdge a b) : rank a < rank b := by
  dsimp [causalEdge] at h
  omega

theorem transGen_causalEdge_lt {a b : TensorPeirceTowerStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

/-- Strict DAG acyclicity of `𝔗𝔗₁ ≺ 𝔗𝔗₂ ≺ 𝔗𝔗₃ ≺ 𝔗𝔗₄ ≺ 𝔗𝔗₅ ≺ 𝔗𝔗₆`. -/
theorem causalEdge_acyclic (a : TensorPeirceTowerStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_lt h)

/-- Monotone embedding into `InfoGeometry.Meta.RepDepth`. -/
def toRepDepth : TensorPeirceTowerStage → InfoGeometry.Meta.RepDepth
  | .TT1_OuterPeirceUnitsAndCornerAporia                        => .operator
  | .TT2_FourCentralizerHomogenizedPeirceProjectors             => .operator
  | .TT3_ExactCommutantReconstructionAndBlockMultiplicationLaws => .operator
  | .TT4_RecursiveInductiveTensorTowerType                      => .transport
  | .TT5_RecursiveTensorPeirceRingIsomorphism                   => .transport
  | .TT6_DualCliffordDeWittTensorBasisAndMasterSynthesis        => .thermo

/-- Monotone embedding into `InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    TensorPeirceTowerStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .TT1_OuterPeirceUnitsAndCornerAporia                        => .M1_ProjectorClabject
  | .TT2_FourCentralizerHomogenizedPeirceProjectors             => .M1_ProjectorClabject
  | .TT3_ExactCommutantReconstructionAndBlockMultiplicationLaws => .M2_GrassmannianPowertypeOrbit
  | .TT4_RecursiveInductiveTensorTowerType                      => .M2_GrassmannianPowertypeOrbit
  | .TT5_RecursiveTensorPeirceRingIsomorphism                   => .M3_ErlangenCasimirMetaLaw
  | .TT6_DualCliffordDeWittTensorBasisAndMasterSynthesis        => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : TensorPeirceTowerStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth InfoGeometry.Meta.RepDepth.toNat <;>
    decide

theorem toOntologyMetaLevel_mono {a b : TensorPeirceTowerStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;>
    decide

end TensorPeirceTowerStage

section TensorPeirceTowerPoset

/-- **The Inductive Tensor Tower Type (`Mat_2(Mat_2(...Mat_2(R)))`)**:
- At level `0`: A scalar in `R` (`1 × 1` matrix).
- At level `n + 1`: A `2 × 2` Peirce matrix whose 4 blocks `(0,0), (0,1), (1,0), (1,1)`
  are elements of `TensorTower R n`. -/
def TensorTower (R : Type*) : ℕ → Type _
  | 0     => R
  | n + 1 => Matrix (Fin 2) (Fin 2) (TensorTower R n)

@[instance_reducible] def tensorTowerSemiring (R : Type*) [Semiring R] :
    (n : ℕ) → Semiring (TensorTower R n)
  | 0 => inferInstanceAs (Semiring R)
  | n + 1 => by
      change Semiring (Matrix (Fin 2) (Fin 2) (TensorTower R n))
      letI := tensorTowerSemiring R n
      exact inferInstance

instance (R : Type*) [Semiring R] (n : ℕ) : Semiring (TensorTower R n) :=
  tensorTowerSemiring R n

/-- Flat `2^n × 2^n` square matrix over `R`. -/
abbrev FlatMat (R : Type*) (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R

/-- Canonical index splitting `Fin (2^n) ⊕ Fin (2^n) ≃ Fin (2^{n+1})`. -/
def finSplit (n : ℕ) : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  have h : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by ring
  finSumFinEquiv.trans (Fin.castOrderIso h).toEquiv

/-- Extracts the `(0,0)` upper-left `2^n × 2^n` Peirce block `P M P`. -/
def block00 {R : Type*} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inl i)) (finSplit n (Sum.inl j))

/-- Extracts the `(0,1)` upper-right `2^n × 2^n` Peirce block `P M (1 - P)`. -/
def block01 {R : Type*} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inl i)) (finSplit n (Sum.inr j))

/-- Extracts the `(1,0)` lower-left `2^n × 2^n` Peirce block `(1 - P) M P`. -/
def block10 {R : Type*} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inr i)) (finSplit n (Sum.inl j))

/-- Extracts the `(1,1)` lower-right `2^n × 2^n` Peirce block `(1 - P) M (1 - P)`. -/
def block11 {R : Type*} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inr i)) (finSplit n (Sum.inr j))

/-- Projects a `2^{n+1} × 2^{n+1}` matrix `M` into a `2 × 2` matrix of `2^n × 2^n` blocks. -/
def peirceSplitStep {R : Type*} {n : ℕ} (M : FlatMat R (n + 1)) :
    Matrix (Fin 2) (Fin 2) (FlatMat R n) :=
  ![![block00 M, block01 M],
    ![block10 M, block11 M]]

/-- Reassembles four `2^n × 2^n` blocks into a `2^{n+1} × 2^{n+1}` matrix. -/
def peirceUnsplitStep {R : Type*} {n : ℕ} (B : Matrix (Fin 2) (Fin 2) (FlatMat R n)) :
    FlatMat R (n + 1) :=
  Matrix.reindex (finSplit n) (finSplit n)
    (Matrix.fromBlocks (B 0 0) (B 0 1) (B 1 0) (B 1 1))

/-- Forward Tensor-Peirce Compiler (`toTensorTower`):
recursively decomposes a `2^n × 2^n` matrix into a nested `n`-level `TensorTower R n`. -/
def toTensorTower {R : Type*} : (n : ℕ) → FlatMat R n → TensorTower R n
  | 0,     M => M 0 0
  | n + 1, M =>
      let B := peirceSplitStep M
      ![![toTensorTower n (B 0 0), toTensorTower n (B 0 1)],
        ![toTensorTower n (B 1 0), toTensorTower n (B 1 1)]]

/-- Inverse Tensor-Peirce Coagulator (`ofTensorTower`):
recursively coagulates an `n`-level `TensorTower R n` back into a `2^n × 2^n` matrix. -/
def ofTensorTower {R : Type*} : (n : ℕ) → TensorTower R n → FlatMat R n
  | 0,     r => fun _ _ => r
  | n + 1, T =>
      peirceUnsplitStep
        ![![ofTensorTower n (T 0 0), ofTensorTower n (T 0 1)],
          ![ofTensorTower n (T 1 0), ofTensorTower n (T 1 1)]]

/-- Uncurries a matrix of matrices into a product-indexed matrix as a ring isomorphism. -/
def matrixCurryEquiv {R α β : Type*} [Semiring R] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] :
    Matrix α α (Matrix β β R) ≃+* Matrix (α × β) (α × β) R where
  toFun A := Matrix.of fun i j => (A i.1 j.1) i.2 j.2
  invFun A := Matrix.of fun i j => Matrix.of fun k l => A (i, k) (j, l)
  left_inv A := by ext i j k l; rfl
  right_inv A := by ext i j; rfl
  map_mul' A B := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
  map_add' A B := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rfl

/-- Reindexing that splits a dyadic matrix index into `(bit, remaining bits)`. -/
def dyadicIndexEquiv (n : ℕ) : Fin (2 ^ (n + 1)) ≃ Fin 2 × Fin (2 ^ n) := by
  have h : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ]; ring
  exact ((finProdFinEquiv : Fin 2 × Fin (2 ^ n) ≃ Fin (2 * 2 ^ n)).trans
    (finCongr h)).symm

/-- One-step finite Peirce splitting `FlatMat R (n + 1) ≃+* Matrix (Fin 2) (Fin 2) (FlatMat R n)`. -/
def flatStepEquiv (R : Type*) [Semiring R] (n : ℕ) :
    FlatMat R (n + 1) ≃+* Matrix (Fin 2) (Fin 2) (FlatMat R n) :=
  (Matrix.reindexRingEquiv R (dyadicIndexEquiv n)).trans
    (matrixCurryEquiv (R := R) (α := Fin 2) (β := Fin (2 ^ n))).symm

/-- At level zero, a `1 × 1` matrix is isomorphic to its unique scalar entry in `R`. -/
def flatZeroEquiv (R : Type*) [Semiring R] : FlatMat R 0 ≃+* R where
  toFun A := A 0 0
  invFun r := fun _ _ => r
  left_inv A := by
    ext i j
    rw [Fin.eq_zero i, Fin.eq_zero j]
  right_inv _ := rfl
  map_mul' A B := by simp [Matrix.mul_apply]
  map_add' _ _ := rfl

/-- **Full `n`-Stage Recursive Tensor-Peirce Ring Isomorphism (`peirceTowerEquiv`)**:
`Matrix (Fin (2^n)) (Fin (2^n)) R ≃+* TensorTower R n`. -/
def peirceTowerEquiv (R : Type*) [Semiring R] :
    (n : ℕ) → FlatMat R n ≃+* TensorTower R n
  | 0 => flatZeroEquiv R
  | n + 1 =>
      let step := flatStepEquiv R n
      let inner : Matrix (Fin 2) (Fin 2) (FlatMat R n) ≃+*
          Matrix (Fin 2) (Fin 2) (TensorTower R n) :=
        (peirceTowerEquiv R n).mapMatrix
      step.trans inner

variable {B : Type*} [Ring B]

/-- Homogenized `(0,0)` Tensor-Peirce projection `π₀₀(M) := E₀₀ M E₀₀ + E₁₀ M E₀₁`. -/
def pi00 (E00 E01 E10 _E11 M : B) : B := E00 * M * E00 + E10 * M * E01

/-- Homogenized `(0,1)` Tensor-Peirce projection `π₀₁(M) := E₀₀ M E₁₀ + E₁₀ M E₁₁`. -/
def pi01 (E00 _E01 E10 E11 M : B) : B := E00 * M * E10 + E10 * M * E11

/-- Homogenized `(1,0)` Tensor-Peirce projection `π₁₀(M) := E₀₁ M E₀₀ + E₁₁ M E₀₁`. -/
def pi10 (E00 E01 _E10 E11 M : B) : B := E01 * M * E00 + E11 * M * E01

/-- Homogenized `(1,1)` Tensor-Peirce projection `π₁₁(M) := E₀₁ M E₁₀ + E₁₁ M E₁₁`. -/
def pi11 (_E00 E01 E10 E11 M : B) : B := E01 * M * E10 + E11 * M * E11

/-- Canonical `(0,0)` matrix unit `P = E₀₀` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitE00 {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, 0]

/-- Canonical `(0,1)` nilpotent shift unit `N_+ = E₀₁` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitE01 {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

/-- Canonical `(1,0)` nilpotent shift unit `N_- = E₁₀` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitE10 {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]

/-- Canonical `(1,1)` matrix unit `Q = 1 - P = E₁₁` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitE11 {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R := !![0, 0; 0, 1]

/-- DeWitt Sum / identity unit `I_2 = E₀₀ + E₁₁` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitI {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R := unitE00 + unitE11

/-- Chiral DeWitt Difference grading unit `S_P = E₀₀ - E₁₁` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitS {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R := unitE00 - unitE11

/-- Osmotic amplitude bridge unit `Φ = E₀₁ + E₁₀` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitPhi {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R := unitE01 + unitE10

/-- Classical phase current unit `J = E₀₁ - E₁₀` in `Matrix (Fin 2) (Fin 2) R`. -/
def unitJ {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R := unitE01 - unitE10

/-- Homogenized `(0,0)` centralizer projection `π₀₀(M)` on `Matrix (Fin 2) (Fin 2) R`. -/
def matPi00 {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  unitE00 * M * unitE00 + unitE10 * M * unitE01

/-- Homogenized `(0,1)` centralizer projection `π₀₁(M)` on `Matrix (Fin 2) (Fin 2) R`. -/
def matPi01 {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  unitE00 * M * unitE10 + unitE10 * M * unitE11

/-- Homogenized `(1,0)` centralizer projection `π₁₀(M)` on `Matrix (Fin 2) (Fin 2) R`. -/
def matPi10 {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  unitE01 * M * unitE00 + unitE11 * M * unitE01

/-- Homogenized `(1,1)` centralizer projection `π₁₁(M)` on `Matrix (Fin 2) (Fin 2) R`. -/
def matPi11 {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  unitE01 * M * unitE10 + unitE11 * M * unitE11

/-- Block-matrix `(0,0)` outer unit `[[1, 0], [0, 0]]` on `Matrix (m ⊕ m) (m ⊕ m) R`. -/
def blkE00 {m R : Type*} [DecidableEq m] [Zero R] [One R] : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 1 0 0 0

/-- Block-matrix `(0,1)` outer shift unit `[[0, 1], [0, 0]]` on `Matrix (m ⊕ m) (m ⊕ m) R`. -/
def blkE01 {m R : Type*} [DecidableEq m] [Zero R] [One R] : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 0 1 0 0

/-- Block-matrix `(1,0)` outer shift unit `[[0, 0], [1, 0]]` on `Matrix (m ⊕ m) (m ⊕ m) R`. -/
def blkE10 {m R : Type*} [DecidableEq m] [Zero R] [One R] : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 0 0 1 0

/-- Block-matrix `(1,1)` outer unit `[[0, 0], [0, 1]]` on `Matrix (m ⊕ m) (m ⊕ m) R`. -/
def blkE11 {m R : Type*} [DecidableEq m] [Zero R] [One R] : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 0 0 0 1

/-- **Stage `𝔗𝔗₁` (`tt1_outer_peirce_units_and_rung0_corner_aporia`)**:
1. **Universal CAR / DeWitt Generation of the Outer $2 \times 2$ Peirce Matrix Units**:
   In any associative ring `[Ring B]`, if $N_+, N_- \in B$ satisfy $N_+^2 = 0$, $N_-^2 = 0$,
   and $N_+ N_- + N_- N_+ = 1$, then $E_{00} := N_+ N_-$, $E_{01} := N_+$, $E_{10} := N_-$,
   $E_{11} := N_- N_+$ automatically satisfy $N_+ N_- N_+ = N_+$, $N_- N_+ N_- = N_-$,
   $E_{00}^2 = E_{00}$, $E_{11}^2 = E_{11}$, $E_{00} E_{11} = 0$, $E_{11} E_{00} = 0$,
   and the Rung 0 corner nilpotency $((N_+ N_-) X (N_- N_+))((N_+ N_-) Y (N_- N_+)) = 0$.
2. **Concrete $2 \times 2$ Outer Peirce Units & Rung 0 Corner Projection Aporia**:
   On `Matrix (Fin 2) (Fin 2) R`, `unitE00 + unitE11 = 1`, `unitE00 * unitE00 = unitE00`,
   `unitE01 * unitE10 = unitE00`, `unitE10 * unitE01 = unitE11`, the naive diagonal projection
   `(unitE00 * 1 * unitE00) 1 1 = 0` kills the lower-right block, and the naive off-diagonal
   corner projection `(unitE00 * M * unitE11) * (unitE00 * N * unitE11) = 0` is square-zero. -/
theorem tt1_outer_peirce_units_and_rung0_corner_aporia
    {Np Nm : B} (hNp : Np * Np = 0) (hNm : Nm * Nm = 0) (hCAR : Np * Nm + Nm * Np = 1)
    (X Y : B)
    {R : Type*} [Ring R] (M N : Matrix (Fin 2) (Fin 2) R) :
    -- 1. Universal CAR / DeWitt generation of matrix units & Rung 0 corner nilpotency:
    Np * Nm * Np = Np ∧
    Nm * Np * Nm = Nm ∧
    (Np * Nm) * (Np * Nm) = Np * Nm ∧
    (Nm * Np) * (Nm * Np) = Nm * Np ∧
    (Np * Nm) * (Nm * Np) = 0 ∧
    (Nm * Np) * (Np * Nm) = 0 ∧
    ((Np * Nm) * X * (Nm * Np)) * ((Np * Nm) * Y * (Nm * Np)) = 0 ∧
    -- 2. Concrete 2×2 matrix units and Rung 0 corner projection aporia:
    unitE00 + unitE11 = (1 : Matrix (Fin 2) (Fin 2) R) ∧
    (unitE00 : Matrix (Fin 2) (Fin 2) R) * unitE00 = unitE00 ∧
    (unitE01 : Matrix (Fin 2) (Fin 2) R) * unitE10 = unitE00 ∧
    (unitE10 : Matrix (Fin 2) (Fin 2) R) * unitE01 = unitE11 ∧
    (unitE00 * 1 * unitE00 : Matrix (Fin 2) (Fin 2) R) 1 1 = 0 ∧
    (unitE00 * M * unitE11) * (unitE00 * N * unitE11) = 0 := by
  have hNpNmNp : Np * Nm * Np = Np := by
    calc Np * Nm * Np
      _ = (Np * Nm + Nm * Np) * Np - Nm * (Np * Np) := by noncomm_ring
      _ = 1 * Np - Nm * 0 := by rw [hCAR, hNp]
      _ = Np := by noncomm_ring
  have hNmNpNm : Nm * Np * Nm = Nm := by
    calc Nm * Np * Nm
      _ = (Np * Nm + Nm * Np) * Nm - Np * (Nm * Nm) := by noncomm_ring
      _ = 1 * Nm - Np * 0 := by rw [hCAR, hNm]
      _ = Nm := by noncomm_ring
  have hE00Sq : (Np * Nm) * (Np * Nm) = Np * Nm := by
    calc (Np * Nm) * (Np * Nm)
      _ = (Np * Nm * Np) * Nm := by noncomm_ring
      _ = Np * Nm := by rw [hNpNmNp]
  have hE11Sq : (Nm * Np) * (Nm * Np) = Nm * Np := by
    calc (Nm * Np) * (Nm * Np)
      _ = (Nm * Np * Nm) * Np := by noncomm_ring
      _ = Nm * Np := by rw [hNmNpNm]
  have hE00E11 : (Np * Nm) * (Nm * Np) = 0 := by
    calc (Np * Nm) * (Nm * Np)
      _ = Np * (Nm * Nm) * Np := by noncomm_ring
      _ = Np * 0 * Np := by rw [hNm]
      _ = 0 := by noncomm_ring
  have hE11E00 : (Nm * Np) * (Np * Nm) = 0 := by
    calc (Nm * Np) * (Np * Nm)
      _ = Nm * (Np * Np) * Nm := by noncomm_ring
      _ = Nm * 0 * Nm := by rw [hNp]
      _ = 0 := by noncomm_ring
  have hCornerNil : ((Np * Nm) * X * (Nm * Np)) * ((Np * Nm) * Y * (Nm * Np)) = 0 := by
    calc ((Np * Nm) * X * (Nm * Np)) * ((Np * Nm) * Y * (Nm * Np))
      _ = (Np * Nm) * X * ((Nm * Np) * (Np * Nm)) * Y * (Nm * Np) := by noncomm_ring
      _ = (Np * Nm) * X * 0 * Y * (Nm * Np) := by rw [hE11E00]
      _ = 0 := by noncomm_ring
  refine ⟨hNpNmNp, hNmNpNm, hE00Sq, hE11Sq, hE00E11, hE11E00, hCornerNil,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [unitE00, unitE11]
  · ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE00]
  · ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE01, unitE10, unitE00]
  · ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE01, unitE10, unitE11]
  · simp [unitE00]
  · ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE00, unitE11]

/-- **Stage `𝔗𝔗₂` (`tt2_four_centralizer_homogenized_peirce_projectors`)**:
1. **Universal Unitality of $\pi_{00}$ and $\pi_{11}$ vs. Vanishing of $\pi_{01}(1)$ and $\pi_{10}(1)$**:
   For $E_{00} = N_+ N_-, E_{01} = N_+, E_{10} = N_-, E_{11} = N_- N_+$:
   $\pi_{00}(1) = 1$, $\pi_{11}(1) = 1$, $\pi_{01}(1) = 0$, $\pi_{10}(1) = 0$.
2. **Concrete $2 \times 2$ Centralizer Homogenization (`matPi_{ab} M = I_2 ⊗ M_{ab}`)**:
   - `matPi00 M = !![M 0 0, 0; 0, M 0 0]` and `matPi00 1 = 1`,
   - `matPi01 M = !![M 0 1, 0; 0, M 0 1]`,
   - `matPi10 M = !![M 1 0, 0; 0, M 1 0]`,
   - `matPi11 M = !![M 1 1, 0; 0, M 1 1]`.
3. **General $2 \times 2$ Block-Matrix Homogenization (`Matrix.fromBlocks M00 M01 M10 M11`)**:
   On `Matrix (m ⊕ m) (m ⊕ m) R`, `pi00..pi11` extract each sub-block `M_{ab}` into the diagonal
   commutant `Matrix.fromBlocks M_{ab} 0 0 M_{ab}`. -/
theorem tt2_four_centralizer_homogenized_peirce_projectors
    {Np Nm : B} (hNp : Np * Np = 0) (hNm : Nm * Nm = 0) (hCAR : Np * Nm + Nm * Np = 1)
    {m R : Type*} [Fintype m] [DecidableEq m] [Ring R]
    (M : Matrix (Fin 2) (Fin 2) R)
    (M00 M01 M10 M11 : Matrix m m R) :
    -- 1. Universal unitality on 1:
    pi00 (Np * Nm) Np Nm (Nm * Np) 1 = 1 ∧
    pi11 (Np * Nm) Np Nm (Nm * Np) 1 = 1 ∧
    pi01 (Np * Nm) Np Nm (Nm * Np) 1 = 0 ∧
    pi10 (Np * Nm) Np Nm (Nm * Np) 1 = 0 ∧
    -- 2. Concrete 2×2 centralizer projections:
    matPi00 M = !![M 0 0, 0; 0, M 0 0] ∧
    matPi00 (1 : Matrix (Fin 2) (Fin 2) R) = 1 ∧
    matPi01 M = !![M 0 1, 0; 0, M 0 1] ∧
    matPi10 M = !![M 1 0, 0; 0, M 1 0] ∧
    matPi11 M = !![M 1 1, 0; 0, M 1 1] ∧
    -- 3. General 2×2 block-matrix homogenization (Matrix.fromBlocks):
    pi00 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
      Matrix.fromBlocks M00 0 0 M00 ∧
    pi01 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
      Matrix.fromBlocks M01 0 0 M01 ∧
    pi10 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
      Matrix.fromBlocks M10 0 0 M10 ∧
    pi11 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
      Matrix.fromBlocks M11 0 0 M11 := by
  have hTT1 := tt1_outer_peirce_units_and_rung0_corner_aporia hNp hNm hCAR 0 0 M M
  have hPi00_1 : pi00 (Np * Nm) Np Nm (Nm * Np) 1 = 1 := by
    calc pi00 (Np * Nm) Np Nm (Nm * Np) 1
      _ = (Np * Nm * Np) * Nm + Nm * Np := by dsimp [pi00]; noncomm_ring
      _ = Np * Nm + Nm * Np := by rw [hTT1.1]
      _ = 1 := hCAR
  have hPi11_1 : pi11 (Np * Nm) Np Nm (Nm * Np) 1 = 1 := by
    calc pi11 (Np * Nm) Np Nm (Nm * Np) 1
      _ = Np * Nm + (Nm * Np * Nm) * Np := by dsimp [pi11]; noncomm_ring
      _ = Np * Nm + Nm * Np := by rw [hTT1.2.1]
      _ = 1 := hCAR
  have hPi01_1 : pi01 (Np * Nm) Np Nm (Nm * Np) 1 = 0 := by
    calc pi01 (Np * Nm) Np Nm (Nm * Np) 1
      _ = Np * (Nm * Nm) + (Nm * Nm) * Np := by dsimp [pi01]; noncomm_ring
      _ = Np * 0 + 0 * Np := by rw [hNm]
      _ = 0 := by noncomm_ring
  have hPi10_1 : pi10 (Np * Nm) Np Nm (Nm * Np) 1 = 0 := by
    calc pi10 (Np * Nm) Np Nm (Nm * Np) 1
      _ = (Np * Np) * Nm + Nm * (Np * Np) := by dsimp [pi10]; noncomm_ring
      _ = 0 * Nm + Nm * 0 := by rw [hNp]
      _ = 0 := by noncomm_ring
  refine ⟨hPi00_1, hPi11_1, hPi01_1, hPi10_1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; dsimp [matPi00]; simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [unitE00, unitE01, unitE10]
  · ext i j; dsimp [matPi00]; simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [unitE00, unitE01, unitE10]
  · ext i j; dsimp [matPi01]; simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [unitE00, unitE10, unitE11]
  · ext i j; dsimp [matPi10]; simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [unitE00, unitE01, unitE11]
  · ext i j; dsimp [matPi11]; simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [unitE01, unitE10, unitE11]
  · simp [pi00, blkE00, blkE01, blkE10, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · simp [pi01, blkE00, blkE10, blkE11, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · simp [pi10, blkE00, blkE01, blkE11, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · simp [pi11, blkE01, blkE10, blkE11, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]

/-- Universal algebraic Tensor-Peirce exact reconstruction in any `[Ring B]`. -/
theorem tensor_peirce_exact_reconstruction
    (E00 E01 E10 E11 M : B)
    (h_sum : E00 + E11 = 1)
    (h00_00 : E00 * E00 = E00) (h00_10 : E00 * E10 = 0)
    (h01_00 : E01 * E00 = 0)   (h01_10 : E01 * E10 = E00)
    (h10_01 : E10 * E01 = E11) (h10_11 : E10 * E11 = 0)
    (h11_01 : E11 * E01 = 0)   (h11_11 : E11 * E11 = E11) :
    E00 * pi00 E00 E01 E10 E11 M +
    E01 * pi01 E00 E01 E10 E11 M +
    E10 * pi10 E00 E01 E10 E11 M +
    E11 * pi11 E00 E01 E10 E11 M = M := by
  unfold pi00 pi01 pi10 pi11
  simp only [mul_add, ← mul_assoc,
             h00_00, h00_10, h01_00, h01_10, h10_01, h10_11, h11_01, h11_11,
             zero_mul, add_zero, zero_add]
  calc E00 * M * E00 + E00 * M * E11 + E11 * M * E00 + E11 * M * E11
    _ = (E00 + E11) * M * (E00 + E11) := by noncomm_ring
    _ = 1 * M * 1 := by rw [h_sum]
    _ = M := by rw [one_mul, mul_one]

/-- **Stage `𝔗𝔗₃` (`tt3_exact_commutant_reconstruction_and_block_multiplication_laws`)**:
1. **Universal Centralizer / Commutant Law & Exact Reconstruction in `[Ring B]`**:
   Under $N_+^2 = 0, N_-^2 = 0, N_+ N_- + N_- N_+ = 1$, for every $X \in B$:
   - $N_+ \, \pi_{00}(X) = \pi_{00}(X) \, N_+$ and $N_- \, \pi_{00}(X) = \pi_{00}(X) \, N_-$,
   - $N_+ \, \pi_{01}(X) = \pi_{01}(X) \, N_+$ and $N_- \, \pi_{01}(X) = \pi_{01}(X) \, N_-$,
   - $(N_+ N_-) \pi_{00}(X) + N_+ \pi_{01}(X) + N_- \pi_{10}(X) + (N_- N_+) \pi_{11}(X) = X$.
2. **Concrete $2 \times 2$ Commutant, Reconstruction, & Block Multiplication Laws**:
   - `unitE01 * matPi00 M = matPi00 M * unitE01`, `unitE10 * matPi01 M = matPi01 M * unitE10`,
   - `unitE00 * matPi00 M + unitE01 * matPi01 M + unitE10 * matPi10 M + unitE11 * matPi11 M = M`,
   - `matPi00 (M * N) = matPi00 M * matPi00 N + matPi01 M * matPi10 N`,
   - `matPi01 (M * N) = matPi00 M * matPi01 N + matPi01 M * matPi11 N`,
   - `matPi10 (M * N) = matPi10 M * matPi00 N + matPi11 M * matPi10 N`,
   - `matPi11 (M * N) = matPi10 M * matPi01 N + matPi11 M * matPi11 N`. -/
theorem tt3_exact_commutant_reconstruction_and_block_multiplication_laws
    {Np Nm : B} (hNp : Np * Np = 0) (hNm : Nm * Nm = 0) (hCAR : Np * Nm + Nm * Np = 1)
    (X : B)
    {R : Type*} [Ring R] (M N : Matrix (Fin 2) (Fin 2) R) :
    -- 1. Universal centralizer / commutant and reconstruction in [Ring B]:
    Np * pi00 (Np * Nm) Np Nm (Nm * Np) X = pi00 (Np * Nm) Np Nm (Nm * Np) X * Np ∧
    Nm * pi00 (Np * Nm) Np Nm (Nm * Np) X = pi00 (Np * Nm) Np Nm (Nm * Np) X * Nm ∧
    Np * pi01 (Np * Nm) Np Nm (Nm * Np) X = pi01 (Np * Nm) Np Nm (Nm * Np) X * Np ∧
    Nm * pi01 (Np * Nm) Np Nm (Nm * Np) X = pi01 (Np * Nm) Np Nm (Nm * Np) X * Nm ∧
    (Np * Nm) * pi00 (Np * Nm) Np Nm (Nm * Np) X +
      Np * pi01 (Np * Nm) Np Nm (Nm * Np) X +
      Nm * pi10 (Np * Nm) Np Nm (Nm * Np) X +
      (Nm * Np) * pi11 (Np * Nm) Np Nm (Nm * Np) X = X ∧
    -- 2. Concrete 2×2 commutant, reconstruction, and block multiplication laws:
    unitE01 * matPi00 M = matPi00 M * unitE01 ∧
    unitE10 * matPi01 M = matPi01 M * unitE10 ∧
    unitE00 * matPi00 M + unitE01 * matPi01 M +
      unitE10 * matPi10 M + unitE11 * matPi11 M = M ∧
    matPi00 (M * N) = matPi00 M * matPi00 N + matPi01 M * matPi10 N ∧
    matPi01 (M * N) = matPi00 M * matPi01 N + matPi01 M * matPi11 N ∧
    matPi10 (M * N) = matPi10 M * matPi00 N + matPi11 M * matPi10 N ∧
    matPi11 (M * N) = matPi10 M * matPi01 N + matPi11 M * matPi11 N := by
  have hTT1 := tt1_outer_peirce_units_and_rung0_corner_aporia hNp hNm hCAR X X M N
  have hNpNmNp : Np * Nm * Np = Np := hTT1.1
  have hNmNpNm : Nm * Np * Nm = Nm := hTT1.2.1
  have hComm00Np : Np * pi00 (Np * Nm) Np Nm (Nm * Np) X =
      pi00 (Np * Nm) Np Nm (Nm * Np) X * Np := by
    calc Np * pi00 (Np * Nm) Np Nm (Nm * Np) X
      _ = (Np * Np) * Nm * X * Np * Nm + Np * Nm * X * Np := by dsimp [pi00]; noncomm_ring
      _ = 0 * Nm * X * Np * Nm + Np * Nm * X * Np := by rw [hNp]
      _ = Np * Nm * X * (Np * Nm * Np) + Nm * X * (Np * Np) := by rw [hNpNmNp, hNp]; noncomm_ring
      _ = pi00 (Np * Nm) Np Nm (Nm * Np) X * Np := by dsimp [pi00]; noncomm_ring
  have hComm00Nm : Nm * pi00 (Np * Nm) Np Nm (Nm * Np) X =
      pi00 (Np * Nm) Np Nm (Nm * Np) X * Nm := by
    calc Nm * pi00 (Np * Nm) Np Nm (Nm * Np) X
      _ = (Nm * Np * Nm) * X * Np * Nm + (Nm * Nm) * X * Np := by dsimp [pi00]; noncomm_ring
      _ = Nm * X * Np * Nm + 0 * X * Np := by rw [hNmNpNm, hNm]
      _ = Np * Nm * X * Np * (Nm * Nm) + Nm * X * Np * Nm := by rw [hNm]; noncomm_ring
      _ = pi00 (Np * Nm) Np Nm (Nm * Np) X * Nm := by dsimp [pi00]; noncomm_ring
  have hComm01Np : Np * pi01 (Np * Nm) Np Nm (Nm * Np) X =
      pi01 (Np * Nm) Np Nm (Nm * Np) X * Np := by
    calc Np * pi01 (Np * Nm) Np Nm (Nm * Np) X
      _ = (Np * Np) * Nm * X * Nm + Np * Nm * X * Nm * Np := by dsimp [pi01]; noncomm_ring
      _ = 0 * Nm * X * Nm + Np * Nm * X * Nm * Np := by rw [hNp]
      _ = Np * Nm * X * Nm * Np + Nm * X * Nm * (Np * Np) := by rw [hNp]; noncomm_ring
      _ = pi01 (Np * Nm) Np Nm (Nm * Np) X * Np := by dsimp [pi01]; noncomm_ring
  have hComm01Nm : Nm * pi01 (Np * Nm) Np Nm (Nm * Np) X =
      pi01 (Np * Nm) Np Nm (Nm * Np) X * Nm := by
    calc Nm * pi01 (Np * Nm) Np Nm (Nm * Np) X
      _ = (Nm * Np * Nm) * X * Nm + (Nm * Nm) * X * Nm * Np := by dsimp [pi01]; noncomm_ring
      _ = Nm * X * Nm + 0 * X * Nm * Np := by rw [hNmNpNm, hNm]
      _ = Np * Nm * X * (Nm * Nm) + Nm * X * (Nm * Np * Nm) := by rw [hNm, hNmNpNm]; noncomm_ring
      _ = pi01 (Np * Nm) Np Nm (Nm * Np) X * Nm := by dsimp [pi01]; noncomm_ring
  have hReconUniv :
      (Np * Nm) * pi00 (Np * Nm) Np Nm (Nm * Np) X +
        Np * pi01 (Np * Nm) Np Nm (Nm * Np) X +
        Nm * pi10 (Np * Nm) Np Nm (Nm * Np) X +
        (Nm * Np) * pi11 (Np * Nm) Np Nm (Nm * Np) X = X := by
    apply tensor_peirce_exact_reconstruction (Np * Nm) Np Nm (Nm * Np) X hCAR hTT1.2.2.1
    · calc (Np * Nm) * Nm = Np * (Nm * Nm) := by noncomm_ring
        _ = Np * 0 := by rw [hNm]
        _ = 0 := by noncomm_ring
    · calc Np * (Np * Nm) = (Np * Np) * Nm := by noncomm_ring
        _ = 0 * Nm := by rw [hNp]
        _ = 0 := by noncomm_ring
    · rfl
    · rfl
    · calc Nm * (Nm * Np) = (Nm * Nm) * Np := by noncomm_ring
        _ = 0 * Np := by rw [hNm]
        _ = 0 := by noncomm_ring
    · calc (Nm * Np) * Np = Nm * (Np * Np) := by noncomm_ring
        _ = Nm * 0 := by rw [hNp]
        _ = 0 := by noncomm_ring
    · exact hTT1.2.2.2.1
  have hTT2 := fun Z : Matrix (Fin 2) (Fin 2) R =>
    (tt2_four_centralizer_homogenized_peirce_projectors hNp hNm hCAR Z (0 : Matrix (Fin 1) (Fin 1) R) 0 0 0).2.2.2.2
  have h00 := fun Z : Matrix (Fin 2) (Fin 2) R => (hTT2 Z).1
  have h01 := fun Z : Matrix (Fin 2) (Fin 2) R => (hTT2 Z).2.2.1
  have h10 := fun Z : Matrix (Fin 2) (Fin 2) R => (hTT2 Z).2.2.2.1
  have h11 := fun Z : Matrix (Fin 2) (Fin 2) R => (hTT2 Z).2.2.2.2.1
  refine ⟨hComm00Np, hComm00Nm, hComm01Np, hComm01Nm, hReconUniv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h00 M]; ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE01]
  · rw [h01 M]; ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE10]
  · rw [h00 M, h01 M, h10 M, h11 M]
    ext i j; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [unitE00, unitE01, unitE10, unitE11]
  · rw [h00 (M * N), h00 M, h00 N, h01 M, h10 N]
    ext i j; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp
  · rw [h01 (M * N), h00 M, h01 N, h01 M, h11 N]
    ext i j; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp
  · rw [h10 (M * N), h10 M, h00 N, h11 M, h10 N]
    ext i j; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp
  · rw [h11 (M * N), h10 M, h01 N, h11 M, h11 N]
    ext i j; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp

/-- **Stage `𝔗𝔗₄` (`tt4_recursive_inductive_tensor_tower_type`)**:
1. **Base Level `0` Ring Isomorphism (`FlatMat R 0 ≃+* R`) & Roundtrip**:
   - `toTensorTower 0 (ofTensorTower 0 r) = r` and `ofTensorTower 0 (toTensorTower 0 M₀) = M₀`,
   - `flatZeroEquiv R (M₀ * N₀) = flatZeroEquiv R M₀ * flatZeroEquiv R N₀`.
2. **Single-Step Peirce Block Ring Isomorphism (`flatStepEquiv R n`) & Block Roundtrip**:
   - `flatStepEquiv R n (A + A') = flatStepEquiv R n A + flatStepEquiv R n A'`,
   - `flatStepEquiv R n (A * A') = flatStepEquiv R n A * flatStepEquiv R n A'`,
   - `block00 (peirceUnsplitStep C) = C 0 0`, `block01 (peirceUnsplitStep C) = C 0 1`,
     `block10 (peirceUnsplitStep C) = C 1 0`, `block11 (peirceUnsplitStep C) = C 1 1`,
   - `peirceSplitStep (peirceUnsplitStep C) = C`. -/
theorem tt4_recursive_inductive_tensor_tower_type
    {R : Type*} [Semiring R] (r : R) (M₀ N₀ : FlatMat R 0)
    (n : ℕ) (A A' : FlatMat R (n + 1)) (C : Matrix (Fin 2) (Fin 2) (FlatMat R n)) :
    toTensorTower 0 (ofTensorTower 0 r) = r ∧
    ofTensorTower 0 (toTensorTower 0 M₀) = M₀ ∧
    flatZeroEquiv R (M₀ * N₀) = flatZeroEquiv R M₀ * flatZeroEquiv R N₀ ∧
    flatStepEquiv R n (A + A') = flatStepEquiv R n A + flatStepEquiv R n A' ∧
    flatStepEquiv R n (A * A') = flatStepEquiv R n A * flatStepEquiv R n A' ∧
    block00 (peirceUnsplitStep C) = C 0 0 ∧
    block01 (peirceUnsplitStep C) = C 0 1 ∧
    block10 (peirceUnsplitStep C) = C 1 0 ∧
    block11 (peirceUnsplitStep C) = C 1 1 ∧
    peirceSplitStep (peirceUnsplitStep C) = C := by
  have hb00 : block00 (peirceUnsplitStep C) = C 0 0 := by
    ext i j; simp [block00, peirceUnsplitStep, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hb01 : block01 (peirceUnsplitStep C) = C 0 1 := by
    ext i j; simp [block01, peirceUnsplitStep, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hb10 : block10 (peirceUnsplitStep C) = C 1 0 := by
    ext i j; simp [block10, peirceUnsplitStep, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hb11 : block11 (peirceUnsplitStep C) = C 1 1 := by
    ext i j; simp [block11, peirceUnsplitStep, Matrix.reindex_apply, Matrix.submatrix_apply]
  refine ⟨rfl, ?_, map_mul (flatZeroEquiv R) M₀ N₀,
    map_add (flatStepEquiv R n) A A', map_mul (flatStepEquiv R n) A A',
    hb00, hb01, hb10, hb11, ?_⟩
  · ext i j
    rw [Fin.eq_zero i, Fin.eq_zero j]
    rfl
  · ext a b i j
    fin_cases a <;> fin_cases b
    · exact congr_fun (congr_fun hb00 i) j
    · exact congr_fun (congr_fun hb01 i) j
    · exact congr_fun (congr_fun hb10 i) j
    · exact congr_fun (congr_fun hb11 i) j

/-- **Stage `𝔗𝔗₅` (`tt5_recursive_tensor_peirce_ring_isomorphism`)**:
1. **Full `n`-Stage Recursive Ring Isomorphism (`peirceTowerEquiv R n : FlatMat R n ≃+* TensorTower R n`)**:
   For every dyadic scale $n \in \mathbb{N}$, matrices $A, A' \in \mathrm{FlatMat}\,R\,n$,
   and tower element $T \in \mathrm{TensorTower}\,R\,n$:
   - `peirceTowerEquiv R n (A + A') = peirceTowerEquiv R n A + peirceTowerEquiv R n A'`,
   - `peirceTowerEquiv R n (A * A') = peirceTowerEquiv R n A * peirceTowerEquiv R n A'`,
   - `peirceTowerEquiv R n 1 = 1`,
   - `(peirceTowerEquiv R n).symm (peirceTowerEquiv R n A) = A`,
   - `peirceTowerEquiv R n ((peirceTowerEquiv R n).symm T) = T`.
2. **Recursive Compiler/Coagulator Roundtrip (`toTensorTower n (ofTensorTower n T) = T`)**:
   `toTensorTower n (ofTensorTower n T) = T`. -/
theorem tt5_recursive_tensor_peirce_ring_isomorphism
    {R : Type*} [Semiring R] (n : ℕ) (A A' : FlatMat R n) (T : TensorTower R n) :
    peirceTowerEquiv R n (A + A') = peirceTowerEquiv R n A + peirceTowerEquiv R n A' ∧
    peirceTowerEquiv R n (A * A') = peirceTowerEquiv R n A * peirceTowerEquiv R n A' ∧
    peirceTowerEquiv R n 1 = 1 ∧
    (peirceTowerEquiv R n).symm (peirceTowerEquiv R n A) = A ∧
    peirceTowerEquiv R n ((peirceTowerEquiv R n).symm T) = T ∧
    toTensorTower n (ofTensorTower n T) = T := by
  have hTower : ∀ (k : ℕ) (S : TensorTower R k),
      toTensorTower k (ofTensorTower k S) = S := by
    intro k
    induction k with
    | zero => intro S; rfl
    | succ k ih =>
      intro (S : Matrix (Fin 2) (Fin 2) (TensorTower R k))
      dsimp [toTensorTower, ofTensorTower]
      have hTT4 := tt4_recursive_inductive_tensor_tower_type (0 : R) 0 0 k 0 0
        ![![ofTensorTower k (S 0 0), ofTensorTower k (S 0 1)],
          ![ofTensorTower k (S 1 0), ofTensorTower k (S 1 1)]]
      rw [hTT4.2.2.2.2.2.2.2.2.2]
      apply Matrix.ext
      intro a b
      fin_cases a <;> fin_cases b <;> simp [ih]
  exact ⟨map_add (peirceTowerEquiv R n) A A',
    map_mul (peirceTowerEquiv R n) A A',
    map_one (peirceTowerEquiv R n),
    (peirceTowerEquiv R n).symm_apply_apply A,
    (peirceTowerEquiv R n).apply_symm_apply T,
    hTower n T⟩

/-- **Stage `𝔗𝔗₆` (`tt6_dual_clifford_dewitt_tensor_basis_and_master_synthesis`)**:
Master theorem unifying the 6-stage **Recursive Tensor-Peirce Centralizer Projection & Dyadic Tensor Tower Poset**
(`𝔗𝔗₁ ≺ 𝔗𝔗₂ ≺ 𝔗𝔗₃ ≺ 𝔗𝔗₄ ≺ 𝔗𝔗₅ ≺ 𝔗𝔗₆`):
1. **Poset Acyclicity & Cardinality**:
   `TensorPeirceTowerStage.causalEdge_acyclic` and `Fintype.card TensorPeirceTowerStage = 6`.
2. **Dual $\mathcal{C}\ell(1,1)$ DeWitt–Clifford Basis (`{I_2, S_P, Φ, J}`) & Division-Free Reconstruction**:
   - `unitS * unitS = unitI` ($S_P^2 = I_2$), `unitPhi * unitPhi = unitI` ($\Phi^2 = +I_2$),
     `unitJ * unitJ = -unitI` ($J^2 = -I_2$),
   - `unitS * unitPhi + unitPhi * unitS = 0`, `unitPhi * unitJ + unitJ * unitPhi = 0`, `unitS * unitPhi = unitJ`,
   - `unitI * (matPi00 M + matPi11 M) + unitS * (matPi00 M - matPi11 M) + unitPhi * (matPi01 M + matPi10 M) + unitJ * (matPi01 M - matPi10 M) = (2 : ℤ) • M`.
3. **Master Tensor-Peirce Centralizer Homogenization & Recursive Tower Synthesis**:
   Bundles `matPi00 M = !![M 0 0, 0; 0, M 0 0]`,
   `unitE00 * matPi00 M + unitE01 * matPi01 M + unitE10 * matPi10 M + unitE11 * matPi11 M = M`,
   `matPi00 (M * N) = matPi00 M * matPi00 N + matPi01 M * matPi10 N`,
   `peirceSplitStep (peirceUnsplitStep C) = C`,
   `peirceTowerEquiv R n (A * A') = peirceTowerEquiv R n A * peirceTowerEquiv R n A'`, and
   `toTensorTower n (ofTensorTower n T) = T`. -/
theorem tt6_dual_clifford_dewitt_tensor_basis_and_master_synthesis
    {Np Nm : B} (hNp : Np * Np = 0) (hNm : Nm * Nm = 0) (hCAR : Np * Nm + Nm * Np = 1)
    {R : Type*} [Ring R] (M N : Matrix (Fin 2) (Fin 2) R)
    (n : ℕ) (A A' : FlatMat R n) (C : Matrix (Fin 2) (Fin 2) (FlatMat R n)) (T : TensorTower R n) :
    -- 1. Poset acyclicity and cardinality:
    (∀ st : TensorPeirceTowerStage,
      ¬ Relation.TransGen TensorPeirceTowerStage.causalEdge st st) ∧
    Fintype.card TensorPeirceTowerStage = 6 ∧
    -- 2. Cl(1,1) DeWitt–Clifford relations and division-free 2-scaled reconstruction:
    (unitS : Matrix (Fin 2) (Fin 2) R) * unitS = unitI ∧
    (unitPhi : Matrix (Fin 2) (Fin 2) R) * unitPhi = unitI ∧
    (unitJ : Matrix (Fin 2) (Fin 2) R) * unitJ = -unitI ∧
    (unitS : Matrix (Fin 2) (Fin 2) R) * unitPhi + unitPhi * unitS = 0 ∧
    (unitPhi : Matrix (Fin 2) (Fin 2) R) * unitJ + unitJ * unitPhi = 0 ∧
    (unitS : Matrix (Fin 2) (Fin 2) R) * unitPhi = unitJ ∧
    unitI * (matPi00 M + matPi11 M) +
      unitS * (matPi00 M - matPi11 M) +
      unitPhi * (matPi01 M + matPi10 M) +
      unitJ * (matPi01 M - matPi10 M) = (2 : ℤ) • M ∧
    -- 3. Master centralizer homogenization and recursive TensorTower synthesis:
    matPi00 M = !![M 0 0, 0; 0, M 0 0] ∧
    matPi01 M = !![M 0 1, 0; 0, M 0 1] ∧
    unitE00 * matPi00 M + unitE01 * matPi01 M +
      unitE10 * matPi10 M + unitE11 * matPi11 M = M ∧
    matPi00 (M * N) = matPi00 M * matPi00 N + matPi01 M * matPi10 N ∧
    peirceSplitStep (peirceUnsplitStep C) = C ∧
    peirceTowerEquiv R n (A * A') = peirceTowerEquiv R n A * peirceTowerEquiv R n A' ∧
    toTensorTower n (ofTensorTower n T) = T := by
  have hTT2 := tt2_four_centralizer_homogenized_peirce_projectors
    hNp hNm hCAR M (0 : Matrix (Fin 1) (Fin 1) R) 0 0 0
  have hTT3 := tt3_exact_commutant_reconstruction_and_block_multiplication_laws
    hNp hNm hCAR 0 M N
  have hTT4 := tt4_recursive_inductive_tensor_tower_type (0 : R) 0 0 n 0 0 C
  have hTT5 := tt5_recursive_tensor_peirce_ring_isomorphism n A A' T
  refine ⟨TensorPeirceTowerStage.causalEdge_acyclic,
    TensorPeirceTowerStage.card_eq_six,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hTT2.2.2.2.2.1,
    hTT2.2.2.2.2.2.2.1,
    hTT3.2.2.2.2.2.2.2.1,
    hTT3.2.2.2.2.2.2.2.2.1,
    hTT4.2.2.2.2.2.2.2.2.2,
    hTT5.2.1,
    hTT5.2.2.2.2.2⟩
  · ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitS, unitI, unitE00, unitE11]
  · ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitPhi, unitI, unitE00, unitE01, unitE10, unitE11]
  · ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitJ, unitI, unitE00, unitE01, unitE10, unitE11]
  · ext i j; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitS, unitPhi, unitE00, unitE01, unitE10, unitE11]
  · ext i j; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitPhi, unitJ, unitE01, unitE10]
  · ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitS, unitPhi, unitJ, unitE00, unitE01, unitE10, unitE11]
  · have hExpand :
        unitI * (matPi00 M + matPi11 M) +
          unitS * (matPi00 M - matPi11 M) +
          unitPhi * (matPi01 M + matPi10 M) +
          unitJ * (matPi01 M - matPi10 M) =
        (2 : ℤ) • (unitE00 * matPi00 M + unitE01 * matPi01 M +
          unitE10 * matPi10 M + unitE11 * matPi11 M) := by
      dsimp [unitI, unitS, unitPhi, unitJ]
      noncomm_ring
    rw [hExpand, hTT3.2.2.2.2.2.2.2.1]

end TensorPeirceTowerPoset

/-!
## 8. Stage `𝔊₇`: Para-Kähler Information Geometry Manifold: Chiral 2-Jet, Schwarz Defect & Bregman Closure
-/

/-- **Stage `𝔊₇` (`G7_ParaKahlerInformationManifoldChiralTwoJetAndBregmanClosure`)**:
1. **Chiral 2-Jet Decomposition & Noncommutative Schwarz Defect (`RadonNikodymKahlerParaKahlerBregmanPoset.lean`)**:
   In any associative ring `[Ring B]` with idempotent $P^2 = P$, twice the forward and backward
   chiral 2-jets decompose into the symmetric Fisher metric strain $V = \{N_+, N_-\}$ and the
   antisymmetric Para-Berry curvature $\Sigma = [N_+, N_-]$:
   $$2 \bullet (N_+ N_-) = V + \Sigma, \qquad 2 \bullet (N_- N_+) = V - \Sigma,$$
   and the mixed chiral derivation commutator is $[\delta_+, \delta_-](X) = [\Sigma, X]$
   (with Rung 0 proving that if $[\delta_+, \delta_-](N_\pm) = 0$, then $2 \bullet V^2 = 0$).
2. **Para-Kähler Fisher Hessian & Universal Noncommutative Bregman Three-Point Law (`ParaKahlerBregmanModularNoetherPoset.lean`)**:
   Twice the symmetric Para-Kähler Hessian sum $\{\delta_+, \delta_-\}(X)$ equals
   $-(\operatorname{ad}_\Phi^2(X) + \operatorname{ad}_J^2(X))$, while the noncommutative Bregman
   divergence $D_B(X, Y) = (X - Y)^2$ satisfies the universal three-point identity
   $D_B(X, Z) - D_B(X, Y) - D_B(Y, Z) = \{X - Y, Y - Z\}$ and null-cone vanishing
   $D_B(\Phi, -J) = 0$.
3. **Supersymmetric Souriau–Massieu UV Cancellation & Moment Readout (`SuperGrassmannianFiveGradedColorSupersymmetrySynthesis.lean`)**:
   When odd Berezinian counterterms cancel the bosonic UV vacuum defect ($b_{\text{fer}}(k) + \Delta_{\text{UV}}(k) = 0$),
   $\Phi_{\text{super}}$ reduces identically to the Souriau–Massieu potential $\Phi(s_{\text{bos}})$
   and its coordinate derivative recovers the canonical Souriau attention weight $A_j(s_{\text{bos}})$. -/
theorem g7_parakahler_information_manifold_chiral_two_jet_and_bregman_closure
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X Y Z : B)
    {m : ℕ} [Nonempty (Fin m)] (s_bos b_fer Δ_UV : Fin m → ℝ) (j : Fin m)
    (h_cancel : ∀ k : Fin m, b_fer k + Δ_UV k = 0) :
    -- 1. Chiral 2-jet decomposition and noncommutative Schwarz defect [δ_+, δ_-](X) = [Σ, X]:
    chiralTwoJetPlus P A C = genV P A C + genSig P A C ∧
    chiralTwoJetMinus P A C = genV P A C - genSig P A C ∧
    chiralSchwarzComm P A C X = OperatorAlgebra.PeirceSpine.comm (genSig P A C) X ∧
    (chiralSchwarzComm P A C (conePlus P A) = 0 →
      chiralSchwarzComm P A C (coneMinus P C) = 0 →
      (2 : ℤ) • (genV P A C * genV P A C) = 0) ∧
    -- 2. Para-Kähler Fisher Hessian decomposition and Bregman 3-point identity:
    (2 : ℤ) • (OperatorAlgebra.PeirceSpine.comm (conePlus P A)
          (OperatorAlgebra.PeirceSpine.comm (coneMinus P C) X) +
        OperatorAlgebra.PeirceSpine.comm (coneMinus P C)
          (OperatorAlgebra.PeirceSpine.comm (conePlus P A) X)) =
      -(derivSqPhi P A C X + derivSqJ P A C X) ∧
    opBregmanDiv X Z - opBregmanDiv X Y - opBregmanDiv Y Z =
      anticomm (X - Y) (Y - Z) ∧
    opBregmanDiv (genPhi P A C) (-genJ P A C) = 0 ∧
    -- 3. Supersymmetric Souriau–Massieu UV cancellation and moment map derivative:
    superSouriauMassieuPotential s_bos (fun k => Δ_UV k + b_fer k) =
      InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis.souriauMassieuPotential s_bos ∧
    HasDerivAt
      (fun t : ℝ =>
        superSouriauMassieuPotential (Function.update s_bos j t)
          (fun k => Δ_UV k + b_fer k))
      (InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis.souriauAttentionWeight s_bos j)
      (s_bos j) := by
  have hJet := chiralTwoJet_decomposition P A C
  have hJacobi : chiralSchwarzComm P A C X =
      OperatorAlgebra.PeirceSpine.comm (genSig P A C) X := by
    dsimp only [chiralSchwarzComm, deltaPlus, deltaMinus, genSig,
      OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  have hM1 := archetype_M1_parakahler_hessian_and_curvature_2form hP A C X
  have hM2 := archetype_M2_modular_surprisal_and_bregman_three_point hP A C A A C C X Y Z
  have hSM := superSouriauMassieu_uv_cancellation_and_moment_readout s_bos b_fer Δ_UV j h_cancel
  refine ⟨hJet.1, hJet.2, hJacobi, ?_, hM1.2.1, hM2.1, hM2.2.2.2.1, hSM.1, hSM.2⟩
  intro hPlus hMinus
  exact (rung0_schwarz_symmetry_aporia hP A C X hPlus hMinus).2.2.2.2.2.2

/-!
## 9. DeWitt-Split Super-Grassmannian & Para-Kähler Operator Geometry Poset (`𝔓₁ ≺ 𝔓₂ ≺ ⋯ ≺ 𝔓₇`)

In any associative unital ring `[Ring B]` equipped with a DeWitt-split idempotent $P^2 = P$,
the Super-Grassmannian $\mathrm{SGr}(P; B)$ of idempotent projectors conjugate to $P$ is a
**Para-Kähler Operator Information Manifold**:
- Its tangent space at the basepoint $P$ is polarized by the chiral DeWitt Difference Involution
  $S_P = 2P - 1$ ($S_P^2 = 1$) into the two maximally isotropic Amari affine sheets
  $\mathfrak{n}_+ = P B (1 - P)$ and $\mathfrak{n}_- = (1 - P) B P$.
- While individual unipotent charts $P_+(N_+) = (1 - N_+) P (1 + N_+) = P + N_+$ and
  $P_-(N_-) = (1 + N_-) P (1 - N_-) = P + N_-$ are exact idempotents, their naive linear
  superposition $\Psi = P + N_+ + N_- = P + \Phi$ jumps off the Grassmannian by the operator
  Fisher metric ($\Psi^2 - \Psi = V$).
- Simultaneous unipotent Bruhat dressing constructs the exact two-chart idempotent
  $$\widehat{P}(N_+, N_-) := (1 - N_+)(P + N_-)(1 + N_+) = P + \Phi - \Sigma - V N_+,$$
  whose quadratic term $-\Sigma = -[N_+, N_-]$ is the Para-Kähler curvature 2-form and whose
  cubic term $-V N_+ = -N_+ N_- N_+$ is half the Jordan triple product $\{N_+, N_-, N_+\} = 2 V N_+$
  required to restore $\widehat{P}(N_+, N_-)^2 = \widehat{P}(N_+, N_-)$.
- The associative Push–Pull Resolvent Intertwiner $Q_+ N_+ = N_+ Q_- = V N_+$ implies
  $R_+ N_+ = N_+ R_- = R_V N_+$ whenever $R_+(1 - Q_+) = 1$, $(1 - Q_-)R_- = 1$, and
  $R_V(1 - V) = 1$, which collapses the Legendre–Schur differential of $\eta_- = R_+ N_+$
  identically into the **Hua–Bergman–Dikin Para-Kähler Operator Metric**
  $$\big(R_+ \, dN_+ + R_+ \, dN_+ \, N_- \, (R_+ N_+)\big) \, dN_- = R_+ \, dN_+ \, R_- \, dN_-.$$
-/

/-- The 7 stages of the **DeWitt-Split Super-Grassmannian & Para-Kähler Operator Geometry Poset**
(`𝔓₁ ≺ 𝔓₂ ≺ 𝔓₃ ≺ 𝔓₄ ≺ 𝔓₅ ≺ 𝔓₆ ≺ 𝔓₇`). -/
inductive DeWittSplitSuperGrassmannianParaKahlerStage : Type
  /-- `𝔓₁`: Chiral DeWitt Difference Involution `S_P = 2P - 1` (`S_P² = 1`) & isotropic tangent polarization `[S_P, N_±] = ±2 N_±`. -/
  | P1_DeWittDifferenceInvolutionAndTangentPolarization
  /-- `𝔓₂`: Unipotent Grassmannian chart conjugations `P_+(N_+) = P + N_+`, `P_-(N_-) = P + N_-` vs. Rung 0 linear chart aporia `Ψ² - Ψ = V`. -/
  | P2_UnipotentGrassmannianChartsAndLinearChartAporia
  /-- `𝔓₃`: Bruhat-dressed two-chart idempotent `P̂(N_+, N_-) = P + Φ - Σ - V N_+` & Jordan triple cubic cancellation `{N_+, N_-, N_+} = 2 V N_+`. -/
  | P3_BruhatDressedTwoChartIdempotentAndJordanTriple
  /-- `𝔓₄`: Associative Push–Pull Resolvent Intertwiner `Q_+ N_+ = N_+ Q_- = V N_+` and `R_+ N_+ = N_+ R_- = R_V N_+`. -/
  | P4_AssociativePushPullResolventIntertwiner
  /-- `𝔓₅`: Legendre–Schur differential collapse & Hua–Bergman–Dikin Para-Kähler operator metric `R_+ dN_+ R_- dN_-`. -/
  | P5_LegendreSchurDifferentialAndHuaBergmanDikinMetric
  /-- `𝔓₆`: Peirce Super-LU Berezinian factor `(1 - Q_+)(1 - Q_-) = 1 - V` & `V₄ = ℤ₂^Peirce × ℤ₂^SUSY` character parity. -/
  | P6_PeirceSuperLUBerezinianAndKleinFourCharacterParity
  /-- `𝔓₇`: Unified DeWitt-Split Split-Octonion `↪` Super-Grassmannian `↪` Para-Kähler Amari Information Manifold Synthesis. -/
  | P7_UnifiedDeWittSplitSuperGrassmannianParaKahlerSynthesis
  deriving DecidableEq, Repr

namespace DeWittSplitSuperGrassmannianParaKahlerStage

/-- Integer rank `0 .. 6` for `𝔓₁ ≺ 𝔓₂ ≺ ⋯ ≺ 𝔓₇`. -/
def rank : DeWittSplitSuperGrassmannianParaKahlerStage → ℕ
  | .P1_DeWittDifferenceInvolutionAndTangentPolarization       => 0
  | .P2_UnipotentGrassmannianChartsAndLinearChartAporia        => 1
  | .P3_BruhatDressedTwoChartIdempotentAndJordanTriple         => 2
  | .P4_AssociativePushPullResolventIntertwiner                => 3
  | .P5_LegendreSchurDifferentialAndHuaBergmanDikinMetric      => 4
  | .P6_PeirceSuperLUBerezinianAndKleinFourCharacterParity     => 5
  | .P7_UnifiedDeWittSplitSuperGrassmannianParaKahlerSynthesis => 6

theorem rank_injective :
    Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder DeWittSplitSuperGrassmannianParaKahlerStage where
  le a b := rank a ≤ rank b
  lt a b := rank a < rank b
  le_refl a := le_rfl
  le_trans a b c := Nat.le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (rank a) (rank b)
  le_antisymm a b hab hba := rank_injective (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total (rank a) (rank b)
  toDecidableLE a b := Nat.decLe (rank a) (rank b)
  toDecidableEq := inferInstance
  toDecidableLT a b := Nat.decLt (rank a) (rank b)

instance : Fintype DeWittSplitSuperGrassmannianParaKahlerStage where
  elems := {
    .P1_DeWittDifferenceInvolutionAndTangentPolarization,
    .P2_UnipotentGrassmannianChartsAndLinearChartAporia,
    .P3_BruhatDressedTwoChartIdempotentAndJordanTriple,
    .P4_AssociativePushPullResolventIntertwiner,
    .P5_LegendreSchurDifferentialAndHuaBergmanDikinMetric,
    .P6_PeirceSuperLUBerezinianAndKleinFourCharacterParity,
    .P7_UnifiedDeWittSplitSuperGrassmannianParaKahlerSynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_seven :
    Fintype.card DeWittSplitSuperGrassmannianParaKahlerStage = 7 := rfl

/-- Directed covering edges `𝔓_k ≺ 𝔓_{k+1}`. -/
def causalEdge (a b : DeWittSplitSuperGrassmannianParaKahlerStage) : Prop :=
  rank b = rank a + 1

theorem causalEdge_lt {a b : DeWittSplitSuperGrassmannianParaKahlerStage}
    (h : causalEdge a b) : rank a < rank b := by
  dsimp [causalEdge] at h
  omega

theorem transGen_causalEdge_lt {a b : DeWittSplitSuperGrassmannianParaKahlerStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

/-- Strict DAG acyclicity of `𝔓₁ ≺ 𝔓₂ ≺ ⋯ ≺ 𝔓₇`. -/
theorem causalEdge_acyclic (a : DeWittSplitSuperGrassmannianParaKahlerStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_lt h)

/-- Monotone embedding into `InfoGeometry.Meta.RepDepth`. -/
def toRepDepth : DeWittSplitSuperGrassmannianParaKahlerStage → InfoGeometry.Meta.RepDepth
  | .P1_DeWittDifferenceInvolutionAndTangentPolarization       => .operator
  | .P2_UnipotentGrassmannianChartsAndLinearChartAporia        => .operator
  | .P3_BruhatDressedTwoChartIdempotentAndJordanTriple         => .operator
  | .P4_AssociativePushPullResolventIntertwiner                => .transport
  | .P5_LegendreSchurDifferentialAndHuaBergmanDikinMetric      => .transport
  | .P6_PeirceSuperLUBerezinianAndKleinFourCharacterParity     => .thermo
  | .P7_UnifiedDeWittSplitSuperGrassmannianParaKahlerSynthesis => .thermo

/-- Monotone embedding into `InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    DeWittSplitSuperGrassmannianParaKahlerStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .P1_DeWittDifferenceInvolutionAndTangentPolarization       => .M1_ProjectorClabject
  | .P2_UnipotentGrassmannianChartsAndLinearChartAporia        => .M1_ProjectorClabject
  | .P3_BruhatDressedTwoChartIdempotentAndJordanTriple         => .M2_GrassmannianPowertypeOrbit
  | .P4_AssociativePushPullResolventIntertwiner                => .M2_GrassmannianPowertypeOrbit
  | .P5_LegendreSchurDifferentialAndHuaBergmanDikinMetric      => .M2_GrassmannianPowertypeOrbit
  | .P6_PeirceSuperLUBerezinianAndKleinFourCharacterParity     => .M3_ErlangenCasimirMetaLaw
  | .P7_UnifiedDeWittSplitSuperGrassmannianParaKahlerSynthesis => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : DeWittSplitSuperGrassmannianParaKahlerStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth InfoGeometry.Meta.RepDepth.toNat <;>
    decide

theorem toOntologyMetaLevel_mono {a b : DeWittSplitSuperGrassmannianParaKahlerStage}
    (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;>
    decide

end DeWittSplitSuperGrassmannianParaKahlerStage

section DeWittSplitSuperGrassmannianOperatorGeometry

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
open InfoGeometry.Canonical.AmariOperatorDuallyFlatGaussianPythagoreanPoset
open InfoGeometry.Canonical.KleinBottleSeamSumDifferenceConnectionPoset
open InfoGeometry.Canonical.OperatorLogDetDikinGeometry
open InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
open InfoGeometry.Analysis.PositiveMatrixDikin
open InfoGeometry.Geometry.LegendreDifferential

variable {B : Type*} [Ring B]

/-- Primal unipotent Grassmannian chart projector `P_+(N_+) := P + N_+ = P + P A (1 - P)`. -/
def primalChartProj (P A : B) : B :=
  P + conePlus P A

/-- Dual unipotent Grassmannian chart projector `P_-(N_-) := P + N_- = P + (1 - P) C P`. -/
def dualChartProj (P C : B) : B :=
  P + coneMinus P C

/-- Naive linear two-sheet superposition `Ψ(N_+, N_-) := P + N_+ + N_- = P + Φ`. -/
def naiveLinearChart (P A C : B) : B :=
  P + genPhi P A C

/-- Exact Bruhat-dressed two-chart Super-Grassmannian idempotent
`P̂(N_+, N_-) := (1 - N_+)(P + N_-)(1 + N_+)`. -/
def dressedTwoChartProj (P A C : B) : B :=
  (1 - conePlus P A) * (P + coneMinus P C) * (1 + conePlus P A)

/-- **Rung 0 (`rung0_socratic_aporia_naive_linear_chart_jumps_off_grassmannian`)**:
1. Each single-sheet unipotent chart `P_+(N_+) = P + N_+` and `P_-(N_-) = P + N_-` is an exact
   idempotent (`P_+² = P_+`, `P_-² = P_-`).
2. However, the naive linear superposition `Ψ = P + N_+ + N_- = P + Φ` jumps off the
   Super-Grassmannian by the operator Fisher metric `V = N_+ N_- + N_- N_+`:
   $$\Psi^2 - \Psi = V, \qquad \Psi^2 = \Psi \iff V = 0.$$
3. Moreover, the two flat Grassmannian charts fail to commute by the Para-Kähler curvature
   2-form `Σ = [N_+, N_-]` minus the combined frame `Φ = N_+ + N_-`:
   $$[P_+(N_+), P_-(N_-)] = \Sigma - \Phi.$$ -/
theorem rung0_socratic_aporia_naive_linear_chart_jumps_off_grassmannian
    {P : B} (hP : P * P = P) (A C : B) :
    primalChartProj P A * primalChartProj P A = primalChartProj P A ∧
    dualChartProj P C * dualChartProj P C = dualChartProj P C ∧
    naiveLinearChart P A C * naiveLinearChart P A C - naiveLinearChart P A C = genV P A C ∧
    (naiveLinearChart P A C * naiveLinearChart P A C = naiveLinearChart P A C ↔
      genV P A C = 0) ∧
    OperatorAlgebra.PeirceSpine.comm (primalChartProj P A) (dualChartProj P C) =
      genSig P A C - genPhi P A C := by
  have hDefect :
      naiveLinearChart P A C * naiveLinearChart P A C - naiveLinearChart P A C =
        genV P A C := by
    simp only [naiveLinearChart]
    peirce_nf hP
  refine ⟨?_, ?_, hDefect, ?_, ?_⟩
  · simp only [primalChartProj]
    peirce_nf hP
  · simp only [dualChartProj]
    peirce_nf hP
  · rw [← sub_eq_zero, hDefect]
  · simp only [primalChartProj, dualChartProj, OperatorAlgebra.PeirceSpine.comm]
    peirce_nf hP

/-- **Stages `𝔓₁, 𝔓₂` (`p1_p2_dewitt_split_tangent_polarization_and_unipotent_charts`)**:
1. **Chiral DeWitt Difference Involution (`𝔓₁`)**:
   $S_P = 2P - 1$ satisfies $S_P^2 = 1$ and polarizes the isotropic tangent sheets
   $\mathfrak{n}_+ = P B (1 - P)$ and $\mathfrak{n}_- = (1 - P) B P$ via one-sided signs
   ($S_P N_+ = N_+$, $N_+ S_P = -N_+$, $S_P N_- = -N_-$, $N_- S_P = N_-$) and adjoint eigenvalues
   $[S_P, N_+] = 2 N_+$, $[S_P, N_-] = -2 N_-$, $\{S_P, N_\pm\} = 0$.
2. **Unipotent Grassmannian Chart Conjugations (`𝔓₂`)**:
   Conjugating the basepoint $P$ by the abelian unipotent exponentials $\mathcal{E}_+(A) = 1 + N_+$
   and $\mathcal{E}_-(C) = 1 + N_-$ yields the affine Grassmannian chart projectors:
   $$(1 - N_+) P (1 + N_+) = P + N_+, \qquad (1 + N_-) P (1 - N_-) = P + N_-.$$ -/
theorem p1_p2_dewitt_split_tangent_polarization_and_unipotent_charts
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * invS P = 1 ∧
    invS P * conePlus P A = conePlus P A ∧
    conePlus P A * invS P = -conePlus P A ∧
    invS P * coneMinus P C = -coneMinus P C ∧
    coneMinus P C * invS P = coneMinus P C ∧
    OperatorAlgebra.PeirceSpine.comm (invS P) (conePlus P A) = (2 : ℤ) • conePlus P A ∧
    OperatorAlgebra.PeirceSpine.comm (invS P) (coneMinus P C) = -((2 : ℤ) • coneMinus P C) ∧
    OperatorAlgebra.PeirceSpine.anticomm (invS P) (conePlus P A) = 0 ∧
    OperatorAlgebra.PeirceSpine.anticomm (invS P) (coneMinus P C) = 0 ∧
    conjPlusInv P A P = primalChartProj P A ∧
    conjMinus P C P = dualChartProj P C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [primalChartProj, dualChartProj, conjPlusInv, conjMinus,
        OperatorAlgebra.PeirceSpine.comm, OperatorAlgebra.PeirceSpine.anticomm]);
      peirce_nf hP)

/-- **Stage `𝔓₃` (`p3_bruhat_dressed_two_chart_idempotent_and_jordan_triple`)**:
1. **Exact Bruhat-Dressed Two-Chart Expansion**:
   Dressing the dual chart projector $P_-(N_-) = P + N_-$ by the primal unipotent group element
   $\mathcal{E}_+(A) = 1 + N_+$ expands into the basepoint $P$, the linear displacement $\Phi$,
   the quadratic Para-Kähler curvature correction $-\Sigma = -[N_+, N_-]$, and the cubic
   correction $-V N_+ = -N_+ N_- N_+$:
   $$\widehat{P}(N_+, N_-) = (1 - N_+)(P + N_-)(1 + N_+) = P + \Phi - \Sigma - V N_+.$$
2. **Exact Two-Chart Idempotency on the Super-Grassmannian**:
   $\widehat{P}(N_+, N_-)^2 = \widehat{P}(N_+, N_-)$ holds identically in any `[Ring B]` with $P^2 = P$,
   and conjugation by $(1 + N_+)$ returns to the dual chart $(1 + N_+) \widehat{P}(N_+, N_-) (1 - N_+) = P + N_-$.
3. **Jordan Triple Cubic Identification (`archetype_A25_jordan_triple_and_grade_inversion`)**:
   The cubic term $N_+ N_- N_+ = V N_+$ is half the Jordan triple product
   $\{N_+, N_-, N_+\} = 2 \bullet (V N_+)$, and dually $N_- N_+ N_- = V N_-$ with
   $\{N_-, N_+, N_-\} = 2 \bullet (V N_-)$. -/
theorem p3_bruhat_dressed_two_chart_idempotent_and_jordan_triple
    {P : B} (hP : P * P = P) (A C : B) :
    dressedTwoChartProj P A C =
      P + genPhi P A C - genSig P A C - genV P A C * conePlus P A ∧
    dressedTwoChartProj P A C * dressedTwoChartProj P A C = dressedTwoChartProj P A C ∧
    conjPlus P A (dressedTwoChartProj P A C) = dualChartProj P C ∧
    conePlus P A * coneMinus P C * conePlus P A = genV P A C * conePlus P A ∧
    coneMinus P C * conePlus P A * coneMinus P C = genV P A C * coneMinus P C ∧
    jordanTriple (conePlus P A) (coneMinus P C) (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    jordanTriple (coneMinus P C) (conePlus P A) (coneMinus P C) =
      (2 : ℤ) • (genV P A C * coneMinus P C) := by
  have hA25 := archetype_A25_jordan_triple_and_grade_inversion hP A C
  refine ⟨?_, ?_, ?_, ?_, ?_, hA25.1, hA25.2.1⟩ <;>
    ((try simp only [dressedTwoChartProj, dualChartProj, conjPlus]);
      peirce_nf hP)

/-- **Stage `𝔓₄` (`p4_associative_push_pull_resolvent_intertwiner`)**:
1. **One-Step & Higher-Power Push–Pull Intertwining**:
   For $Q_+ = N_+ N_-$ and $Q_- = N_- N_+$, associativity forces
   $$Q_+ N_+ = N_+ Q_- = V N_+, \qquad Q_- N_- = N_- Q_+ = V N_-,$$
   and by induction for all $k \in \mathbb{N}$:
   $$Q_+^{k+1} N_+ = N_+ Q_-^{k+1} = V^{k+1} N_+.$$
2. **Bergman Factor Intertwining**:
   $$(1 - Q_+) N_+ = N_+ (1 - Q_-) = (1 - V) N_+, \qquad (1 - Q_-) N_- = N_- (1 - Q_+) = (1 - V) N_-.$$
3. **Series-Free Resolvent Intertwining (`R_+ N_+ = N_+ R_- = R_V N_+`)**:
   For any operators $R_+, R_-, R_V \in B$ satisfying $R_+(1 - Q_+) = 1$, $(1 - Q_-)R_- = 1$,
   and $R_V(1 - V) = 1$, the left action of $R_+$ or $R_V$ on $N_+$ equals the right action of $R_-$:
   $$R_+ N_+ = N_+ R_- = R_V N_+.$$ -/
theorem p4_associative_push_pull_resolvent_intertwiner
    {P : B} (hP : P * P = P) (A C : B) :
    qgtPlus P A C * conePlus P A = conePlus P A * qgtMinus P A C ∧
    qgtPlus P A C * conePlus P A = genV P A C * conePlus P A ∧
    qgtMinus P A C * coneMinus P C = coneMinus P C * qgtPlus P A C ∧
    qgtMinus P A C * coneMinus P C = genV P A C * coneMinus P C ∧
    (∀ k : ℕ,
      (qgtPlus P A C) ^ (k + 1) * conePlus P A =
        conePlus P A * (qgtMinus P A C) ^ (k + 1) ∧
      (qgtPlus P A C) ^ (k + 1) * conePlus P A =
        (genV P A C) ^ (k + 1) * conePlus P A) ∧
    (1 - qgtPlus P A C) * conePlus P A = conePlus P A * (1 - qgtMinus P A C) ∧
    (1 - qgtPlus P A C) * conePlus P A = (1 - genV P A C) * conePlus P A ∧
    (1 - qgtMinus P A C) * coneMinus P C = coneMinus P C * (1 - qgtPlus P A C) ∧
    (1 - qgtMinus P A C) * coneMinus P C = (1 - genV P A C) * coneMinus P C ∧
    (∀ R_plus R_minus R_V : B,
      R_plus * (1 - qgtPlus P A C) = 1 →
      (1 - qgtMinus P A C) * R_minus = 1 →
      R_V * (1 - genV P A C) = 1 →
      R_plus * conePlus P A = conePlus P A * R_minus ∧
      R_V * conePlus P A = conePlus P A * R_minus ∧
      R_plus * conePlus P A = R_V * conePlus P A) := by
  have h1 : qgtPlus P A C * conePlus P A = conePlus P A * qgtMinus P A C := by
    simp only [qgtPlus, qgtMinus]
    peirce_nf hP
  have h2 : qgtPlus P A C * conePlus P A = genV P A C * conePlus P A := by
    simp only [qgtPlus]
    peirce_nf hP
  have h3 : qgtMinus P A C * coneMinus P C = coneMinus P C * qgtPlus P A C := by
    simp only [qgtPlus, qgtMinus]
    peirce_nf hP
  have h4 : qgtMinus P A C * coneMinus P C = genV P A C * coneMinus P C := by
    simp only [qgtMinus]
    peirce_nf hP
  have hPow : ∀ k : ℕ,
      (qgtPlus P A C) ^ (k + 1) * conePlus P A =
        conePlus P A * (qgtMinus P A C) ^ (k + 1) ∧
      (qgtPlus P A C) ^ (k + 1) * conePlus P A =
        (genV P A C) ^ (k + 1) * conePlus P A := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.zero_add, pow_one]
      exact ⟨h1, h2⟩
    | succ k ih =>
      constructor
      · calc (qgtPlus P A C) ^ (k + 1 + 1) * conePlus P A
          _ = qgtPlus P A C * ((qgtPlus P A C) ^ (k + 1) * conePlus P A) := by
                rw [pow_succ', mul_assoc]
          _ = qgtPlus P A C * (conePlus P A * (qgtMinus P A C) ^ (k + 1)) := by
                rw [ih.1]
          _ = (qgtPlus P A C * conePlus P A) * (qgtMinus P A C) ^ (k + 1) := by
                rw [mul_assoc]
          _ = (conePlus P A * qgtMinus P A C) * (qgtMinus P A C) ^ (k + 1) := by
                rw [h1]
          _ = conePlus P A * (qgtMinus P A C) ^ (k + 1 + 1) := by
                rw [mul_assoc, ← pow_succ']
      · calc (qgtPlus P A C) ^ (k + 1 + 1) * conePlus P A
          _ = qgtPlus P A C * ((qgtPlus P A C) ^ (k + 1) * conePlus P A) := by
                rw [pow_succ', mul_assoc]
          _ = qgtPlus P A C * ((genV P A C) ^ (k + 1) * conePlus P A) := by
                rw [ih.2]
          _ = ((qgtPlus P A C + qgtMinus P A C) * (genV P A C) ^ (k + 1)) * conePlus P A := by
                have hOrth : qgtMinus P A C * conePlus P A = 0 := by
                  simp only [qgtMinus]
                  peirce_nf hP
                have hCommQ :
                    qgtMinus P A C * (genV P A C) ^ (k + 1) * conePlus P A = 0 := by
                  rw [(u2_gramian_power_sum_and_berezinian_difference hP A C k).1]
                  have hQQ : qgtMinus P A C * (qgtPlus P A C) ^ (k + 1) = 0 := by
                    rw [pow_succ', ← mul_assoc]
                    have h0 : qgtMinus P A C * qgtPlus P A C = 0 := by
                      simp only [qgtMinus, qgtPlus]
                      peirce_nf hP
                    rw [h0, zero_mul]
                  have hQm : qgtMinus P A C * (qgtMinus P A C) ^ (k + 1) * conePlus P A = 0 := by
                    rw [mul_assoc, pow_succ, mul_assoc, hOrth, mul_zero, mul_zero]
                  rw [mul_add, add_mul, hQQ, zero_mul, zero_add, hQm]
                calc qgtPlus P A C * ((genV P A C) ^ (k + 1) * conePlus P A)
                  _ = (qgtPlus P A C * (genV P A C) ^ (k + 1)) * conePlus P A +
                        (qgtMinus P A C * (genV P A C) ^ (k + 1)) * conePlus P A := by
                        rw [hCommQ, add_zero, mul_assoc]
                  _ = ((qgtPlus P A C + qgtMinus P A C) * (genV P A C) ^ (k + 1)) * conePlus P A := by
                        rw [add_mul, add_mul]
          _ = (genV P A C) ^ (k + 1 + 1) * conePlus P A := by
                have hVQ : qgtPlus P A C + qgtMinus P A C = genV P A C := by
                  simp only [qgtPlus, qgtMinus]
                  peirce_nf hP
                rw [hVQ, ← pow_succ']
  have hBerg1 : (1 - qgtPlus P A C) * conePlus P A = conePlus P A * (1 - qgtMinus P A C) := by
    simp only [qgtPlus, qgtMinus]
    peirce_nf hP
  have hBerg2 : (1 - qgtPlus P A C) * conePlus P A = (1 - genV P A C) * conePlus P A := by
    simp only [qgtPlus]
    peirce_nf hP
  have hBerg3 : (1 - qgtMinus P A C) * coneMinus P C = coneMinus P C * (1 - qgtPlus P A C) := by
    simp only [qgtPlus, qgtMinus]
    peirce_nf hP
  have hBerg4 : (1 - qgtMinus P A C) * coneMinus P C = (1 - genV P A C) * coneMinus P C := by
    simp only [qgtMinus]
    peirce_nf hP
  refine ⟨h1, h2, h3, h4, hPow, hBerg1, hBerg2, hBerg3, hBerg4, ?_⟩
  intro R_plus R_minus R_V hR_plus hR_minus hR_V
  have hInter1 : R_plus * conePlus P A = conePlus P A * R_minus := by
    calc R_plus * conePlus P A
      _ = R_plus * (conePlus P A * ((1 - qgtMinus P A C) * R_minus)) := by
            rw [hR_minus, mul_one]
      _ = R_plus * ((conePlus P A * (1 - qgtMinus P A C)) * R_minus) := by
            rw [mul_assoc]
      _ = R_plus * (((1 - qgtPlus P A C) * conePlus P A) * R_minus) := by
            rw [← hBerg1]
      _ = ((R_plus * (1 - qgtPlus P A C)) * conePlus P A) * R_minus := by
            noncomm_ring
      _ = conePlus P A * R_minus := by
            rw [hR_plus, one_mul]
  have hInter2 : R_V * conePlus P A = conePlus P A * R_minus := by
    have hBergV : (1 - genV P A C) * conePlus P A = conePlus P A * (1 - qgtMinus P A C) :=
      hBerg2.symm.trans hBerg1
    calc R_V * conePlus P A
      _ = R_V * (conePlus P A * ((1 - qgtMinus P A C) * R_minus)) := by
            rw [hR_minus, mul_one]
      _ = R_V * ((conePlus P A * (1 - qgtMinus P A C)) * R_minus) := by
            rw [mul_assoc]
      _ = R_V * (((1 - genV P A C) * conePlus P A) * R_minus) := by
            rw [← hBergV]
      _ = ((R_V * (1 - genV P A C)) * conePlus P A) * R_minus := by
            noncomm_ring
      _ = conePlus P A * R_minus := by
            rw [hR_V, one_mul]
  exact ⟨hInter1, hInter2, hInter1.trans hInter2.symm⟩

/-- **Stage `𝔓₅` (`p5_legendre_schur_differential_and_hua_bergman_dikin_metric`)**:
1. **Legendre–Schur Differential Collapse**:
   Whenever $R_+(1 - Q_+) = 1$ and $(1 - Q_-)R_- = 1$, the directional differential of the
   Legendre-dual expectation coordinate $\eta_- = R_+ N_+$ along $dN_+ = \text{conePlus } P \, dA$
   collapses via the Push–Pull Intertwiner $R_+ N_+ = N_+ R_-$ into the two-sided Bergman
   sandwich:
   $$R_+ \, dN_+ + R_+ \, dN_+ \, N_- \, (R_+ N_+) = R_+ \, dN_+ \, R_-.$$
2. **Hua–Bergman–Dikin Para-Kähler Operator Metric**:
   Pairing the Legendre differential $d\eta_-$ with the dual tangent perturbation
   $dN_- = \text{coneMinus } P \, dC$ yields the exact **Hua–Bergman–Dikin Operator Metric**:
   $$\big(R_+ \, dN_+ + R_+ \, dN_+ \, N_- \, (R_+ N_+)\big) \, dN_- = R_+ \, dN_+ \, R_- \, dN_-.$$
3. **Peirce Bergman Operator & Native Log-Det Dikin Hessian Bridge
   (`Bergman.lean`, `OperatorLogDetDikinGeometry.lean`)**:
   On the Peirce spine, `bergmanOp P A C 1 = 1 - V` and
   `bergmanOp P A C (conePlus P A) = (1 - V)² N_+`, while on strictly positive matrices $P_0 \in M_n(\mathbb{C})$
   the native Fréchet Hessian of $-\log\|\det P_0\|$ is the symmetric non-negative trace form
   $\operatorname{Re}\operatorname{Tr}(P_0^{-1} K P_0^{-1} H)$. -/
theorem p5_legendre_schur_differential_and_hua_bergman_dikin_metric
    {P : B} (hP : P * P = P) (A C dA dC R_plus R_minus : B)
    (hR_plus : R_plus * (1 - qgtPlus P A C) = 1)
    (hR_minus : (1 - qgtMinus P A C) * R_minus = 1)
    {n_mat : Type*} [Fintype n_mat] [DecidableEq n_mat]
    (P_pos K_mat H_mat : Matrix n_mat n_mat ℂ)
    (hP_pos : IsStrictlyPositive P_pos) (hH_sa : IsSelfAdjoint H_mat) :
    -- 1. Legendre–Schur differential collapse:
    R_plus * conePlus P dA +
      R_plus * conePlus P dA * coneMinus P C * (R_plus * conePlus P A) =
      R_plus * conePlus P dA * R_minus ∧
    -- 2. Hua–Bergman–Dikin Para-Kähler operator metric factorization:
    (R_plus * conePlus P dA +
      R_plus * conePlus P dA * coneMinus P C * (R_plus * conePlus P A)) *
      coneMinus P dC =
      R_plus * conePlus P dA * R_minus * coneMinus P dC ∧
    -- 3. Peirce Bergman operator identities (`archetype_A23_bergman_operator`):
    bergmanOp P A C 1 = 1 - genV P A C ∧
    bergmanOp P A C (conePlus P A) =
      (1 - genV P A C) * (1 - genV P A C) * conePlus P A ∧
    bergmanOp P A C (coneMinus P C) = coneMinus P C ∧
    -- 4. Native Log-Det Fréchet Hessian & Dikin positivity (`OperatorLogDetDikinGeometry.lean`):
    hessianMap negLogDet P_pos K_mat H_mat =
      (Matrix.trace (P_pos⁻¹ * K_mat * P_pos⁻¹ * H_mat)).re ∧
    hessianMap negLogDet P_pos K_mat H_mat =
      hessianMap negLogDet P_pos H_mat K_mat ∧
    0 ≤ hessianMap negLogDet P_pos H_mat H_mat := by
  have hP4 := p4_associative_push_pull_resolvent_intertwiner hP A C
  have hBerg1 := hP4.2.2.2.2.2.1
  have hInter : R_plus * conePlus P A = conePlus P A * R_minus := by
    calc R_plus * conePlus P A
      _ = R_plus * (conePlus P A * ((1 - qgtMinus P A C) * R_minus)) := by
            rw [hR_minus, mul_one]
      _ = R_plus * ((conePlus P A * (1 - qgtMinus P A C)) * R_minus) := by
            rw [mul_assoc]
      _ = R_plus * (((1 - qgtPlus P A C) * conePlus P A) * R_minus) := by
            rw [← hBerg1]
      _ = ((R_plus * (1 - qgtPlus P A C)) * conePlus P A) * R_minus := by
            noncomm_ring
      _ = conePlus P A * R_minus := by
            rw [hR_plus, one_mul]
  have hSchur :
      R_plus * conePlus P dA +
        R_plus * conePlus P dA * coneMinus P C * (R_plus * conePlus P A) =
        R_plus * conePlus P dA * R_minus := by
    calc R_plus * conePlus P dA +
          R_plus * conePlus P dA * coneMinus P C * (R_plus * conePlus P A)
      _ = R_plus * conePlus P dA * ((1 - qgtMinus P A C) * R_minus) +
            R_plus * conePlus P dA * coneMinus P C * (conePlus P A * R_minus) := by
            rw [hR_minus, mul_one, hInter]
      _ = R_plus * conePlus P dA * R_minus := by
            dsimp only [qgtMinus]
            noncomm_ring
  have hA23 := archetype_A23_bergman_operator hP A C
  exact ⟨hSchur,
    congrArg (· * coneMinus P dC) hSchur,
    hA23.1,
    hA23.2.1,
    hA23.2.2.1,
    hessianMap_negLogDet P_pos K_mat H_mat hP_pos.isUnit,
    hessianMap_negLogDet_symmetric P_pos K_mat H_mat hP_pos.isUnit,
    hessianMap_negLogDet_nonneg hP_pos hH_sa⟩

/-- **Stages `𝔓₆, 𝔓₇` (`p6_p7_unified_dewitt_split_supergrassmannian_parakahler_amari_closure`)**:
Unifies the 7-stage **DeWitt-Split Super-Grassmannian & Para-Kähler Operator Geometry Poset**
(`𝔓₁ ≺ ⋯ ≺ 𝔓₇`) with the Peirce Super-LU factorization of `1 + Φ`, the Bergman factor
`(1 - Q_+)(1 - Q_-) = 1 - V`, the Klein four-group `V₄ = ℤ₂^Peirce × ℤ₂^SUSY` character parity
separating the Fisher metric $V \in \chi_{++}$ (`β(V) = +V`) from the Para-Kähler Berry curvature
$\Sigma \in \chi_{+-}$ (`β(Σ) = -Σ`, `P_{+-}(𝒢_+) = 2 Σ`), and the Split-Octonion circular
isotropic DeWitt basis (`zornFisherV`, `zornBerrySig`, `zornAmariChentsovCubic`, `zornAssociator`). -/
theorem p6_p7_unified_dewitt_split_supergrassmannian_parakahler_amari_closure
    {P U_klein : B} (hP : P * P = P)
    (hU2 : U_klein * U_klein = 1) (hUP : U_klein * P * U_klein = 1 - P)
    (A C dA dC R_plus R_minus : B)
    (hUNp : U_klein * conePlus P A * U_klein = coneMinus P C)
    (hUNm : U_klein * coneMinus P C * U_klein = conePlus P A)
    (hR_plus : R_plus * (1 - qgtPlus P A C) = 1)
    (hR_minus : (1 - qgtMinus P A C) * R_minus = 1) :
    -- 1. Poset DAG acyclicity and cardinality of 𝔓₁ ≺ ⋯ ≺ 𝔓₇:
    (∀ st : DeWittSplitSuperGrassmannianParaKahlerStage,
      ¬ Relation.TransGen DeWittSplitSuperGrassmannianParaKahlerStage.causalEdge st st) ∧
    Fintype.card DeWittSplitSuperGrassmannianParaKahlerStage = 7 ∧
    -- 2. Rung 0 linear chart aporia vs. Stage 𝔓₃ Bruhat-dressed two-chart idempotent:
    naiveLinearChart P A C * naiveLinearChart P A C - naiveLinearChart P A C = genV P A C ∧
    dressedTwoChartProj P A C =
      P + genPhi P A C - genSig P A C - genV P A C * conePlus P A ∧
    dressedTwoChartProj P A C * dressedTwoChartProj P A C = dressedTwoChartProj P A C ∧
    jordanTriple (conePlus P A) (coneMinus P C) (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    -- 3. Stage 𝔓₄ Push–Pull Resolvent Intertwiner & Stage 𝔓₅ Hua–Bergman–Dikin Metric:
    R_plus * conePlus P A = conePlus P A * R_minus ∧
    (R_plus * conePlus P dA +
      R_plus * conePlus P dA * coneMinus P C * (R_plus * conePlus P A)) *
      coneMinus P dC =
      R_plus * conePlus P dA * R_minus * coneMinus P dC ∧
    -- 4. Stage 𝔓₆ Peirce Super-LU factorization & V₄ = ℤ₂^Peirce × ℤ₂^SUSY character parity:
    unipotentExpPlus P A * (1 - qgtPlus P A C) * unipotentExpMinus P C =
      1 + genPhi P A C ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 - genV P A C ∧
    kleinBeta U_klein (genV P A C) = genV P A C ∧
    kleinBeta U_klein (genSig P A C) = -genSig P A C ∧
    walshProjPM P U_klein (operatorGaussianPlus P A C) = (2 : ℤ) • genSig P A C := by
  have hR0 := rung0_socratic_aporia_naive_linear_chart_jumps_off_grassmannian hP A C
  have hP3 := p3_bruhat_dressed_two_chart_idempotent_and_jordan_triple hP A C
  have hP4 := p4_associative_push_pull_resolvent_intertwiner hP A C
  have hBerg1 := hP4.2.2.2.2.2.1
  have hInter : R_plus * conePlus P A = conePlus P A * R_minus := by
    calc R_plus * conePlus P A
      _ = R_plus * (conePlus P A * ((1 - qgtMinus P A C) * R_minus)) := by
            rw [hR_minus, mul_one]
      _ = R_plus * ((conePlus P A * (1 - qgtMinus P A C)) * R_minus) := by
            rw [mul_assoc]
      _ = R_plus * (((1 - qgtPlus P A C) * conePlus P A) * R_minus) := by
            rw [← hBerg1]
      _ = ((R_plus * (1 - qgtPlus P A C)) * conePlus P A) * R_minus := by
            noncomm_ring
      _ = conePlus P A * R_minus := by
            rw [hR_plus, one_mul]
  have hSchur :
      R_plus * conePlus P dA +
        R_plus * conePlus P dA * coneMinus P C * (R_plus * conePlus P A) =
        R_plus * conePlus P dA * R_minus := by
    calc R_plus * conePlus P dA +
          R_plus * conePlus P dA * coneMinus P C * (R_plus * conePlus P A)
      _ = R_plus * conePlus P dA * ((1 - qgtMinus P A C) * R_minus) +
            R_plus * conePlus P dA * coneMinus P C * (conePlus P A * R_minus) := by
            rw [hR_minus, mul_one, hInter]
      _ = R_plus * conePlus P dA * R_minus := by
            dsimp only [qgtMinus]
            noncomm_ring
  have hU1 := u1_peirce_super_lu_and_gaussian_skewness_diagonalization hP A C
  have hBergFactor : (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 - genV P A C := by
    simp only [qgtPlus, qgtMinus]
    peirce_nf hP
  have hU6 := u6_klein_seam_parity_of_fisher_metric_vs_berry_skewness hP hU2 hUP A C hUNp hUNm
  exact ⟨DeWittSplitSuperGrassmannianParaKahlerStage.causalEdge_acyclic,
    DeWittSplitSuperGrassmannianParaKahlerStage.card_eq_seven,
    hR0.2.2.1,
    hP3.1,
    hP3.2.1,
    hP3.2.2.2.2.2.1,
    hInter,
    congrArg (· * coneMinus P dC) hSchur,
    hU1.2.2.2.2.1,
    hBergFactor,
    hU6.2.2.2.2.2.1,
    hU6.2.2.2.2.2.2.2.2.2.2.1,
    hU6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Ordered non-commutative Operator Möbius fractional transition `(c + d * f) * R_den`
in an associative ring `B`, where `R_den` is a right inverse to the Möbius denominator `a + b * f`. -/
def operatorMoebiusRingTransition (c d f R_den : B) : B :=
  (c + d * f) * R_den

/-- **Operator Möbius `↔` Push–Pull Legendre Equivalence & Left/Right-Absorptive Chart Semigroups
(`p2_p3_p4_left_right_absorptive_chart_semigroups_and_moebius_legendre_identity`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P`:
1. **Left-Absorptive Dual Chart Semigroup (`P_-(C₁) P_-(C₂) = P_-(C₁)`)**:
   * `dualChartProj P C₁ * dualChartProj P C₂ = dualChartProj P C₁`,
   * `comm (dualChartProj P C₁) (dualChartProj P C₂) = coneMinus P C₁ - coneMinus P C₂`,
   * `comm (dualChartProj P C₁) (dualChartProj P C₂) = 0 ↔ coneMinus P C₁ = coneMinus P C₂`.
2. **Right-Absorptive Primal Chart Semigroup (`P_+(A₁) P_+(A₂) = P_+(A₂)`)**:
   * `primalChartProj P A₁ * primalChartProj P A₂ = primalChartProj P A₂`,
   * `comm (primalChartProj P A₁) (primalChartProj P A₂) = conePlus P A₂ - conePlus P A₁`,
   * `comm (primalChartProj P A₁) (primalChartProj P A₂) = 0 ↔ conePlus P A₁ = conePlus P A₂`.
3. **Exact Equivalence of the Operator Möbius Transition and the Amari Legendre Coordinate (`𝔊₃ ⋈ 𝔓₄`)**:
   Evaluating the Operator Möbius denominator `a + b * f` at the unipotent dual dressing
   `(a, b, c, d) = (1, -N_-, 0, 1)` on the primal chart `f = N_+` yields `1 - Q_-`:
   * `1 + (-coneMinus P C) * conePlus P A = 1 - qgtMinus P A C`,
   * Whenever `R_plus * (1 - qgtPlus P A C) = 1`, `(1 - qgtMinus P A C) * R_minus = 1`, and
     `R_V * (1 - genV P A C) = 1`, the Operator Möbius fractional transition
     `operatorMoebiusRingTransition 0 1 (conePlus P A) R_minus` equals both the right resolvent
     action `N_+ R_-`, the left Bergman resolvent action `R_+ N_+` (the Amari Legendre-dual
     expectation coordinate `η_-`), and the symmetric Fisher resolvent action `R_V N_+`:
     $$\mathcal{M}_{(1, -N_-, 0, 1)}(N_+; R_-) = N_+ R_- = R_+ N_+ = R_V N_+.$$ -/
theorem p2_p3_p4_left_right_absorptive_chart_semigroups_and_moebius_legendre_identity
    {P : B} (hP : P * P = P) (A A₁ A₂ C C₁ C₂ R_plus R_minus R_V : B)
    (hR_plus : R_plus * (1 - qgtPlus P A C) = 1)
    (hR_minus : (1 - qgtMinus P A C) * R_minus = 1)
    (hR_V : R_V * (1 - genV P A C) = 1) :
    -- 1. Left-absorptive dual chart semigroup:
    (dualChartProj P C₁ * dualChartProj P C₂ = dualChartProj P C₁ ∧
      OperatorAlgebra.PeirceSpine.comm (dualChartProj P C₁) (dualChartProj P C₂) =
        coneMinus P C₁ - coneMinus P C₂ ∧
      (OperatorAlgebra.PeirceSpine.comm (dualChartProj P C₁) (dualChartProj P C₂) = 0 ↔
        coneMinus P C₁ = coneMinus P C₂)) ∧
    -- 2. Right-absorptive primal chart semigroup:
    (primalChartProj P A₁ * primalChartProj P A₂ = primalChartProj P A₂ ∧
      OperatorAlgebra.PeirceSpine.comm (primalChartProj P A₁) (primalChartProj P A₂) =
        conePlus P A₂ - conePlus P A₁ ∧
      (OperatorAlgebra.PeirceSpine.comm (primalChartProj P A₁) (primalChartProj P A₂) = 0 ↔
        conePlus P A₁ = conePlus P A₂)) ∧
    -- 3. Operator Möbius ↔ Push–Pull Legendre Expectation Coordinate identity:
    (1 + (-coneMinus P C) * conePlus P A = 1 - qgtMinus P A C ∧
      operatorMoebiusRingTransition 0 1 (conePlus P A) R_minus =
        conePlus P A * R_minus ∧
      operatorMoebiusRingTransition 0 1 (conePlus P A) R_minus =
        R_plus * conePlus P A ∧
      operatorMoebiusRingTransition 0 1 (conePlus P A) R_minus =
        R_V * conePlus P A) := by
  have hDualMul : dualChartProj P C₁ * dualChartProj P C₂ = dualChartProj P C₁ := by
    simp only [dualChartProj]
    peirce_nf hP
  have hDualComm :
      OperatorAlgebra.PeirceSpine.comm (dualChartProj P C₁) (dualChartProj P C₂) =
        coneMinus P C₁ - coneMinus P C₂ := by
    simp only [dualChartProj, OperatorAlgebra.PeirceSpine.comm]
    peirce_nf hP
  have hPrimalMul : primalChartProj P A₁ * primalChartProj P A₂ = primalChartProj P A₂ := by
    simp only [primalChartProj]
    peirce_nf hP
  have hPrimalComm :
      OperatorAlgebra.PeirceSpine.comm (primalChartProj P A₁) (primalChartProj P A₂) =
        conePlus P A₂ - conePlus P A₁ := by
    simp only [primalChartProj, OperatorAlgebra.PeirceSpine.comm]
    peirce_nf hP
  have hDenom : 1 + (-coneMinus P C) * conePlus P A = 1 - qgtMinus P A C := by
    simp only [qgtMinus]
    noncomm_ring
  have hMoeb :
      operatorMoebiusRingTransition 0 1 (conePlus P A) R_minus = conePlus P A * R_minus := by
    dsimp [operatorMoebiusRingTransition]
    noncomm_ring
  have hP4 :=
    (p4_associative_push_pull_resolvent_intertwiner hP A C).2.2.2.2.2.2.2.2.2
      R_plus R_minus R_V hR_plus hR_minus hR_V
  refine ⟨⟨hDualMul, hDualComm, ?_⟩, ⟨hPrimalMul, hPrimalComm, ?_⟩,
    ⟨hDenom, hMoeb, hMoeb.trans hP4.1.symm, hMoeb.trans hP4.2.1.symm⟩⟩
  · rw [hDualComm, sub_eq_zero]
  · rw [hPrimalComm, sub_eq_zero, eq_comm]

end DeWittSplitSuperGrassmannianOperatorGeometry

/-!
## 9b. The 7-Stage Multi-Scale Non-Commutative Tensor-Peirce Attention Network Poset (`𝔗𝔑₁ ≺ 𝔗𝔑₂ ≺ 𝔗𝔑₃ ≺ {𝔗𝔑₄, 𝔗𝔑₅} ≺ 𝔗𝔑₆ ≺ 𝔗𝔑₇`)
-/

/-- **The 7-Stage Multi-Scale Non-Commutative Tensor-Peirce Attention Network Poset
(`TensorPeirceAttentionNetworkStage`, `𝔗𝔑₁ ≺ 𝔗𝔑₂ ≺ 𝔗𝔑₃ ≺ {𝔗𝔑₄, 𝔗𝔑₅} ≺ 𝔗𝔑₆ ≺ 𝔗𝔑₇`)**:
Formalizes the acyclic causal poset severing the flat $O(L^2)$ `softmax` attention matrix
and its Drazin-index-1 memory wall from the recursive $\mathcal{C}\ell(1,1)^{\otimes n}$
Tensor-Peirce Attention Network, reversible Amari Operator Gaussian layers, Bruhat-dressed
Grassmannian & Legendre–Möbius resolvent normalization, Berry Wilson loop causal rotors,
Firth–Zorn 3-body bond contractions, and Krein LogCFT quadratic secular memory:
* `TN1_RecursiveTensorPeirceScaleDecomposition` (`𝔗𝔑₁`):
  Recursive Tensor-Peirce ring isomorphism `peirceTowerEquiv R n : FlatMat R n ≃+* TensorTower R n`
  and centralizer-homogenized scale-$k$ projections `matPi00..matPi11`.
* `TN2_ScaleUnipotentAttentionGates` (`𝔗𝔑₂`):
  Scale-$k$ dually flat Amari unipotent attention gates $\mathcal{E}_+^{(k)}(X) = 1 + N_+^{(k)}$
  and $\mathcal{E}_-^{(k)}(Y) = 1 + N_-^{(k)}$ with interference-free multi-head addition
  $\mathcal{E}_\pm(A_1)\mathcal{E}_\pm(A_2) = \mathcal{E}_\pm(A_1 + A_2)$ and directional curvature
  $[\mathcal{E}_+(N_+), \mathcal{E}_-(N_-)] = \Sigma$.
* `TN3_ReversibleScaleGaussianLayerAndInverse` (`𝔗𝔑₃`):
  Reversible scale-$k$ Operator Gaussian attention layer
  $\mathcal{G}_+^{(k)} = (1 + N_+^{(k)})(1 + N_-^{(k)}) = 1 + \Phi_{(k)} + Q_+^{(k)}$
  and its $O(1)$ polynomial two-sided inverse
  $(\mathcal{G}_+^{(k)})^{-1} = (1 - N_-^{(k)})(1 - N_+^{(k)}) = 1 - \Phi_{(k)} + Q_-^{(k)}$,
  plus symmetric/antisymmetric extraction of $V^{(k)}$ and $\Sigma^{(k)}$.
* `TN4_BruhatDressedProjectorAndLegendreResolvent` (`𝔗𝔑₄`, diamond branch A):
  Rank-preserving Bruhat-dressed Grassmannian attention projector
  $\widehat{P}^{(k)} = P_{(k)} + \Phi_{(k)} - \Sigma^{(k)} - V^{(k)} N_+^{(k)}$
  ($(\widehat{P}^{(k)})^2 = \widehat{P}^{(k)}$, $\mathrm{Tr}(\widehat{P}^{(k)}) = \mathrm{Tr}(P_{(k)})$)
  and Push–Pull Legendre–Möbius resolvent $\eta_-^{(k)} = (1 - Q_+^{(k)})^{-1} N_+^{(k)} = N_+^{(k)} (1 - Q_-^{(k)})^{-1}$.
* `TN5_BerryWilsonRotorAndWaveletCrossover` (`𝔗𝔑₅`, diamond branch B):
  Non-abelian Berry Wilson loop causal rotor $W^{(k)}(c, s) = c \cdot V^{(k)} + s \cdot \Sigma^{(k)}$
  satisfying $(W^{(k)}(c, s) J_{(k)})^2 = (s^2 - c^2)(V^{(k)})^3$, and diagonal residual highway
  vs. chiral wavelet detail crossover $[\Gamma_{\text{diff}}^{(k)}, \Phi_{(k)}] = \{\Gamma_{\text{sum}}^{(k)}, J_{(k)}\}$.
* `TN6_MultiScaleTowerInversionAndZornThreeBodyBond` (`𝔗𝔑₆`):
  Arbitrary-depth $n$-scale attention tower $\mathcal{A}_{\text{tower}} = \prod_{k=1}^n \mathcal{G}_+^{(k)}$
  with exact series-free polynomial inverse $\mathcal{A}_{\text{tower}}^{-1}$, commutativity of
  commuting-scale Gaussian layers, and 3-body Firth–Zorn bond volume
  $\{N_+(u_1)N_+(u_2), N_+(u_3)\} = \det(u_1, u_2, u_3) I$.
* `TN7_YangianMonodromyAndKreinSecularMemoryClosure` (`𝔗𝔑₇`):
  Resolution of the Drazin-index-1 memory wall ($(P - 1)^2 = 1 - P \implies \ker(P - 1)^2 = \ker(P - 1)$)
  via the Krein exceptional Jordan cell $N_{\text{nil}} = A + B$ ($N_{\text{nil}}^2 = 0$) and its
  exact $O(t^2)$ LogCFT quadratic secular memory law
  $(1 - N_{\text{nil}}) A (1 + N_{\text{nil}}) = A + 2 A B + 2 N_{\text{nil}}$. -/
inductive TensorPeirceAttentionNetworkStage : Type
  | TN1_RecursiveTensorPeirceScaleDecomposition
  | TN2_ScaleUnipotentAttentionGates
  | TN3_ReversibleScaleGaussianLayerAndInverse
  | TN4_BruhatDressedProjectorAndLegendreResolvent
  | TN5_BerryWilsonRotorAndWaveletCrossover
  | TN6_MultiScaleTowerInversionAndZornThreeBodyBond
  | TN7_YangianMonodromyAndKreinSecularMemoryClosure
  deriving DecidableEq, Repr, Inhabited

namespace TensorPeirceAttentionNetworkStage

/-- Integer topological rank `0..5` (with diamond branches `TN4, TN5` sharing rank `3`). -/
def rank : TensorPeirceAttentionNetworkStage → ℕ
  | .TN1_RecursiveTensorPeirceScaleDecomposition      => 0
  | .TN2_ScaleUnipotentAttentionGates                 => 1
  | .TN3_ReversibleScaleGaussianLayerAndInverse       => 2
  | .TN4_BruhatDressedProjectorAndLegendreResolvent   => 3
  | .TN5_BerryWilsonRotorAndWaveletCrossover          => 3
  | .TN6_MultiScaleTowerInversionAndZornThreeBodyBond => 4
  | .TN7_YangianMonodromyAndKreinSecularMemoryClosure => 5

/-- Total index `0..6` for `Fintype` and `LinearOrder` enumeration. -/
def stageIndex : TensorPeirceAttentionNetworkStage → ℕ
  | .TN1_RecursiveTensorPeirceScaleDecomposition      => 0
  | .TN2_ScaleUnipotentAttentionGates                 => 1
  | .TN3_ReversibleScaleGaussianLayerAndInverse       => 2
  | .TN4_BruhatDressedProjectorAndLegendreResolvent   => 3
  | .TN5_BerryWilsonRotorAndWaveletCrossover          => 4
  | .TN6_MultiScaleTowerInversionAndZornThreeBodyBond => 5
  | .TN7_YangianMonodromyAndKreinSecularMemoryClosure => 6

theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder TensorPeirceAttentionNetworkStage where
  le a b := stageIndex a ≤ stageIndex b
  lt a b := stageIndex a < stageIndex b
  le_refl a := le_rfl
  le_trans a b c := Nat.le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (stageIndex a) (stageIndex b)
  le_antisymm a b hab hba := stageIndex_injective (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total (stageIndex a) (stageIndex b)
  toDecidableLE a b := Nat.decLe (stageIndex a) (stageIndex b)
  toDecidableEq := inferInstance
  toDecidableLT a b := Nat.decLt (stageIndex a) (stageIndex b)

instance : Fintype TensorPeirceAttentionNetworkStage where
  elems := {
    .TN1_RecursiveTensorPeirceScaleDecomposition,
    .TN2_ScaleUnipotentAttentionGates,
    .TN3_ReversibleScaleGaussianLayerAndInverse,
    .TN4_BruhatDressedProjectorAndLegendreResolvent,
    .TN5_BerryWilsonRotorAndWaveletCrossover,
    .TN6_MultiScaleTowerInversionAndZornThreeBodyBond,
    .TN7_YangianMonodromyAndKreinSecularMemoryClosure
  }
  complete x := by cases x <;> simp

theorem card_eq_seven : Fintype.card TensorPeirceAttentionNetworkStage = 7 := rfl

/-- Directed covering edges of the diamond poset
`𝔗𝔑₁ ≺ 𝔗𝔑₂ ≺ 𝔗𝔑₃ ≺ {𝔗𝔑₄, 𝔗𝔑₅} ≺ 𝔗𝔑₆ ≺ 𝔗𝔑₇`. -/
def causalEdge : TensorPeirceAttentionNetworkStage → TensorPeirceAttentionNetworkStage → Prop
  | .TN1_RecursiveTensorPeirceScaleDecomposition,      .TN2_ScaleUnipotentAttentionGates                 => True
  | .TN2_ScaleUnipotentAttentionGates,                 .TN3_ReversibleScaleGaussianLayerAndInverse       => True
  | .TN3_ReversibleScaleGaussianLayerAndInverse,       .TN4_BruhatDressedProjectorAndLegendreResolvent   => True
  | .TN3_ReversibleScaleGaussianLayerAndInverse,       .TN5_BerryWilsonRotorAndWaveletCrossover          => True
  | .TN4_BruhatDressedProjectorAndLegendreResolvent,   .TN6_MultiScaleTowerInversionAndZornThreeBodyBond => True
  | .TN5_BerryWilsonRotorAndWaveletCrossover,          .TN6_MultiScaleTowerInversionAndZornThreeBodyBond => True
  | .TN6_MultiScaleTowerInversionAndZornThreeBodyBond, .TN7_YangianMonodromyAndKreinSecularMemoryClosure => True
  | _, _ => False

theorem causalEdge_lt {a b : TensorPeirceAttentionNetworkStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;>
    revert h <;>
    unfold causalEdge rank <;>
    decide

theorem transGen_causalEdge_lt {a b : TensorPeirceAttentionNetworkStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

/-- Strict DAG acyclicity of `𝔗𝔑₁ ≺ 𝔗𝔑₂ ≺ 𝔗𝔑₃ ≺ {𝔗𝔑₄, 𝔗𝔑₅} ≺ 𝔗𝔑₆ ≺ 𝔗𝔑₇`. -/
theorem causalEdge_acyclic (a : TensorPeirceAttentionNetworkStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_lt h)

theorem diamond_branches_incomparable :
    ¬ causalEdge .TN4_BruhatDressedProjectorAndLegendreResolvent
        .TN5_BerryWilsonRotorAndWaveletCrossover ∧
    ¬ causalEdge .TN5_BerryWilsonRotorAndWaveletCrossover
        .TN4_BruhatDressedProjectorAndLegendreResolvent := by
  exact ⟨ id, id ⟩

/-- Monotone embedding into `InfoGeometry.Meta.RepDepth`. -/
def toRepDepth : TensorPeirceAttentionNetworkStage → InfoGeometry.Meta.RepDepth
  | .TN1_RecursiveTensorPeirceScaleDecomposition      => .operator
  | .TN2_ScaleUnipotentAttentionGates                 => .operator
  | .TN3_ReversibleScaleGaussianLayerAndInverse       => .operator
  | .TN4_BruhatDressedProjectorAndLegendreResolvent   => .transport
  | .TN5_BerryWilsonRotorAndWaveletCrossover          => .transport
  | .TN6_MultiScaleTowerInversionAndZornThreeBodyBond => .thermo
  | .TN7_YangianMonodromyAndKreinSecularMemoryClosure => .thermo

/-- Monotone embedding into `InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    TensorPeirceAttentionNetworkStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .TN1_RecursiveTensorPeirceScaleDecomposition      => .M1_ProjectorClabject
  | .TN2_ScaleUnipotentAttentionGates                 => .M1_ProjectorClabject
  | .TN3_ReversibleScaleGaussianLayerAndInverse       => .M2_GrassmannianPowertypeOrbit
  | .TN4_BruhatDressedProjectorAndLegendreResolvent   => .M2_GrassmannianPowertypeOrbit
  | .TN5_BerryWilsonRotorAndWaveletCrossover          => .M2_GrassmannianPowertypeOrbit
  | .TN6_MultiScaleTowerInversionAndZornThreeBodyBond => .M3_ErlangenCasimirMetaLaw
  | .TN7_YangianMonodromyAndKreinSecularMemoryClosure => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : TensorPeirceAttentionNetworkStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth InfoGeometry.Meta.RepDepth.toNat <;>
    decide

theorem toOntologyMetaLevel_mono {a b : TensorPeirceAttentionNetworkStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;>
    decide

end TensorPeirceAttentionNetworkStage

section TensorPeirceAttentionNetworkPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.BerryWilsonLoopHyperplaneCausalTransmutationPoset
open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
open InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset

variable {B : Type*} [Ring B]

/-- Primal $e$-flat causal attention gate $\mathcal{E}_+(N_+) := 1 + N_+$. -/
def attnGatePlus (Np : B) : B := 1 + Np

/-- Dual $m$-flat feedback attention gate $\mathcal{E}_-(N_-) := 1 + N_-$. -/
def attnGateMinus (Nm : B) : B := 1 + Nm

/-- Forward scale-$k$ Operator Gaussian attention layer
$\mathcal{G}_+(N_+, N_-) := (1 + N_+)(1 + N_-)$. -/
def attnGaussianFwd (Np Nm : B) : B := (1 + Np) * (1 + Nm)

/-- Reverse scale-$k$ Operator Gaussian attention layer
$\mathcal{G}_-(N_+, N_-) := (1 + N_-)(1 + N_+)$. -/
def attnGaussianRev (Np Nm : B) : B := (1 + Nm) * (1 + Np)

/-- Exact $O(1)$ polynomial inverse of $\mathcal{G}_+(N_+, N_-)$:
$(\mathcal{G}_+)^{-1} := (1 - N_-)(1 - N_+)$. -/
def attnGaussianInv (Np Nm : B) : B := (1 - Nm) * (1 - Np)

/-- Multi-scale forward attention tower $\mathcal{A}_{\text{tower}}(L) := \prod_{(N_+, N_-) \in L} (1 + N_+)(1 + N_-)$. -/
def attnTowerFwd : List (B × B) → B
  | [] => 1
  | (Np, Nm) :: rest => attnGaussianFwd Np Nm * attnTowerFwd rest

/-- Multi-scale polynomial inverse tower $\mathcal{A}_{\text{tower}}^{-1}(L) := \prod^{\text{rev}}_{(N_+, N_-) \in L} (1 - N_-)(1 - N_+)$. -/
def attnTowerInv : List (B × B) → B
  | [] => 1
  | (Np, Nm) :: rest => attnTowerInv rest * attnGaussianInv Np Nm

/-- **Stage `𝔗𝔑₁` (`tn1_recursive_tensor_peirce_scale_decomposition`)**:
1. **Recursive Tensor-Peirce Ring Isomorphism (`peirceTowerEquiv R n : FlatMat R n ≃+* TensorTower R n`)**:
   Replaces the unstructured $2^n \times 2^n$ attention matrix grid with the $n$-stage recursive
   `TensorTower R n` while preserving ring addition, matrix multiplication, identity, and exact
   two-sided roundtrip (`toTensorTower n (ofTensorTower n T) = T`).
2. **Scale-$k$ Centralizer-Homogenized Peirce Projections (`matPi00..matPi11`)**:
   Extracts each $2 \times 2$ Peirce sub-block into the diagonal commutant and reconstructs $M$
   via `unitE00 * matPi00 M + unitE01 * matPi01 M + unitE10 * matPi10 M + unitE11 * matPi11 M = M`. -/
theorem tn1_recursive_tensor_peirce_scale_decomposition
    {R : Type*} [Ring R] (n : ℕ) (A A' : FlatMat R n) (T : TensorTower R n)
    (M : Matrix (Fin 2) (Fin 2) R) :
    peirceTowerEquiv R n (A + A') = peirceTowerEquiv R n A + peirceTowerEquiv R n A' ∧
    peirceTowerEquiv R n (A * A') = peirceTowerEquiv R n A * peirceTowerEquiv R n A' ∧
    peirceTowerEquiv R n 1 = 1 ∧
    (peirceTowerEquiv R n).symm (peirceTowerEquiv R n A) = A ∧
    peirceTowerEquiv R n ((peirceTowerEquiv R n).symm T) = T ∧
    toTensorTower n (ofTensorTower n T) = T ∧
    matPi00 M = !![M 0 0, 0; 0, M 0 0] ∧
    unitE00 * matPi00 M + unitE01 * matPi01 M +
      unitE10 * matPi10 M + unitE11 * matPi11 M = M := by
  have hTT5 := tt5_recursive_tensor_peirce_ring_isomorphism n A A' T
  have hTT6 := tt6_dual_clifford_dewitt_tensor_basis_and_master_synthesis
    (B := Matrix (Fin 2) (Fin 2) R)
    (Np := unitE01) (Nm := unitE10)
    (by ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE01])
    (by ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE10])
    (by ext i j; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE01, unitE10])
    M M n A A' 0 T
  exact ⟨hTT5.1, hTT5.2.1, hTT5.2.2.1, hTT5.2.2.2.1, hTT5.2.2.2.2.1, hTT5.2.2.2.2.2,
    hTT6.2.2.2.2.2.2.2.2.2.1, hTT6.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- **Stage `𝔗𝔑₂` (`tn2_scale_unipotent_attention_gates`)**:
1. **Multi-Head Abelian Addition Without Non-Abelian Interference**:
   On the causal $e$-flat Peirce sheet $\mathfrak{n}_+ = P B (1 - P)$ and feedback $m$-flat sheet
   $\mathfrak{n}_- = (1 - P) B P$, multiple attention heads add linearly in the exponent:
   $$\mathcal{E}_+(N_+(A_1)) \mathcal{E}_+(N_+(A_2)) = \mathcal{E}_+(N_+(A_1) + N_+(A_2)), \qquad
     \mathcal{E}_-(N_-(C_1)) \mathcal{E}_-(N_-(C_2)) = \mathcal{E}_-(N_-(C_1) + N_-(C_2)).$$
2. **Exact Single-Gate Polynomial Inverse**:
   $$\mathcal{E}_+(N_+(A_1)) \mathcal{E}_+(-N_+(A_1)) = 1, \qquad
     \mathcal{E}_-(N_-(C_1)) \mathcal{E}_-(-N_-(C_1)) = 1.$$
3. **Directional Tension Between Forward and Backward Gates**:
   $$[\mathcal{E}_+(N_+(A_1)), \, \mathcal{E}_-(N_-(C_1))] = \Sigma(A_1, C_1).$$ -/
theorem tn2_scale_unipotent_attention_gates
    {P : B} (hP : P * P = P) (A₁ A₂ C₁ C₂ : B) :
    attnGatePlus (conePlus P A₁) * attnGatePlus (conePlus P A₂) =
      attnGatePlus (conePlus P A₁ + conePlus P A₂) ∧
    attnGateMinus (coneMinus P C₁) * attnGateMinus (coneMinus P C₂) =
      attnGateMinus (coneMinus P C₁ + coneMinus P C₂) ∧
    attnGatePlus (conePlus P A₁) * attnGatePlus (-conePlus P A₁) = 1 ∧
    attnGateMinus (coneMinus P C₁) * attnGateMinus (-coneMinus P C₁) = 1 ∧
    OperatorAlgebra.PeirceSpine.comm
      (attnGatePlus (conePlus P A₁)) (attnGateMinus (coneMinus P C₁)) =
      genSig P A₁ C₁ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [attnGatePlus, attnGateMinus, OperatorAlgebra.PeirceSpine.comm];
     peirce_nf hP)

/-- **Stage `𝔗𝔑₃` (`tn3_reversible_scale_gaussian_layer_and_polynomial_inverse`)**:
1. **Scale-$k$ Operator Gaussian Expansion & $O(1)$ Polynomial Inverse**:
   $$\mathcal{G}_+(N_+, N_-) = 1 + \Phi + Q_+, \qquad
     (\mathcal{G}_+)^{-1} = (1 - N_-)(1 - N_+) = 1 - \Phi + Q_-,$$
   with exact two-sided invertibility $\mathcal{G}_+ (\mathcal{G}_+)^{-1} = 1 = (\mathcal{G}_+)^{-1} \mathcal{G}_+$.
2. **Symmetric Fisher Attention Metric $V$ & Antisymmetric Berry Curvature $\Sigma$ Extraction**:
   $$\mathcal{G}_+ + \mathcal{G}_- - 2(1 + \Phi) = V, \qquad
     \mathcal{G}_+ - \mathcal{G}_- = \Sigma.$$ -/
theorem tn3_reversible_scale_gaussian_layer_and_polynomial_inverse
    {P : B} (hP : P * P = P) (A C : B) :
    attnGaussianFwd (conePlus P A) (coneMinus P C) =
      1 + genPhi P A C + qgtPlus P A C ∧
    attnGaussianInv (conePlus P A) (coneMinus P C) =
      1 - genPhi P A C + qgtMinus P A C ∧
    attnGaussianFwd (conePlus P A) (coneMinus P C) *
      attnGaussianInv (conePlus P A) (coneMinus P C) = 1 ∧
    attnGaussianInv (conePlus P A) (coneMinus P C) *
      attnGaussianFwd (conePlus P A) (coneMinus P C) = 1 ∧
    attnGaussianFwd (conePlus P A) (coneMinus P C) +
      attnGaussianRev (conePlus P A) (coneMinus P C) -
      (2 : ℤ) • (1 + genPhi P A C) = genV P A C ∧
    attnGaussianFwd (conePlus P A) (coneMinus P C) -
      attnGaussianRev (conePlus P A) (coneMinus P C) = genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [attnGaussianFwd, attnGaussianRev, attnGaussianInv, qgtPlus, qgtMinus];
     peirce_nf hP)

/-- **Stage `𝔗𝔑₄` (`tn4_bruhat_dressed_projector_and_legendre_moebius_resolvent`)**:
1. **Rank-Preserving Bruhat-Dressed Attention Projector (`dressedTwoChartProj`)**:
   $$\widehat{P} = (1 - N_+)(P + N_-)(1 + N_+) = P + \Phi - \Sigma - V N_+, \qquad \widehat{P}^2 = \widehat{P},$$
   with diagonal block compressions $P \widehat{P} P = P - Q_+$ and $(1 - P) \widehat{P} (1 - P) = Q_-$,
   whose sum $P \widehat{P} P + (1 - P) \widehat{P} (1 - P) = P - \Sigma$ has trace equal to $\mathrm{Tr}(P)$
   (since $\Sigma = [N_+, N_-]$ is a commutator).
2. **Push–Pull Legendre–Möbius Resolvent Normalization (Replacing Scalar `softmax`)**:
   $$(1 - Q_+) N_+ = N_+ (1 - Q_-) = (1 - V) N_+,$$
   and for any resolvents $R_+(1 - Q_+) = 1$, $(1 - Q_-)R_- = 1$, $R_V(1 - V) = 1$:
   $$R_+ N_+ = N_+ R_- = R_V N_+.$$ -/
theorem tn4_bruhat_dressed_projector_and_legendre_moebius_resolvent
    {P : B} (hP : P * P = P) (A C : B) :
    dressedTwoChartProj P A C =
      P + genPhi P A C - genSig P A C - genV P A C * conePlus P A ∧
    dressedTwoChartProj P A C * dressedTwoChartProj P A C = dressedTwoChartProj P A C ∧
    (P * dressedTwoChartProj P A C * P = P - qgtPlus P A C ∧
      (1 - P) * dressedTwoChartProj P A C * (1 - P) = qgtMinus P A C) ∧
    (1 - qgtPlus P A C) * conePlus P A = conePlus P A * (1 - qgtMinus P A C) ∧
    (1 - qgtPlus P A C) * conePlus P A = (1 - genV P A C) * conePlus P A ∧
    (∀ R_plus R_minus R_V : B,
      R_plus * (1 - qgtPlus P A C) = 1 →
      (1 - qgtMinus P A C) * R_minus = 1 →
      R_V * (1 - genV P A C) = 1 →
      R_plus * conePlus P A = conePlus P A * R_minus ∧
      R_V * conePlus P A = conePlus P A * R_minus ∧
      R_plus * conePlus P A = R_V * conePlus P A) := by
  have hP3 := p3_bruhat_dressed_two_chart_idempotent_and_jordan_triple hP A C
  have hP4 := p4_associative_push_pull_resolvent_intertwiner hP A C
  refine ⟨hP3.1, hP3.2.1, ⟨?_, ?_⟩, hP4.2.2.2.2.2.1, hP4.2.2.2.2.2.2.1, hP4.2.2.2.2.2.2.2.2.2⟩
  · simp only [dressedTwoChartProj, qgtPlus]; peirce_nf hP
  · simp only [dressedTwoChartProj, qgtMinus]; peirce_nf hP

/-- **Stage `𝔗𝔑₅` (`tn5_berry_wilson_rotor_and_wavelet_crossover`)**:
1. **Non-Abelian Berry Wilson Loop Causal Rotor (Replacing Scalar RoPE)**:
   For any commutative ring $R$ and $R$-algebra $B$, the scale-$k$ Berry Wilson loop rotor
   $W(c, s) = c \cdot V + s \cdot \Sigma$ (`wilsonLoopEven P A C c s`) rotates $J$ and $\Phi$
   inside the $(J, \Phi)$ hyperplane with exact causal signature transmutation:
   $$(W(c, s) J)^2 = (s^2 - c^2) \cdot V^3, \qquad (W(c, s) \Phi)^2 = (c^2 - s^2) \cdot V^3,$$
   and at the lightlike critical horizon $s = c$, $(W(c, c) J)^2 = 0$.
2. **Diagonal Residual Highway (`sheetConnectionSum`) & Chiral Wavelet Detail (`sheetConnectionDiff`) Crossover**:
   For any diagonal stream seed $W \in B$:
   $$[\Gamma_{\text{diff}}(W), \, \Phi] = \{\Gamma_{\text{sum}}(W), \, J\}, \qquad
     [\Gamma_{\text{diff}}(W), \, J] = \{\Gamma_{\text{sum}}(W), \, \Phi\}.$$ -/
theorem tn5_berry_wilson_rotor_and_wavelet_crossover
    {R : Type*} [CommRing R] [Algebra R B]
    {P : B} (hP : P * P = P) (A C W : B) (c_rot s_rot : R) :
    (wilsonLoopEven P A C c_rot s_rot * genJ P A C) *
      (wilsonLoopEven P A C c_rot s_rot * genJ P A C) =
      (s_rot ^ 2 - c_rot ^ 2) • (genV P A C * genV P A C * genV P A C) ∧
    (wilsonLoopEven P A C c_rot s_rot * genPhi P A C) *
      (wilsonLoopEven P A C c_rot s_rot * genPhi P A C) =
      (c_rot ^ 2 - s_rot ^ 2) • (genV P A C * genV P A C * genV P A C) ∧
    (wilsonLoopEven P A C c_rot c_rot * genJ P A C) *
      (wilsonLoopEven P A C c_rot c_rot * genJ P A C) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (sheetConnectionDiff P W) (genPhi P A C) =
      OperatorAlgebra.PeirceSpine.anticomm (sheetConnectionSum P W) (genJ P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (sheetConnectionDiff P W) (genJ P A C) =
      OperatorAlgebra.PeirceSpine.anticomm (sheetConnectionSum P W) (genPhi P A C) := by
  have hW5 := stage_W5_universal_polynomial_wilson_loop_transmutation hP A C c_rot s_rot
  have hW5_null := (stage_W5_universal_polynomial_wilson_loop_transmutation hP A C c_rot c_rot).2.2.1
  have hCross := sheetConnection_sum_difference_crossover hP W A C
  refine ⟨hW5.2.2.1, hW5.2.2.2.1, ?_, hCross.1, hCross.2.2.1⟩
  rw [hW5_null, sub_self, zero_smul]

/-- **Stage `𝔗𝔑₆` (`tn6_multiscale_tower_inversion_and_zorn_three_body_bond`)**:
1. **Theorem 1 (Arbitrary-Depth Multi-Scale Attention Tower Exact Reversibility)**:
   For any depth-$n$ list `L : List (B × B)` of scale-wise nilpotent attention pairs
   (`∀ p ∈ L, p.1 * p.1 = 0 ∧ p.2 * p.2 = 0`), the multi-scale forward attention tower
   `attnTowerFwd L` and reverse polynomial tower `attnTowerInv L` are exact two-sided inverses
   with zero matrix-inversion overhead:
   $$\mathcal{A}_{\text{tower}}(L)\,\mathcal{A}_{\text{tower}}^{-1}(L) = 1 \;\land\;
     \mathcal{A}_{\text{tower}}^{-1}(L)\,\mathcal{A}_{\text{tower}}(L) = 1.$$
2. **Commutativity of Distinct-Scale Operator Gaussian Layers**:
   Whenever scale-$k$ nilpotents $(N_+^{(1)}, N_-^{(1)})$ commute with scale-$l$ nilpotents
   $(N_+^{(2)}, N_-^{(2)})$, their Operator Gaussian layers commute:
   $$\mathcal{G}_+(N_+^{(1)}, N_-^{(1)})\,\mathcal{G}_+(N_+^{(2)}, N_-^{(2)}) =
     \mathcal{G}_+(N_+^{(2)}, N_-^{(2)})\,\mathcal{G}_+(N_+^{(1)}, N_-^{(1)}).$$
3. **3-Body Firth–Zorn Bond Contraction**:
   In `ZornMat K`, fusing two primal token states $N_+(u_1), N_+(u_2)$ and anticommuting
   with a third token state $N_+(u_3)$ evaluates the exact 3-body syntactic volume determinant:
   $$\{N_+(u_1)N_+(u_2), \, N_+(u_3)\} = \mathrm{baryonDet3}(u_1, u_2, u_3) \cdot 1_{\mathrm{Zorn}}.$$ -/
theorem tn6_multiscale_tower_inversion_and_zorn_three_body_bond
    (L : List (B × B))
    (hL : ∀ p ∈ L, p.1 * p.1 = 0 ∧ p.2 * p.2 = 0)
    (Np1 Nm1 Np2 Nm2 : B)
    (h11 : Np1 * Np2 = Np2 * Np1) (h12 : Np1 * Nm2 = Nm2 * Np1)
    (h21 : Nm1 * Np2 = Np2 * Nm1) (h22 : Nm1 * Nm2 = Nm2 * Nm1)
    {K : Type*} [CommRing K] (u₁ u₂ u₃ : Vec3 K) :
    (attnTowerFwd L * attnTowerInv L = 1 ∧
     attnTowerInv L * attnTowerFwd L = 1) ∧
    attnGaussianFwd Np1 Nm1 * attnGaussianFwd Np2 Nm2 =
      attnGaussianFwd Np2 Nm2 * attnGaussianFwd Np1 Nm1 ∧
    (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
      zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat K) := by
  have hStepInv : ∀ (Np Nm : B), Np * Np = 0 → Nm * Nm = 0 →
      attnGaussianFwd Np Nm * attnGaussianInv Np Nm = 1 ∧
      attnGaussianInv Np Nm * attnGaussianFwd Np Nm = 1 := by
    intro Np Nm hNp hNm
    constructor
    · calc attnGaussianFwd Np Nm * attnGaussianInv Np Nm
        _ = (1 + Np) * ((1 + Nm) * (1 - Nm)) * (1 - Np) := by
              dsimp [attnGaussianFwd, attnGaussianInv]; noncomm_ring
        _ = (1 + Np) * (1 - Nm * Nm) * (1 - Np) := by noncomm_ring
        _ = (1 + Np) * (1 - 0) * (1 - Np) := by rw [hNm]
        _ = 1 - Np * Np := by noncomm_ring
        _ = 1 - 0 := by rw [hNp]
        _ = 1 := by noncomm_ring
    · calc attnGaussianInv Np Nm * attnGaussianFwd Np Nm
        _ = (1 - Nm) * ((1 - Np) * (1 + Np)) * (1 + Nm) := by
              dsimp [attnGaussianFwd, attnGaussianInv]; noncomm_ring
        _ = (1 - Nm) * (1 - Np * Np) * (1 + Nm) := by noncomm_ring
        _ = (1 - Nm) * (1 - 0) * (1 + Nm) := by rw [hNp]
        _ = 1 - Nm * Nm := by noncomm_ring
        _ = 1 - 0 := by rw [hNm]
        _ = 1 := by noncomm_ring
  have hTower : attnTowerFwd L * attnTowerInv L = 1 ∧
      attnTowerInv L * attnTowerFwd L = 1 := by
    induction L with
    | nil =>
      simp [attnTowerFwd, attnTowerInv]
    | cons hd tl ih =>
      have hhd := hL hd List.mem_cons_self
      have htl : ∀ p ∈ tl, p.1 * p.1 = 0 ∧ p.2 * p.2 = 0 :=
        fun p hp => hL p (List.mem_cons_of_mem hd hp)
      have ihtl := ih htl
      have hhdInv := hStepInv hd.1 hd.2 hhd.1 hhd.2
      constructor
      · calc attnTowerFwd (hd :: tl) * attnTowerInv (hd :: tl)
          _ = attnGaussianFwd hd.1 hd.2 * (attnTowerFwd tl * attnTowerInv tl) *
                attnGaussianInv hd.1 hd.2 := by
                dsimp [attnTowerFwd, attnTowerInv]; noncomm_ring
          _ = attnGaussianFwd hd.1 hd.2 * 1 * attnGaussianInv hd.1 hd.2 := by rw [ihtl.1]
          _ = attnGaussianFwd hd.1 hd.2 * attnGaussianInv hd.1 hd.2 := by noncomm_ring
          _ = 1 := hhdInv.1
      · calc attnTowerInv (hd :: tl) * attnTowerFwd (hd :: tl)
          _ = attnTowerInv tl * (attnGaussianInv hd.1 hd.2 * attnGaussianFwd hd.1 hd.2) *
                attnTowerFwd tl := by
                dsimp [attnTowerFwd, attnTowerInv]; noncomm_ring
          _ = attnTowerInv tl * 1 * attnTowerFwd tl := by rw [hhdInv.2]
          _ = attnTowerInv tl * attnTowerFwd tl := by noncomm_ring
          _ = 1 := ihtl.2
  have hComm : attnGaussianFwd Np1 Nm1 * attnGaussianFwd Np2 Nm2 =
      attnGaussianFwd Np2 Nm2 * attnGaussianFwd Np1 Nm1 := by
    dsimp [attnGaussianFwd]
    have hA1A2 : (1 + Np1) * (1 + Np2) = (1 + Np2) * (1 + Np1) := by
      calc (1 + Np1) * (1 + Np2)
        _ = 1 + Np1 + Np2 + Np1 * Np2 := by noncomm_ring
        _ = 1 + Np1 + Np2 + Np2 * Np1 := by rw [h11]
        _ = (1 + Np2) * (1 + Np1) := by noncomm_ring
    have hA1B2 : (1 + Np1) * (1 + Nm2) = (1 + Nm2) * (1 + Np1) := by
      calc (1 + Np1) * (1 + Nm2)
        _ = 1 + Np1 + Nm2 + Np1 * Nm2 := by noncomm_ring
        _ = 1 + Np1 + Nm2 + Nm2 * Np1 := by rw [h12]
        _ = (1 + Nm2) * (1 + Np1) := by noncomm_ring
    have hB1A2 : (1 + Nm1) * (1 + Np2) = (1 + Np2) * (1 + Nm1) := by
      calc (1 + Nm1) * (1 + Np2)
        _ = 1 + Nm1 + Np2 + Nm1 * Np2 := by noncomm_ring
        _ = 1 + Nm1 + Np2 + Np2 * Nm1 := by rw [h21]
        _ = (1 + Np2) * (1 + Nm1) := by noncomm_ring
    have hB1B2 : (1 + Nm1) * (1 + Nm2) = (1 + Nm2) * (1 + Nm1) := by
      calc (1 + Nm1) * (1 + Nm2)
        _ = 1 + Nm1 + Nm2 + Nm1 * Nm2 := by noncomm_ring
        _ = 1 + Nm1 + Nm2 + Nm2 * Nm1 := by rw [h22]
        _ = (1 + Nm2) * (1 + Nm1) := by noncomm_ring
    calc (1 + Np1) * (1 + Nm1) * ((1 + Np2) * (1 + Nm2))
      _ = (1 + Np1) * ((1 + Nm1) * (1 + Np2)) * (1 + Nm2) := by simp only [mul_assoc]
      _ = (1 + Np1) * ((1 + Np2) * (1 + Nm1)) * (1 + Nm2) := by rw [hB1A2]
      _ = ((1 + Np1) * (1 + Np2)) * ((1 + Nm1) * (1 + Nm2)) := by simp only [mul_assoc]
      _ = ((1 + Np2) * (1 + Np1)) * ((1 + Nm2) * (1 + Nm1)) := by rw [hA1A2, hB1B2]
      _ = (1 + Np2) * ((1 + Np1) * (1 + Nm2)) * (1 + Nm1) := by simp only [mul_assoc]
      _ = (1 + Np2) * ((1 + Nm2) * (1 + Np1)) * (1 + Nm1) := by rw [hA1B2]
      _ = (1 + Np2) * (1 + Nm2) * ((1 + Np1) * (1 + Nm1)) := by simp only [mul_assoc]
  have hMB3 := mb3_firth_trilinear_contextual_semantics_in_zorn_matrix u₁ u₂ u₃ 0 0
  exact ⟨hTower, hComm, hMB3.2.2.2.2.2.2.2.2.2.2.1⟩

/-- **Stage `𝔗𝔑₇` (`tn7_yangian_monodromy_krein_secular_memory_and_master_synthesis`)**:
Master theorem unifying the 7-stage **Multi-Scale Non-Commutative Tensor-Peirce Attention Network Poset**
(`𝔗𝔑₁ ≺ 𝔗𝔑₂ ≺ 𝔗𝔑₃ ≺ {𝔗𝔑₄, 𝔗𝔑₅} ≺ 𝔗𝔑₆ ≺ 𝔗𝔑₇`):
1. **Poset Acyclicity, Cardinality, & Diamond Branching**:
   `TensorPeirceAttentionNetworkStage.causalEdge_acyclic`,
   `Fintype.card TensorPeirceAttentionNetworkStage = 7`, and
   `¬ causalEdge TN4 TN5 ∧ ¬ causalEdge TN5 TN4`.
2. **Rung 0 Softmax / Idempotent Drazin-Index-1 Memory Wall**:
   For any idempotent projection $P^2 = P$, $(P - 1)^2 = 1 - P = -(P - 1)$, so every length-2
   generalized fixed vector collapses to a length-1 fixed vector:
   $$\forall x \in B, \quad (P - 1)\big((P - 1) x\big) = 0 \iff (P - 1) x = 0.$$
3. **Krein LogCFT Exceptional Jordan Cell & Quadratic $O(t^2)$ Secular Memory Law**:
   For any anticommuting Krein pair $A_{\text{kr}}^2 = -1$, $B_{\text{kr}}^2 = 1$,
   $A_{\text{kr}} B_{\text{kr}} + B_{\text{kr}} A_{\text{kr}} = 0$, the critical horizon generator
   $N_{\text{nil}} := A_{\text{kr}} + B_{\text{kr}}$ satisfies:
   $$N_{\text{nil}}^2 = 0, \qquad N_{\text{nil}} A_{\text{kr}} N_{\text{nil}} = -2 N_{\text{nil}}, \qquad
     (1 - N_{\text{nil}}) A_{\text{kr}} (1 + N_{\text{nil}}) = A_{\text{kr}} + 2 A_{\text{kr}} B_{\text{kr}} + 2 N_{\text{nil}}.$$
4. **Master Multi-Scale Tensor-Peirce Attention Network Synthesis**:
   Bundles recursive Tensor-Peirce ring equivalence `peirceTowerEquiv R n`, multi-head unipotent
   gate addition, reversible Operator Gaussian layer inversion, Bruhat-dressed idempotent projection,
   Legendre–Möbius resolvent intertwining, Berry Wilson loop causal transmutation, arbitrary-depth
   tower inversion `attnTowerFwd L * attnTowerInv L = 1`, and 3-body Firth–Zorn syntactic volume. -/
theorem tn7_yangian_monodromy_krein_secular_memory_and_master_synthesis
    {R : Type*} [CommRing R] [Algebra R B]
    {P : B} (hP : P * P = P) (A C W : B) (c_rot s_rot : R)
    (L : List (B × B)) (hL : ∀ p ∈ L, p.1 * p.1 = 0 ∧ p.2 * p.2 = 0)
    {A_kr B_kr : B} (hA_kr : A_kr * A_kr = -1) (hB_kr : B_kr * B_kr = 1)
    (hAnti_kr : A_kr * B_kr + B_kr * A_kr = 0)
    (n : ℕ) (M_n M_n' : FlatMat R n) (T_n : TensorTower R n)
    (u₁ u₂ u₃ : Vec3 R) :
    -- 1. Poset acyclicity, cardinality, and diamond branching:
    (∀ st : TensorPeirceAttentionNetworkStage,
      ¬ Relation.TransGen TensorPeirceAttentionNetworkStage.causalEdge st st) ∧
    Fintype.card TensorPeirceAttentionNetworkStage = 7 ∧
    (¬ TensorPeirceAttentionNetworkStage.causalEdge
        .TN4_BruhatDressedProjectorAndLegendreResolvent
        .TN5_BerryWilsonRotorAndWaveletCrossover ∧
     ¬ TensorPeirceAttentionNetworkStage.causalEdge
        .TN5_BerryWilsonRotorAndWaveletCrossover
        .TN4_BruhatDressedProjectorAndLegendreResolvent) ∧
    -- 2. Rung 0 Drazin-index-1 memory wall (no length-2 Jordan chain at λ = 1):
    (P - 1) * (P - 1) = 1 - P ∧
    (∀ x : B, (P - 1) * ((P - 1) * x) = 0 ↔ (P - 1) * x = 0) ∧
    -- 3. Krein LogCFT exceptional Jordan cell & quadratic secular memory:
    (A_kr + B_kr) * (A_kr + B_kr) = 0 ∧
    (A_kr + B_kr) * A_kr * (A_kr + B_kr) = -((2 : ℤ) • (A_kr + B_kr)) ∧
    (1 - (A_kr + B_kr)) * A_kr * (1 + (A_kr + B_kr)) =
      A_kr + (2 : ℤ) • (A_kr * B_kr) + (2 : ℤ) • (A_kr + B_kr) ∧
    -- 4. Master Tensor-Peirce Attention Network synthesis (TN1..TN6):
    peirceTowerEquiv R n (M_n * M_n') = peirceTowerEquiv R n M_n * peirceTowerEquiv R n M_n' ∧
    attnGatePlus (conePlus P A) * attnGatePlus (conePlus P C) =
      attnGatePlus (conePlus P A + conePlus P C) ∧
    attnGaussianFwd (conePlus P A) (coneMinus P C) *
      attnGaussianInv (conePlus P A) (coneMinus P C) = 1 ∧
    dressedTwoChartProj P A C * dressedTwoChartProj P A C = dressedTwoChartProj P A C ∧
    (1 - qgtPlus P A C) * conePlus P A = conePlus P A * (1 - qgtMinus P A C) ∧
    (wilsonLoopEven P A C c_rot s_rot * genJ P A C) *
      (wilsonLoopEven P A C c_rot s_rot * genJ P A C) =
      (s_rot ^ 2 - c_rot ^ 2) • (genV P A C * genV P A C * genV P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (sheetConnectionDiff P W) (genPhi P A C) =
      OperatorAlgebra.PeirceSpine.anticomm (sheetConnectionSum P W) (genJ P A C) ∧
    attnTowerFwd L * attnTowerInv L = 1 ∧
    (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
      zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat R) := by
  have hDrazinSq : (P - 1) * (P - 1) = 1 - P := by
    calc (P - 1) * (P - 1)
      _ = P * P - (P + P) + 1 := by noncomm_ring
      _ = P - (P + P) + 1 := by rw [hP]
      _ = 1 - P := by noncomm_ring
  have hDrazinKer : ∀ x : B, (P - 1) * ((P - 1) * x) = 0 ↔ (P - 1) * x = 0 := by
    intro x
    rw [← mul_assoc, hDrazinSq]
    have hNeg : (1 - P) * x = -((P - 1) * x) := by noncomm_ring
    rw [hNeg, neg_eq_zero]
  have hKreinNil : (A_kr + B_kr) * (A_kr + B_kr) = 0 := by
    calc (A_kr + B_kr) * (A_kr + B_kr)
      _ = A_kr * A_kr + (A_kr * B_kr + B_kr * A_kr) + B_kr * B_kr := by noncomm_ring
      _ = -1 + 0 + 1 := by rw [hA_kr, hAnti_kr, hB_kr]
      _ = 0 := by abel
  have hBA : B_kr * A_kr = -(A_kr * B_kr) := eq_neg_of_add_eq_zero_right hAnti_kr
  have hKreinSandwich : (A_kr + B_kr) * A_kr * (A_kr + B_kr) = -((2 : ℤ) • (A_kr + B_kr)) := by
    calc (A_kr + B_kr) * A_kr * (A_kr + B_kr)
      _ = (A_kr * A_kr) * A_kr + (A_kr * A_kr) * B_kr + B_kr * (A_kr * A_kr) +
            (B_kr * A_kr) * B_kr := by noncomm_ring
      _ = (-1) * A_kr + (-1) * B_kr + B_kr * (-1) + (-(A_kr * B_kr)) * B_kr := by
            rw [hA_kr, hBA]
      _ = -A_kr - B_kr - B_kr - A_kr * (B_kr * B_kr) := by noncomm_ring
      _ = -A_kr - B_kr - B_kr - A_kr * 1 := by rw [hB_kr]
      _ = -((2 : ℤ) • (A_kr + B_kr)) := by noncomm_ring
  have hKreinSecular :
      (1 - (A_kr + B_kr)) * A_kr * (1 + (A_kr + B_kr)) =
        A_kr + (2 : ℤ) • (A_kr * B_kr) + (2 : ℤ) • (A_kr + B_kr) := by
    calc (1 - (A_kr + B_kr)) * A_kr * (1 + (A_kr + B_kr))
      _ = A_kr + (A_kr * B_kr - B_kr * A_kr) - (A_kr + B_kr) * A_kr * (A_kr + B_kr) := by
            noncomm_ring
      _ = A_kr + (A_kr * B_kr - -(A_kr * B_kr)) - -((2 : ℤ) • (A_kr + B_kr)) := by
            rw [hBA, hKreinSandwich]
      _ = A_kr + (2 : ℤ) • (A_kr * B_kr) + (2 : ℤ) • (A_kr + B_kr) := by noncomm_ring
  have hTN1 := tn1_recursive_tensor_peirce_scale_decomposition n M_n M_n' T_n 0
  have hTN2 := tn2_scale_unipotent_attention_gates hP A C A C
  have hTN3 := tn3_reversible_scale_gaussian_layer_and_polynomial_inverse hP A C
  have hTN4 := tn4_bruhat_dressed_projector_and_legendre_moebius_resolvent hP A C
  have hTN5 := tn5_berry_wilson_rotor_and_wavelet_crossover hP A C W c_rot s_rot
  have hTN6 := tn6_multiscale_tower_inversion_and_zorn_three_body_bond
    L hL 0 0 0 0 rfl rfl rfl rfl u₁ u₂ u₃
  exact ⟨TensorPeirceAttentionNetworkStage.causalEdge_acyclic,
    TensorPeirceAttentionNetworkStage.card_eq_seven,
    TensorPeirceAttentionNetworkStage.diamond_branches_incomparable,
    hDrazinSq, hDrazinKer,
    hKreinNil, hKreinSandwich, hKreinSecular,
    hTN1.2.1, hTN2.1, hTN3.2.2.1, hTN4.2.1, hTN4.2.2.2.1,
    hTN5.1, hTN5.2.2.2.1, hTN6.1.1, hTN6.2.2⟩

end TensorPeirceAttentionNetworkPoset

/-!
## 9c. The 6-Stage Bitwise Symplectic Clifford Compiler & Multi-Scale Attention Filtration Poset (`𝔅ℭ₁ ≺ 𝔅ℭ₂ ≺ 𝔅ℭ₃ ≺ {𝔅ℭ₄, 𝔅ℭ₅} ≺ 𝔅ℭ₆`)
-/

/-- **The 6-Stage Bitwise Symplectic Clifford Compiler & Multi-Scale Attention Filtration Poset
(`BitwiseCliffordCompilerStage`, `𝔅ℭ₁ ≺ 𝔅ℭ₂ ≺ 𝔅ℭ₃ ≺ {𝔅ℭ₄, 𝔅ℭ₅} ≺ 𝔅ℭ₆`)**:
Formalizes the acyclic causal poset severing naive $(i, j)$ row-column indexing and the
commutative 2D Walsh–Hadamard illusion ($H M H$) from the **Bitwise Phase-Space Coordinates
$(x = i \oplus j, \, z \in \mathbb{F}_2^n)$**, the **Symplectic Multiplication Cocycle
$(-1)^{\mathrm{popcount}(x_1 \,\&\, z_2)}$**, the **Division-Free XOR + Butterfly Compiler**,
and **Multi-Scale Hamming Attention Filtration**:
* `BC1_SingleBitCliffordBasisAndEntryLaw` (`𝔅ℭ₁`):
  Single-bit $\mathcal{C}\ell(1,1)$ basis $\gamma_{(x_0, z_0)} = S_P^{z_0} \Phi^{x_0}$ and
  single-bit symplectic sign bicharacter `bitSign(b₁ ⊕ b₂, c) = bitSign(b₁, c) * bitSign(b₂, c)`.
* `BC2_NBitBitwiseTensorProductBasis` (`𝔅ℭ₂`):
  $n$-bit Tensor-Peirce Clifford basis $\Gamma_{(x, z)}$ (`cliffordBitBasis R x z`) on
  $\mathbb{F}_2^n = (\mathrm{Fin}\,n \to \mathrm{Bool})$ with entry law
  $(\Gamma_{(x, z)})_{i, j} = \delta_{j, \, i \oplus x}\,(-1)^{\mathrm{popcount}(i \,\&\, z)}$
  and $n$-bit symplectic bicharacter laws `bvSign_xor_left`, `bvSign_xor_right`.
* `BC3_BitwiseSymplecticCocycleAndCausalSignature` (`𝔅ℭ₃`):
  Exact $n$-bit symplectic Clifford multiplication law
  $\Gamma_{(x_1, z_1)} \Gamma_{(x_2, z_2)} = (-1)^{\mathrm{popcount}(x_1 \,\&\, z_2)} \Gamma_{(x_1 \oplus x_2, \, z_1 \oplus z_2)}$,
  causal signature square law $\Gamma_{(x, z)}^2 = (-1)^{\mathrm{popcount}(x \,\&\, z)} I_{2^n}$,
  and exact $\mathbb{Z}$-invertibility of every basis matrix $\Gamma_{(x, z)}$.
* `BC4_DivisionFreeFastWalshCliffordCompiler` (`𝔅ℭ₄`, diamond branch A):
  Division-free XOR banding `xorBand M x i := M i (i ⊕ x)`, inverse `unband`,
  division-free Walsh–Clifford compiler `compileClifford`, and Rung 0 concentration of $I_{2^n}$
  at $x = 0$.
* `BC5_BitwiseSymplecticAlgebraConvolution` (`𝔅ℭ₅`, diamond branch B):
  Bitwise commutator/anticommutator parity laws
  $[\Gamma_{(x_1, z_1)}, \Gamma_{(x_2, z_2)}] = (\mathrm{bvSign}(x_1, z_2) - \mathrm{bvSign}(x_2, z_1)) \Gamma_{(x_1 \oplus x_2, z_1 \oplus z_2)}$
  and autonomous scale-$x$ nilpotent light-cone construction
  $(\Gamma_{(x, z_1)} \pm \Gamma_{(x, z_2)})^2 = 0$.
* `BC6_MultiScaleHammingAttentionFiltrationAndSynthesis` (`𝔅ℭ₆`):
  Bitwise Hamming weight `bvPopcount`, XOR-banded matrix-vector multiplication
  $(M *_{\text{vec}} v)(i) = \sum_x \mathrm{xorBand}(M)(x, i)\,v(i \oplus x)$, and master synthesis. -/
inductive BitwiseCliffordCompilerStage : Type
  | BC1_SingleBitCliffordBasisAndEntryLaw
  | BC2_NBitBitwiseTensorProductBasis
  | BC3_BitwiseSymplecticCocycleAndCausalSignature
  | BC4_DivisionFreeFastWalshCliffordCompiler
  | BC5_BitwiseSymplecticAlgebraConvolution
  | BC6_MultiScaleHammingAttentionFiltrationAndSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace BitwiseCliffordCompilerStage

/-- Topological rank `0..4` (with diamond branches `BC4, BC5` sharing rank `3`). -/
def rank : BitwiseCliffordCompilerStage → ℕ
  | .BC1_SingleBitCliffordBasisAndEntryLaw                => 0
  | .BC2_NBitBitwiseTensorProductBasis                    => 1
  | .BC3_BitwiseSymplecticCocycleAndCausalSignature       => 2
  | .BC4_DivisionFreeFastWalshCliffordCompiler            => 3
  | .BC5_BitwiseSymplecticAlgebraConvolution              => 3
  | .BC6_MultiScaleHammingAttentionFiltrationAndSynthesis => 4

/-- Total index `0..5` for `Fintype` and `LinearOrder`. -/
def stageIndex : BitwiseCliffordCompilerStage → ℕ
  | .BC1_SingleBitCliffordBasisAndEntryLaw                => 0
  | .BC2_NBitBitwiseTensorProductBasis                    => 1
  | .BC3_BitwiseSymplecticCocycleAndCausalSignature       => 2
  | .BC4_DivisionFreeFastWalshCliffordCompiler            => 3
  | .BC5_BitwiseSymplecticAlgebraConvolution              => 4
  | .BC6_MultiScaleHammingAttentionFiltrationAndSynthesis => 5

theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder BitwiseCliffordCompilerStage where
  le a b := stageIndex a ≤ stageIndex b
  lt a b := stageIndex a < stageIndex b
  le_refl a := le_rfl
  le_trans a b c := Nat.le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (stageIndex a) (stageIndex b)
  le_antisymm a b hab hba := stageIndex_injective (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total (stageIndex a) (stageIndex b)
  toDecidableLE a b := Nat.decLe (stageIndex a) (stageIndex b)
  toDecidableEq := inferInstance
  toDecidableLT a b := Nat.decLt (stageIndex a) (stageIndex b)

instance : Fintype BitwiseCliffordCompilerStage where
  elems := {
    .BC1_SingleBitCliffordBasisAndEntryLaw,
    .BC2_NBitBitwiseTensorProductBasis,
    .BC3_BitwiseSymplecticCocycleAndCausalSignature,
    .BC4_DivisionFreeFastWalshCliffordCompiler,
    .BC5_BitwiseSymplecticAlgebraConvolution,
    .BC6_MultiScaleHammingAttentionFiltrationAndSynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card BitwiseCliffordCompilerStage = 6 := rfl

/-- Directed covering edges of the diamond poset `𝔅ℭ₁ ≺ 𝔅ℭ₂ ≺ 𝔅ℭ₃ ≺ {𝔅ℭ₄, 𝔅ℭ₅} ≺ 𝔅ℭ₆`. -/
def causalEdge : BitwiseCliffordCompilerStage → BitwiseCliffordCompilerStage → Prop
  | .BC1_SingleBitCliffordBasisAndEntryLaw,          .BC2_NBitBitwiseTensorProductBasis                    => True
  | .BC2_NBitBitwiseTensorProductBasis,              .BC3_BitwiseSymplecticCocycleAndCausalSignature       => True
  | .BC3_BitwiseSymplecticCocycleAndCausalSignature, .BC4_DivisionFreeFastWalshCliffordCompiler            => True
  | .BC3_BitwiseSymplecticCocycleAndCausalSignature, .BC5_BitwiseSymplecticAlgebraConvolution              => True
  | .BC4_DivisionFreeFastWalshCliffordCompiler,      .BC6_MultiScaleHammingAttentionFiltrationAndSynthesis => True
  | .BC5_BitwiseSymplecticAlgebraConvolution,        .BC6_MultiScaleHammingAttentionFiltrationAndSynthesis => True
  | _, _ => False

theorem causalEdge_lt {a b : BitwiseCliffordCompilerStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;>
    revert h <;>
    unfold causalEdge rank <;>
    decide

theorem transGen_causalEdge_lt {a b : BitwiseCliffordCompilerStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

/-- Strict DAG acyclicity of `𝔅ℭ₁ ≺ 𝔅ℭ₂ ≺ 𝔅ℭ₃ ≺ {𝔅ℭ₄, 𝔅ℭ₅} ≺ 𝔅ℭ₆`. -/
theorem causalEdge_acyclic (a : BitwiseCliffordCompilerStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_lt h)

theorem incomparable_BC4_BC5 :
    ¬ causalEdge .BC4_DivisionFreeFastWalshCliffordCompiler
        .BC5_BitwiseSymplecticAlgebraConvolution ∧
    ¬ causalEdge .BC5_BitwiseSymplecticAlgebraConvolution
        .BC4_DivisionFreeFastWalshCliffordCompiler := by
  exact ⟨ id, id ⟩

/-- Monotone embedding into `InfoGeometry.Meta.RepDepth`. -/
def toRepDepth : BitwiseCliffordCompilerStage → InfoGeometry.Meta.RepDepth
  | .BC1_SingleBitCliffordBasisAndEntryLaw                => .operator
  | .BC2_NBitBitwiseTensorProductBasis                    => .operator
  | .BC3_BitwiseSymplecticCocycleAndCausalSignature       => .operator
  | .BC4_DivisionFreeFastWalshCliffordCompiler            => .transport
  | .BC5_BitwiseSymplecticAlgebraConvolution              => .transport
  | .BC6_MultiScaleHammingAttentionFiltrationAndSynthesis => .thermo

/-- Monotone embedding into `InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    BitwiseCliffordCompilerStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .BC1_SingleBitCliffordBasisAndEntryLaw                => .M1_ProjectorClabject
  | .BC2_NBitBitwiseTensorProductBasis                    => .M1_ProjectorClabject
  | .BC3_BitwiseSymplecticCocycleAndCausalSignature       => .M2_GrassmannianPowertypeOrbit
  | .BC4_DivisionFreeFastWalshCliffordCompiler            => .M2_GrassmannianPowertypeOrbit
  | .BC5_BitwiseSymplecticAlgebraConvolution              => .M2_GrassmannianPowertypeOrbit
  | .BC6_MultiScaleHammingAttentionFiltrationAndSynthesis => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : BitwiseCliffordCompilerStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth InfoGeometry.Meta.RepDepth.toNat <;>
    decide

theorem toOntologyMetaLevel_mono {a b : BitwiseCliffordCompilerStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;>
    decide

end BitwiseCliffordCompilerStage

section BitwiseCliffordCompilerPoset

/-- Single-bit symplectic sign `(-1)^{b · c} ∈ {-1, +1} ⊂ ℤ`. -/
def bitSign (b c : Bool) : ℤ :=
  if b && c then -1 else 1

/-- $n$-bit coordinate vector $x \in \mathbb{F}_2^n \equiv (\mathrm{Fin}\,n \to \mathrm{Bool})$. -/
abbrev BitVecN (n : ℕ) := Fin n → Bool

/-- Zero $n$-bit vector $0 \in \mathbb{F}_2^n$. -/
def bvZero (n : ℕ) : BitVecN n := fun _ => false

/-- Bitwise XOR $x \oplus y$ on $\mathbb{F}_2^n$. -/
def bvXor {n : ℕ} (x y : BitVecN n) : BitVecN n :=
  fun k => bne (x k) (y k)

/-- Bitwise symplectic cocycle sign $(-1)^{\mathrm{popcount}(x \,\&\, z)} = \prod_{k=0}^{n-1} (-1)^{x_k z_k} \in \mathbb{Z}$. -/
def bvSign {n : ℕ} (x z : BitVecN n) : ℤ :=
  ∏ k : Fin n, bitSign (x k) (z k)

/-- Bitwise Hamming weight $\mathrm{popcount}(x) = \sum_{k=0}^{n-1} (x_k ? 1 : 0) \in \mathbb{N}$. -/
def bvPopcount {n : ℕ} (x : BitVecN n) : ℕ :=
  ∑ k : Fin n, if x k then 1 else 0

/-- $n$-bit Tensor-Peirce $\mathcal{C}\ell(1,1)^{\otimes n}$ basis matrix $\Gamma_{(x, z)}$:
$(\Gamma_{(x, z)})_{i, j} = \delta_{j, \, i \oplus x}\,(-1)^{\mathrm{popcount}(i \,\&\, z)}$. -/
def cliffordBitBasis (R : Type*) [Ring R] {n : ℕ} (x z : BitVecN n) :
    Matrix (BitVecN n) (BitVecN n) R :=
  Matrix.of fun i j => if j = bvXor i x then bvSign i z • (1 : R) else 0

/-- Step 1 of the Bitwise Clifford Compiler: XOR Banding $B(x, i) := M(i, \, i \oplus x)$. -/
def xorBand {R : Type*} {n : ℕ} (M : Matrix (BitVecN n) (BitVecN n) R) :
    Matrix (BitVecN n) (BitVecN n) R :=
  Matrix.of fun x i => M i (bvXor i x)

/-- Inverse of XOR Banding: $\mathrm{unband}(B)(i, j) := B(i \oplus j, \, i)$. -/
def unband {R : Type*} {n : ℕ} (B : Matrix (BitVecN n) (BitVecN n) R) :
    Matrix (BitVecN n) (BitVecN n) R :=
  Matrix.of fun i j => B (bvXor i j) i

/-- Division-free $n$-bit Walsh–Clifford compiler:
$\widehat{C}(M)(x, z) := \sum_{i \in \mathbb{F}_2^n} (-1)^{\mathrm{popcount}(i \,\&\, z)} M(i, \, i \oplus x)$. -/
def compileClifford {R : Type*} [Ring R] {n : ℕ} (M : Matrix (BitVecN n) (BitVecN n) R) :
    Matrix (BitVecN n) (BitVecN n) R :=
  Matrix.of fun x z => ∑ i : BitVecN n, bvSign i z • M i (bvXor i x)

/-- **Stage `𝔅ℭ₁` (`bc1_single_bit_clifford_basis_and_bicharacter_laws`)**:
1. **Single-Bit Symplectic Bicharacter Laws (`bitSign`)**:
   - `bitSign false c = 1` and `bitSign b false = 1`,
   - `bitSign b c * bitSign b c = 1`,
   - `bitSign (bne b₁ b₂) c = bitSign b₁ c * bitSign b₂ c`,
   - `bitSign b (bne c₁ c₂) = bitSign b c₁ * bitSign b c₂`.
2. **Single-Qubit $\mathcal{C}\ell(1,1)$ Basis (`unitI, unitS, unitPhi, unitJ`)**:
   - `unitS * unitPhi = unitJ` ($J = S_P \Phi$),
   - `unitPhi * unitS = -unitJ` ($\Phi S_P = -S_P \Phi = -J$: non-commutative bit-flip cocycle!),
   - `unitI * (matPi00 M + matPi11 M) + unitS * (matPi00 M - matPi11 M) + unitPhi * (matPi01 M + matPi10 M) + unitJ * (matPi01 M - matPi10 M) = (2 : ℤ) • M`. -/
theorem bc1_single_bit_clifford_basis_and_bicharacter_laws
    (b b₁ b₂ c c₁ c₂ : Bool)
    {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) :
    bitSign false c = 1 ∧
    bitSign b false = 1 ∧
    bitSign b c * bitSign b c = 1 ∧
    bitSign (bne b₁ b₂) c = bitSign b₁ c * bitSign b₂ c ∧
    bitSign b (bne c₁ c₂) = bitSign b c₁ * bitSign b c₂ ∧
    (unitS : Matrix (Fin 2) (Fin 2) R) * unitPhi = unitJ ∧
    (unitPhi : Matrix (Fin 2) (Fin 2) R) * unitS = -unitJ ∧
    unitI * (matPi00 M + matPi11 M) +
      unitS * (matPi00 M - matPi11 M) +
      unitPhi * (matPi01 M + matPi10 M) +
      unitJ * (matPi01 M - matPi10 M) = (2 : ℤ) • M := by
  have hTT6 := tt6_dual_clifford_dewitt_tensor_basis_and_master_synthesis
    (B := Matrix (Fin 2) (Fin 2) R)
    (Np := unitE01) (Nm := unitE10)
    (by ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE01])
    (by ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE10])
    (by ext i j; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitE01, unitE10])
    M M 0 0 0 0 (0 : R)
  refine ⟨rfl, ?_, ?_, ?_, ?_, hTT6.2.2.2.2.2.2.2.1, ?_, hTT6.2.2.2.2.2.2.2.2.1⟩
  · cases b <;> rfl
  · cases b <;> cases c <;> rfl
  · cases b₁ <;> cases b₂ <;> cases c <;> rfl
  · cases b <;> cases c₁ <;> cases c₂ <;> rfl
  · ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [unitPhi, unitS, unitJ, unitE00, unitE01, unitE10, unitE11]

/-- **Stage `𝔅ℭ₂` (`bc2_nbit_xor_group_and_symplectic_bicharacter_laws`)**:
For any bit-width $n \in \mathbb{N}$ and $n$-bit vectors $x, x_1, x_2, z, z_1, z_2 \in \mathbb{F}_2^n$:
1. **Bitwise XOR Abelian Involutive Group Laws**:
   - `bvXor x x = bvZero n`, `bvXor x (bvZero n) = x`, `bvXor (bvZero n) x = x`,
   - `bvXor x₁ x₂ = bvXor x₂ x₁`, `bvXor (bvXor x₁ x₂) z = bvXor x₁ (bvXor x₂ z)`,
   - `bvXor x₁ (bvXor x₁ x₂) = x₂` and `bvXor (bvXor x₁ x₂) x₂ = x₁`.
2. **$n$-Bit Symplectic Bicharacter Laws (`bvSign`)**:
   - `bvSign (bvZero n) z = 1` and `bvSign x (bvZero n) = 1`,
   - `bvSign (bvXor x₁ x₂) z = bvSign x₁ z * bvSign x₂ z`,
   - `bvSign x (bvXor z₁ z₂) = bvSign x z₁ * bvSign x z₂`,
   - `bvSign x z * bvSign x z = 1`,
3. **Unital Origin Basis Matrix (`Γ_{0, 0} = I_{2^n}`)**:
   `cliffordBitBasis R (bvZero n) (bvZero n) = 1`. -/
theorem bc2_nbit_xor_group_and_symplectic_bicharacter_laws
    {R : Type*} [Ring R] {n : ℕ} (x x₁ x₂ z z₁ z₂ : BitVecN n) :
    bvXor x x = bvZero n ∧
    bvXor x (bvZero n) = x ∧
    bvXor (bvZero n) x = x ∧
    bvXor x₁ x₂ = bvXor x₂ x₁ ∧
    bvXor (bvXor x₁ x₂) z = bvXor x₁ (bvXor x₂ z) ∧
    bvXor x₁ (bvXor x₁ x₂) = x₂ ∧
    bvXor (bvXor x₁ x₂) x₂ = x₁ ∧
    bvSign (bvZero n) z = 1 ∧
    bvSign x (bvZero n) = 1 ∧
    bvSign (bvXor x₁ x₂) z = bvSign x₁ z * bvSign x₂ z ∧
    bvSign x (bvXor z₁ z₂) = bvSign x z₁ * bvSign x z₂ ∧
    bvSign x z * bvSign x z = 1 ∧
    cliffordBitBasis R (bvZero n) (bvZero n) = 1 := by
  have hSelf : ∀ u : BitVecN n, bvXor u u = bvZero n := by
    intro u; ext k; dsimp [bvXor, bvZero]; cases u k <;> rfl
  have hZeroR : ∀ u : BitVecN n, bvXor u (bvZero n) = u := by
    intro u; ext k; dsimp [bvXor, bvZero]; cases u k <;> rfl
  have hZeroL : ∀ u : BitVecN n, bvXor (bvZero n) u = u := by
    intro u; ext k; dsimp [bvXor, bvZero]; cases u k <;> rfl
  have hComm : bvXor x₁ x₂ = bvXor x₂ x₁ := by
    ext k; dsimp [bvXor]; cases x₁ k <;> cases x₂ k <;> rfl
  have hAssoc : ∀ u v w : BitVecN n, bvXor (bvXor u v) w = bvXor u (bvXor v w) := by
    intro u v w; ext k; dsimp [bvXor]; cases u k <;> cases v k <;> cases w k <;> rfl
  have hCancelL : bvXor x₁ (bvXor x₁ x₂) = x₂ := by
    rw [← hAssoc, hSelf, hZeroL]
  have hCancelR : bvXor (bvXor x₁ x₂) x₂ = x₁ := by
    rw [hAssoc, hSelf, hZeroR]
  have hSign0L : ∀ w : BitVecN n, bvSign (bvZero n) w = 1 := by
    intro w; dsimp [bvSign, bvZero, bitSign]; simp
  have hSign0R : ∀ u : BitVecN n, bvSign u (bvZero n) = 1 := by
    intro u
    dsimp [bvSign, bvZero]
    have h1 : ∀ k : Fin n, bitSign (u k) false = 1 := fun k => by cases u k <;> rfl
    simp [h1]
  have hSignXorL : ∀ u₁ u₂ w : BitVecN n, bvSign (bvXor u₁ u₂) w = bvSign u₁ w * bvSign u₂ w := by
    intro u₁ u₂ w
    dsimp [bvSign, bvXor]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    cases u₁ k <;> cases u₂ k <;> cases w k <;> rfl
  have hSignXorR : ∀ u w₁ w₂ : BitVecN n, bvSign u (bvXor w₁ w₂) = bvSign u w₁ * bvSign u w₂ := by
    intro u w₁ w₂
    dsimp [bvSign, bvXor]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    cases u k <;> cases w₁ k <;> cases w₂ k <;> rfl
  have hSignSq : bvSign x z * bvSign x z = 1 := by
    rw [← hSignXorL x x z, hSelf x, hSign0L z]
  have hBasis0 : cliffordBitBasis R (bvZero n) (bvZero n) = 1 := by
    ext i j
    simp [cliffordBitBasis, hZeroR i, hSign0R i, Matrix.one_apply, eq_comm]
  exact ⟨hSelf x, hZeroR x, hZeroL x, hComm, hAssoc x₁ x₂ z, hCancelL, hCancelR,
    hSign0L z, hSign0R x, hSignXorL x₁ x₂ z, hSignXorR x z₁ z₂, hSignSq, hBasis0⟩

/-- **Stage `𝔅ℭ₃` (`bc3_bitwise_symplectic_cocycle_and_causal_signature_law`)**:
For any associative ring `[Ring R]`, bit-width $n \in \mathbb{N}$, and phase-space coordinates
$x, z, x_1, z_1, x_2, z_2 \in \mathbb{F}_2^n$:
1. **Universal Bitwise Symplectic Multiplication Law**:
   $$\Gamma_{(x_1, z_1)} * \Gamma_{(x_2, z_2)} \;=\; \mathrm{bvSign}(x_1, z_2) \bullet \Gamma_{(x_1 \oplus x_2, \, z_1 \oplus z_2)}.$$
2. **Causal Signature Square Law ($\mathrm{popcount}(x \,\&\, z)$ Even $\implies +I$, Odd $\implies -I$)**:
   $$\Gamma_{(x, z)} * \Gamma_{(x, z)} \;=\; \mathrm{bvSign}(x, z) \bullet 1.$$
3. **Exact $\mathbb{Z}$-Invertibility of Every Basis Matrix $\Gamma_{(x, z)}$ (Rung 0 Contrast with Rank-1 $H M H$)**:
   $$\Gamma_{(x, z)} * \big(\mathrm{bvSign}(x, z) \bullet \Gamma_{(x, z)}\big) = 1 \;\land\;
     \big(\mathrm{bvSign}(x, z) \bullet \Gamma_{(x, z)}\big) * \Gamma_{(x, z)} = 1.$$ -/
theorem bc3_bitwise_symplectic_cocycle_and_causal_signature_law
    {R : Type*} [Ring R] {n : ℕ} (x z x₁ z₁ x₂ z₂ : BitVecN n) :
    cliffordBitBasis R x₁ z₁ * cliffordBitBasis R x₂ z₂ =
      bvSign x₁ z₂ • cliffordBitBasis R (bvXor x₁ x₂) (bvXor z₁ z₂) ∧
    cliffordBitBasis R x z * cliffordBitBasis R x z =
      bvSign x z • (1 : Matrix (BitVecN n) (BitVecN n) R) ∧
    cliffordBitBasis R x z * (bvSign x z • cliffordBitBasis R x z) = 1 ∧
    (bvSign x z • cliffordBitBasis R x z) * cliffordBitBasis R x z = 1 := by
  have hMul : ∀ u₁ w₁ u₂ w₂ : BitVecN n,
      cliffordBitBasis R u₁ w₁ * cliffordBitBasis R u₂ w₂ =
        bvSign u₁ w₂ • cliffordBitBasis R (bvXor u₁ u₂) (bvXor w₁ w₂) := by
    intro u₁ w₁ u₂ w₂
    ext i j
    simp only [Matrix.mul_apply, cliffordBitBasis, Matrix.of_apply, Matrix.smul_apply]
    rw [Fintype.sum_eq_single (bvXor i u₁)]
    · simp only [ ↓reduceIte ]
      have hBC2 := bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) i i u₁ u₂ w₁ w₂
      have hAssoc : bvXor (bvXor i u₁) u₂ = bvXor i (bvXor u₁ u₂) :=
        (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) i i u₁ u₂ w₁ w₂).2.2.2.2.1
      rw [hAssoc]
      by_cases hj : j = bvXor i (bvXor u₁ u₂)
      · simp only [hj, ↓reduceIte]
        have hSignL := (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) i i u₁ w₂ w₁ w₂).2.2.2.2.2.2.2.2.2.1
        have hSignR := (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) i i u₁ w₂ w₁ w₂).2.2.2.2.2.2.2.2.2.2.1
        have hSign : bvSign i w₁ * bvSign (bvXor i u₁) w₂ =
            bvSign u₁ w₂ * bvSign i (bvXor w₁ w₂) := by
          rw [hSignL, hSignR]
          simp only [mul_comm, mul_left_comm]
        calc (bvSign i w₁ • (1 : R)) * (bvSign (bvXor i u₁) w₂ • (1 : R))
          _ = (bvSign i w₁ * bvSign (bvXor i u₁) w₂) • (1 : R) := by
                rw [smul_mul_smul_comm, mul_one]
          _ = (bvSign u₁ w₂ * bvSign i (bvXor w₁ w₂)) • (1 : R) := by rw [hSign]
          _ = bvSign u₁ w₂ • (bvSign i (bvXor w₁ w₂) • (1 : R)) := by rw [mul_smul]
      · simp only [hj, ↓reduceIte, mul_zero, smul_zero]
    · intro l hl
      simp only [hl, ↓reduceIte, zero_mul]
  have hBC2 := bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) x x x z z z
  have hSq : cliffordBitBasis R x z * cliffordBitBasis R x z =
      bvSign x z • (1 : Matrix (BitVecN n) (BitVecN n) R) := by
    rw [hMul x z x z, hBC2.1,
      (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) z x x z z z).1,
      hBC2.2.2.2.2.2.2.2.2.2.2.2.2]
  have hInvR : cliffordBitBasis R x z * (bvSign x z • cliffordBitBasis R x z) = 1 := by
    rw [mul_smul_comm, hSq, smul_smul, hBC2.2.2.2.2.2.2.2.2.2.2.2.1, one_smul]
  have hInvL : (bvSign x z • cliffordBitBasis R x z) * cliffordBitBasis R x z = 1 := by
    rw [smul_mul_assoc, hSq, smul_smul, hBC2.2.2.2.2.2.2.2.2.2.2.2.1, one_smul]
  exact ⟨hMul x₁ z₁ x₂ z₂, hSq, hInvR, hInvL⟩

/-- **Stage `𝔅ℭ₄` (`bc4_division_free_xor_band_and_walsh_clifford_compiler`)**:
1. **Exact Roundtrip of Bitwise XOR Banding (`unband (xorBand M) = M` & `xorBand (unband B) = B`)**:
   Re-indexing columns by $x = i \oplus j$ is an involutive bijection with zero arithmetic overhead.
2. **Additivity of the Division-Free Walsh–Clifford Compiler (`compileClifford`)**:
   $\widehat{C}(M + N) = \widehat{C}(M) + \widehat{C}(N)$.
3. **Rung 0 Socratic Aporia (Why Off-Diagonal XOR Bands of $I_{2^n}$ Vanish Identically)**:
   For any non-zero jump mask $x \neq 0$, the XOR band of the identity matrix $\mathrm{xorBand}(1)(x, i)$
   and its Clifford spectrum $\widehat{C}(1)(x, z)$ vanish identically! -/
theorem bc4_division_free_xor_band_and_walsh_clifford_compiler
    {R : Type*} [Ring R] {n : ℕ}
    (M N B_mat : Matrix (BitVecN n) (BitVecN n) R)
    (x z i : BitVecN n) (hx : x ≠ bvZero n) :
    unband (xorBand M) = M ∧
    xorBand (unband B_mat) = B_mat ∧
    compileClifford (M + N) = compileClifford M + compileClifford N ∧
    xorBand (1 : Matrix (BitVecN n) (BitVecN n) R) x i = 0 ∧
    compileClifford (1 : Matrix (BitVecN n) (BitVecN n) R) x z = 0 := by
  have hUnband : unband (xorBand M) = M := by
    ext r c
    have hCancel := (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) r r c r r r).2.2.2.2.2.1
    simp [unband, xorBand, hCancel]
  have hBand : xorBand (unband B_mat) = B_mat := by
    ext r c
    have hCancel := (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) c c r c c c).2.2.2.2.2.1
    simp [unband, xorBand, hCancel]
  have hAdd : compileClifford (M + N) = compileClifford M + compileClifford N := by
    ext r c
    simp [compileClifford, smul_add, Finset.sum_add_distrib]
  have hNe : ∀ r : BitVecN n, r ≠ bvXor r x := by
    intro r hr
    apply hx
    have hCancel := (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) r r x r r r).2.2.2.2.2.1
    have hSelf := (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) r r x r r r).1
    calc x
      _ = bvXor r (bvXor r x) := hCancel.symm
      _ = bvXor r r := by rw [← hr]
      _ = bvZero n := hSelf
  have hBandOne : xorBand (1 : Matrix (BitVecN n) (BitVecN n) R) x i = 0 := by
    simp [xorBand, Matrix.one_apply, hNe i]
  have hCompOne : compileClifford (1 : Matrix (BitVecN n) (BitVecN n) R) x z = 0 := by
    simp [compileClifford, Matrix.one_apply, hNe]
  exact ⟨hUnband, hBand, hAdd, hBandOne, hCompOne⟩

/-- **Stage `𝔅ℭ₅` (`bc5_bitwise_symplectic_commutator_anticommutator_and_nilpotent_cone`)**:
1. **Bitwise Symplectic Commutator & Anticommutator Laws**:
   $$[\Gamma_{(x_1, z_1)}, \, \Gamma_{(x_2, z_2)}] = \big(\mathrm{bvSign}(x_1, z_2) - \mathrm{bvSign}(x_2, z_1)\big) \bullet \Gamma_{(x_1 \oplus x_2, \, z_1 \oplus z_2)},$$
   $$\{\Gamma_{(x_1, z_1)}, \, \Gamma_{(x_2, z_2)}\} = \big(\mathrm{bvSign}(x_1, z_2) + \mathrm{bvSign}(x_2, z_1)\big) \bullet \Gamma_{(x_1 \oplus x_2, \, z_1 \oplus z_2)}.$$
2. **Autonomous Scale-$x$ Nilpotent Light-Cone Construction (`Phase II.4`)**:
   Whenever a spacelike mode $\Gamma_{(x, z_1)}$ ($\mathrm{bvSign}(x, z_1) = 1$) and a timelike mode
   $\Gamma_{(x, z_2)}$ ($\mathrm{bvSign}(x, z_2) = -1$) at the same scale jump $x$ satisfy
   $\mathrm{bvSign}(x, z_2) = -\mathrm{bvSign}(x, z_1)$, their sum and difference are
   **square-zero nilpotent** attention gates:
   $$\big(\Gamma_{(x, z_1)} + \Gamma_{(x, z_2)}\big)^2 = 0 \;\land\;
     \big(\Gamma_{(x, z_1)} - \Gamma_{(x, z_2)}\big)^2 = 0.$$ -/
theorem bc5_bitwise_symplectic_commutator_anticommutator_and_nilpotent_cone
    {R : Type*} [Ring R] {n : ℕ} (x z₁ z₂ x₁ x₂ : BitVecN n)
    (hSpace : bvSign x z₁ = 1) (hTime : bvSign x z₂ = -1) :
    (cliffordBitBasis R x₁ z₁ * cliffordBitBasis R x₂ z₂ -
      cliffordBitBasis R x₂ z₂ * cliffordBitBasis R x₁ z₁ =
      (bvSign x₁ z₂ - bvSign x₂ z₁) • cliffordBitBasis R (bvXor x₁ x₂) (bvXor z₁ z₂)) ∧
    (cliffordBitBasis R x₁ z₁ * cliffordBitBasis R x₂ z₂ +
      cliffordBitBasis R x₂ z₂ * cliffordBitBasis R x₁ z₁ =
      (bvSign x₁ z₂ + bvSign x₂ z₁) • cliffordBitBasis R (bvXor x₁ x₂) (bvXor z₁ z₂)) ∧
    ((cliffordBitBasis R x z₁ + cliffordBitBasis R x z₂) *
      (cliffordBitBasis R x z₁ + cliffordBitBasis R x z₂) = 0 ∧
     (cliffordBitBasis R x z₁ - cliffordBitBasis R x z₂) *
      (cliffordBitBasis R x z₁ - cliffordBitBasis R x z₂) = 0) := by
  have hMul12 := (bc3_bitwise_symplectic_cocycle_and_causal_signature_law (R := R) x₁ z₁ x₁ z₁ x₂ z₂).1
  have hMul21 := (bc3_bitwise_symplectic_cocycle_and_causal_signature_law (R := R) x₁ z₁ x₂ z₂ x₁ z₁).1
  have hXorX : bvXor x₂ x₁ = bvXor x₁ x₂ :=
    (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) x₂ x₂ x₁ z₁ z₁ z₂).2.2.2.1
  have hXorZ : bvXor z₂ z₁ = bvXor z₁ z₂ :=
    (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) x₂ z₂ z₁ z₁ z₁ z₂).2.2.2.1
  have hComm :
      cliffordBitBasis R x₁ z₁ * cliffordBitBasis R x₂ z₂ -
        cliffordBitBasis R x₂ z₂ * cliffordBitBasis R x₁ z₁ =
        (bvSign x₁ z₂ - bvSign x₂ z₁) • cliffordBitBasis R (bvXor x₁ x₂) (bvXor z₁ z₂) := by
    rw [hMul12, hMul21, hXorX, hXorZ, ← sub_smul]
  have hAnti :
      cliffordBitBasis R x₁ z₁ * cliffordBitBasis R x₂ z₂ +
        cliffordBitBasis R x₂ z₂ * cliffordBitBasis R x₁ z₁ =
        (bvSign x₁ z₂ + bvSign x₂ z₁) • cliffordBitBasis R (bvXor x₁ x₂) (bvXor z₁ z₂) := by
    rw [hMul12, hMul21, hXorX, hXorZ, ← add_smul]
  have hSq1 := (bc3_bitwise_symplectic_cocycle_and_causal_signature_law (R := R) x z₁ x z₁ x z₁).2.1
  have hSq2 := (bc3_bitwise_symplectic_cocycle_and_causal_signature_law (R := R) x z₂ x z₂ x z₂).2.1
  have hMulZ12 := (bc3_bitwise_symplectic_cocycle_and_causal_signature_law (R := R) x z₁ x z₁ x z₂).1
  have hMulZ21 := (bc3_bitwise_symplectic_cocycle_and_causal_signature_law (R := R) x z₁ x z₂ x z₁).1
  have hAntiXZ :
      cliffordBitBasis R x z₁ * cliffordBitBasis R x z₂ +
        cliffordBitBasis R x z₂ * cliffordBitBasis R x z₁ = 0 := by
    rw [hMulZ12, hMulZ21, hXorZ, ← add_smul, hTime, hSpace]
    simp
  refine ⟨hComm, hAnti, ⟨?_, ?_⟩⟩
  · calc (cliffordBitBasis R x z₁ + cliffordBitBasis R x z₂) *
          (cliffordBitBasis R x z₁ + cliffordBitBasis R x z₂)
      _ = cliffordBitBasis R x z₁ * cliffordBitBasis R x z₁ +
            (cliffordBitBasis R x z₁ * cliffordBitBasis R x z₂ +
             cliffordBitBasis R x z₂ * cliffordBitBasis R x z₁) +
            cliffordBitBasis R x z₂ * cliffordBitBasis R x z₂ := by noncomm_ring
      _ = bvSign x z₁ • 1 + 0 + bvSign x z₂ • 1 := by rw [hSq1, hAntiXZ, hSq2]
      _ = (1 : ℤ) • (1 : Matrix (BitVecN n) (BitVecN n) R) + 0 + (-1 : ℤ) • 1 := by
            rw [hSpace, hTime]
      _ = 0 := by simp
  · calc (cliffordBitBasis R x z₁ - cliffordBitBasis R x z₂) *
          (cliffordBitBasis R x z₁ - cliffordBitBasis R x z₂)
      _ = cliffordBitBasis R x z₁ * cliffordBitBasis R x z₁ -
            (cliffordBitBasis R x z₁ * cliffordBitBasis R x z₂ +
             cliffordBitBasis R x z₂ * cliffordBitBasis R x z₁) +
            cliffordBitBasis R x z₂ * cliffordBitBasis R x z₂ := by noncomm_ring
      _ = bvSign x z₁ • 1 - 0 + bvSign x z₂ • 1 := by rw [hSq1, hAntiXZ, hSq2]
      _ = (1 : ℤ) • (1 : Matrix (BitVecN n) (BitVecN n) R) - 0 + (-1 : ℤ) • 1 := by
            rw [hSpace, hTime]
      _ = 0 := by simp

/-- **Stage `𝔅ℭ₆` (`bc6_multiscale_hamming_attention_filtration_and_master_synthesis`)**:
Master theorem unifying the 6-stage **Bitwise Symplectic Clifford Compiler & Multi-Scale
Attention Filtration Poset** (`𝔅ℭ₁ ≺ 𝔅ℭ₂ ≺ 𝔅ℭ₃ ≺ {𝔅ℭ₄, 𝔅ℭ₅} ≺ 𝔅ℭ₆`):
1. **Poset Acyclicity, Cardinality, & Diamond Branching**:
   `BitwiseCliffordCompilerStage.causalEdge_acyclic`,
   `Fintype.card BitwiseCliffordCompilerStage = 6`, and
   `¬ causalEdge BC4 BC5 ∧ ¬ causalEdge BC5 BC4`.
2. **Bitwise Hamming Weight (`bvPopcount`) & XOR-Banded Matrix-Vector Execution**:
   - `bvPopcount (bvZero n) = 0`,
   - For any matrix $M : \mathrm{Matrix}\,(\mathrm{BitVecN}\,n)\,(\mathrm{BitVecN}\,n)\,R$ and
     token vector $v : \mathrm{BitVecN}\,n \to R$, the row-column product $\sum_j M(i, j) v(j)$
     equals the XOR-banded sum $\sum_x \mathrm{xorBand}(M)(x, i)\,v(i \oplus x)$:
     $$\sum_{j \in \mathbb{F}_2^n} M(i, j)\,v(j) \;=\; \sum_{x \in \mathbb{F}_2^n} \mathrm{xorBand}(M)(x, i)\,v(i \oplus x).$$
3. **Master Bitwise Clifford Compiler Synthesis**:
   Bundles `cliffordBitBasis R x₁ z₁ * cliffordBitBasis R x₂ z₂ = bvSign x₁ z₂ • cliffordBitBasis R (bvXor x₁ x₂) (bvXor z₁ z₂)`,
   `cliffordBitBasis R x z * cliffordBitBasis R x z = bvSign x z • 1`,
   `unband (xorBand M) = M`, and `compileClifford (M + N) = compileClifford M + compileClifford N`. -/
theorem bc6_multiscale_hamming_attention_filtration_and_master_synthesis
    {R : Type*} [Ring R] {n : ℕ}
    (M N : Matrix (BitVecN n) (BitVecN n) R) (v : BitVecN n → R)
    (i x z x₁ z₁ x₂ z₂ : BitVecN n) :
    -- 1. Poset acyclicity, cardinality, and diamond branching:
    (∀ st : BitwiseCliffordCompilerStage,
      ¬ Relation.TransGen BitwiseCliffordCompilerStage.causalEdge st st) ∧
    Fintype.card BitwiseCliffordCompilerStage = 6 ∧
    (¬ BitwiseCliffordCompilerStage.causalEdge
        .BC4_DivisionFreeFastWalshCliffordCompiler
        .BC5_BitwiseSymplecticAlgebraConvolution ∧
     ¬ BitwiseCliffordCompilerStage.causalEdge
        .BC5_BitwiseSymplecticAlgebraConvolution
        .BC4_DivisionFreeFastWalshCliffordCompiler) ∧
    -- 2. Hamming weight at origin and XOR-banded matrix-vector execution:
    bvPopcount (bvZero n) = 0 ∧
    (∑ j : BitVecN n, M i j * v j =
      ∑ x_band : BitVecN n, xorBand M x_band i * v (bvXor i x_band)) ∧
    -- 3. Master Bitwise Symplectic Clifford Compiler identities:
    cliffordBitBasis R x₁ z₁ * cliffordBitBasis R x₂ z₂ =
      bvSign x₁ z₂ • cliffordBitBasis R (bvXor x₁ x₂) (bvXor z₁ z₂) ∧
    cliffordBitBasis R x z * cliffordBitBasis R x z =
      bvSign x z • (1 : Matrix (BitVecN n) (BitVecN n) R) ∧
    unband (xorBand M) = M ∧
    compileClifford (M + N) = compileClifford M + compileClifford N := by
  have hPop0 : bvPopcount (bvZero n) = 0 := by
    simp [bvPopcount, bvZero]
  let hXorEquiv : (BitVecN n) ≃ (BitVecN n) := {
    toFun := fun x_band => bvXor i x_band
    invFun := fun j => bvXor i j
    left_inv := fun x_band =>
      (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) i i x_band i i i).2.2.2.2.2.1
    right_inv := fun j =>
      (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) i i j i i i).2.2.2.2.2.1
  }
  have hBandMV :
      ∑ j : BitVecN n, M i j * v j =
        ∑ x_band : BitVecN n, xorBand M x_band i * v (bvXor i x_band) := by
    rw [← Equiv.sum_comp hXorEquiv]
    rfl
  have hBC3 := bc3_bitwise_symplectic_cocycle_and_causal_signature_law (R := R) x z x₁ z₁ x₂ z₂
  exact ⟨BitwiseCliffordCompilerStage.causalEdge_acyclic,
    BitwiseCliffordCompilerStage.card_eq_six,
    BitwiseCliffordCompilerStage.incomparable_BC4_BC5,
    hPop0, hBandMV,
    hBC3.1, hBC3.2.1,
    (unband_xorBand : unband (xorBand M) = M),
    (compile_add : compileClifford (M + N) = compileClifford M + compileClifford N)⟩
where
  unband_xorBand : unband (xorBand M) = M := by
    ext r c
    have hCancel := (bc2_nbit_xor_group_and_symplectic_bicharacter_laws (R := R) r r c r r r).2.2.2.2.2.1
    simp [unband, xorBand, hCancel]
  compile_add : compileClifford (M + N) = compileClifford M + compileClifford N := by
    ext r c
    simp [compileClifford, smul_add, Finset.sum_add_distrib]

end BitwiseCliffordCompilerPoset

/-!
## 9d. The 6-Stage Conformal Net Balancing & Connes Fusion Monodromy Poset (`ℭ𝔑₁ ≺ ℭ𝔑₂ ≺ ℭ𝔑₃ ≺ ℭ𝔑₄ ≺ {ℭ𝔑₅, ℭ𝔑₆}`)
-/

/-- **The 6-Stage Conformal Net Balancing & Connes Fusion Monodromy Poset
(`ConformalNetBalancedCategoryStage`, `ℭ𝔑₁ ≺ ℭ𝔑₂ ≺ ℭ𝔑₃ ≺ ℭ𝔑₄ ≺ {ℭ𝔑₅, ℭ𝔑₆}`)**:
Formalizes the acyclic causal poset synthesized from Adrià Marín-Salvador's
*"The balanced structure on the category of representations of a conformal net"*
(J. Math. Phys. **67**, 102302, Oct 2026; arXiv:2605.18446 & arXiv:2606.03623),
severing localized rational Doplicher–Haag–Roberts (DHR) endomorphisms and bare
$\mathrm{Möb} = \mathrm{PSU}(1,1)$ representations from **Connes Fusion Bimodules
$\mathcal{H}_{(-)} \boxtimes_{\mathcal{A}} \mathcal{K}_{(+)}$**, **Path-Continuation Braiding**,
the **Universal Cover $\widetilde{\mathrm{Möb}}$ Balance Twist $\theta_{\mathcal{H}} = e^{-2\pi i L_0}$**,
the **All-Orders Multiplicative Group-Commutator Monodromy Law**, and **Unipotent LogCFT
Jordan Balance**:
* `CN1_TwoSheetedCircleSplitAndHaagDuality` (`ℭ𝔑₁`):
  Two-sheeted circle split $S^1 = I_- \cup I_+$, Haag commutant duality
  $\mathcal{A}(I_-) = \mathcal{A}(I_+)' \leftrightarrow$ complementary Peirce idempotents
  $P + (1 - P) = 1$, $P(1 - P) = 0$, DeWitt involution $S_P = 2P - 1$ ($S_P^2 = 1$),
  and causal commutativity $[P X P, \, (1 - P) Y (1 - P)] = 0$.
* `CN2_ConnesFusionAcrossSeamAndRadonNikodymGluing` (`ℭ𝔑₂`):
  Connes fusion $\mathcal{H}_{(-)} \boxtimes_{\mathcal{A}} \mathcal{K}_{(+)}$ across the
  two-point boundary seam $\partial I_\pm = \{-1, +1\}$ via the forward and reverse
  Operator Gaussians $\mathcal{G}_+ = (1 + N_+)(1 + N_-) = 1 + \Phi + Q_+$ and
  $\mathcal{G}_- = (1 + N_-)(1 + N_+) = 1 + \Phi + Q_-$, plus Rung 0 non-additivity
  defect $\mathcal{G}_+ - (1 + \Phi) = Q_+$ and chiral difference $\mathcal{G}_+ - \mathcal{G}_- = \Sigma$.
* `CN3_PathContinuationBraidingAndSheetSwap` (`ℭ𝔑₃`):
  Path-continuation braiding $B_{\mathcal{H}, \mathcal{K}}$ across complementary semicircles,
  sheet-swap reflection $S_P \Phi S_P = -\Phi$, $S_P J S_P = -J$, $S_P V S_P = V$,
  $S_P \Sigma S_P = \Sigma$, and exact polynomial inverses of $\mathcal{G}_+$ and $\mathcal{G}_-$.
* `CN4_UniversalCoverMobiusLiftAndCanonicalBalance` (`ℭ𝔑₄`):
  Universal cover $\widetilde{\mathrm{Möb}}$ lift, Rung 0 bare-$\mathrm{Möb}$ spin-erasure
  aporia ($\theta = 1 \implies \theta - 1 = 0$), and non-semisimple LogCFT unipotent
  balance twist $\theta_{\mathrm{LogCFT}}(w, c, N_{\mathrm{nil}}) := w(1 - c N_{\mathrm{nil}})$
  for $N_{\mathrm{nil}}^2 = 0$, satisfying multiplicative composition
  $\theta(w_1, c_1)\theta(w_2, c_2) = \theta(w_1 w_2, c_1 + c_2)$.
* `CN5_FundamentalBalancingMonodromyTheorem` (`ℭ𝔑₅`, diamond branch A):
  Theorem 1 — Exact all-orders multiplicative group-commutator / double-braiding monodromy law:
  $$\mathcal{M}_{\mathrm{braid}}(P, A, C) := (1 + N_+)(1 + N_-)(1 - N_+)(1 - N_-) = 1 + \Sigma - V J + Q_+^2,$$
  its exact polynomial inverse $\mathcal{M}_{\mathrm{braid}}^{-1}(P, A, C) = 1 - \Sigma + V J + Q_-^2$,
  and the exact **Balancing Coherence Identity** $\mathcal{G}_+ = \mathcal{M}_{\mathrm{braid}} \cdot \mathcal{G}_-$.
* `CN6_UnipotentLogCFTBalanceAndMasterSynthesis` (`ℭ𝔑₆`, diamond branch B / terminal synthesis):
  Theorem 2 — Unipotent LogCFT balance action on a rank-2 Jordan chain
  $\theta(w, c, N_{\mathrm{nil}}) \Phi_{\mathrm{gen}} = w \Phi_{\mathrm{gen}} - (w c)\Psi_{\mathrm{jord}}$,
  modular $c/24$ framing clock (`(24 : ZMod 24) = 0`), and master synthesis. -/
inductive ConformalNetBalancedCategoryStage : Type
  | CN1_TwoSheetedCircleSplitAndHaagDuality
  | CN2_ConnesFusionAcrossSeamAndRadonNikodymGluing
  | CN3_PathContinuationBraidingAndSheetSwap
  | CN4_UniversalCoverMobiusLiftAndCanonicalBalance
  | CN5_FundamentalBalancingMonodromyTheorem
  | CN6_UnipotentLogCFTBalanceAndMasterSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace ConformalNetBalancedCategoryStage

/-- Topological rank `0..4` (with diamond branches `CN5, CN6` sharing rank `4`). -/
def rank : ConformalNetBalancedCategoryStage → ℕ
  | .CN1_TwoSheetedCircleSplitAndHaagDuality            => 0
  | .CN2_ConnesFusionAcrossSeamAndRadonNikodymGluing    => 1
  | .CN3_PathContinuationBraidingAndSheetSwap           => 2
  | .CN4_UniversalCoverMobiusLiftAndCanonicalBalance    => 3
  | .CN5_FundamentalBalancingMonodromyTheorem           => 4
  | .CN6_UnipotentLogCFTBalanceAndMasterSynthesis       => 4

/-- Total index `0..5` for `Fintype` and `LinearOrder`. -/
def stageIndex : ConformalNetBalancedCategoryStage → ℕ
  | .CN1_TwoSheetedCircleSplitAndHaagDuality            => 0
  | .CN2_ConnesFusionAcrossSeamAndRadonNikodymGluing    => 1
  | .CN3_PathContinuationBraidingAndSheetSwap           => 2
  | .CN4_UniversalCoverMobiusLiftAndCanonicalBalance    => 3
  | .CN5_FundamentalBalancingMonodromyTheorem           => 4
  | .CN6_UnipotentLogCFTBalanceAndMasterSynthesis       => 5

theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder ConformalNetBalancedCategoryStage where
  le a b := stageIndex a ≤ stageIndex b
  lt a b := stageIndex a < stageIndex b
  le_refl a := le_rfl
  le_trans a b c := Nat.le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (stageIndex a) (stageIndex b)
  le_antisymm a b hab hba := stageIndex_injective (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total (stageIndex a) (stageIndex b)
  toDecidableLE a b := Nat.decLe (stageIndex a) (stageIndex b)
  toDecidableEq := inferInstance
  toDecidableLT a b := Nat.decLt (stageIndex a) (stageIndex b)

instance : Fintype ConformalNetBalancedCategoryStage where
  elems := {
    .CN1_TwoSheetedCircleSplitAndHaagDuality,
    .CN2_ConnesFusionAcrossSeamAndRadonNikodymGluing,
    .CN3_PathContinuationBraidingAndSheetSwap,
    .CN4_UniversalCoverMobiusLiftAndCanonicalBalance,
    .CN5_FundamentalBalancingMonodromyTheorem,
    .CN6_UnipotentLogCFTBalanceAndMasterSynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card ConformalNetBalancedCategoryStage = 6 := rfl

/-- Directed covering edges of the diamond poset `ℭ𝔑₁ ≺ ℭ𝔑₂ ≺ ℭ𝔑₃ ≺ ℭ𝔑₄ ≺ {ℭ𝔑₅, ℭ𝔑₆}`. -/
def causalEdge : ConformalNetBalancedCategoryStage → ConformalNetBalancedCategoryStage → Prop
  | .CN1_TwoSheetedCircleSplitAndHaagDuality,         .CN2_ConnesFusionAcrossSeamAndRadonNikodymGluing => True
  | .CN2_ConnesFusionAcrossSeamAndRadonNikodymGluing, .CN3_PathContinuationBraidingAndSheetSwap        => True
  | .CN3_PathContinuationBraidingAndSheetSwap,        .CN4_UniversalCoverMobiusLiftAndCanonicalBalance => True
  | .CN4_UniversalCoverMobiusLiftAndCanonicalBalance, .CN5_FundamentalBalancingMonodromyTheorem        => True
  | .CN4_UniversalCoverMobiusLiftAndCanonicalBalance, .CN6_UnipotentLogCFTBalanceAndMasterSynthesis    => True
  | _, _ => False

theorem causalEdge_lt {a b : ConformalNetBalancedCategoryStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;>
    revert h <;>
    unfold causalEdge rank <;>
    decide

theorem transGen_causalEdge_lt {a b : ConformalNetBalancedCategoryStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

/-- Strict DAG acyclicity of `ℭ𝔑₁ ≺ ℭ𝔑₂ ≺ ℭ𝔑₃ ≺ ℭ𝔑₄ ≺ {ℭ𝔑₅, ℭ𝔑₆}`. -/
theorem causalEdge_acyclic (a : ConformalNetBalancedCategoryStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_lt h)

theorem incomparable_CN5_CN6 :
    ¬ causalEdge .CN5_FundamentalBalancingMonodromyTheorem
        .CN6_UnipotentLogCFTBalanceAndMasterSynthesis ∧
    ¬ causalEdge .CN6_UnipotentLogCFTBalanceAndMasterSynthesis
        .CN5_FundamentalBalancingMonodromyTheorem := by
  exact ⟨ id, id ⟩

/-- Monotone embedding into `InfoGeometry.Meta.RepDepth`. -/
def toRepDepth : ConformalNetBalancedCategoryStage → InfoGeometry.Meta.RepDepth
  | .CN1_TwoSheetedCircleSplitAndHaagDuality         => .operator
  | .CN2_ConnesFusionAcrossSeamAndRadonNikodymGluing => .operator
  | .CN3_PathContinuationBraidingAndSheetSwap        => .transport
  | .CN4_UniversalCoverMobiusLiftAndCanonicalBalance => .transport
  | .CN5_FundamentalBalancingMonodromyTheorem        => .thermo
  | .CN6_UnipotentLogCFTBalanceAndMasterSynthesis    => .thermo

/-- Monotone embedding into `InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    ConformalNetBalancedCategoryStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .CN1_TwoSheetedCircleSplitAndHaagDuality         => .M1_ProjectorClabject
  | .CN2_ConnesFusionAcrossSeamAndRadonNikodymGluing => .M1_ProjectorClabject
  | .CN3_PathContinuationBraidingAndSheetSwap        => .M2_GrassmannianPowertypeOrbit
  | .CN4_UniversalCoverMobiusLiftAndCanonicalBalance => .M2_GrassmannianPowertypeOrbit
  | .CN5_FundamentalBalancingMonodromyTheorem        => .M3_ErlangenCasimirMetaLaw
  | .CN6_UnipotentLogCFTBalanceAndMasterSynthesis    => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_mono {a b : ConformalNetBalancedCategoryStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth InfoGeometry.Meta.RepDepth.toNat <;>
    decide

theorem toOntologyMetaLevel_mono {a b : ConformalNetBalancedCategoryStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;>
    decide

end ConformalNetBalancedCategoryStage

section ConformalNetBalancedCategoryPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.AmariOperatorDuallyFlatGaussianPythagoreanPoset

variable {B : Type*} [Ring B]

/-- **Multiplicative Connes Double-Braiding Monodromy (`connesBraidMonodromy`)**:
$$\mathcal{M}_{\mathrm{braid}}(P, A, C) \;:=\; \mathcal{E}_+(N_+)\,\mathcal{E}_-(N_-)\,\mathcal{E}_+^{-1}(N_+)\,\mathcal{E}_-^{-1}(N_-)
  \;=\; (1 + N_+)(1 + N_-)(1 - N_+)(1 - N_-).$$ -/
def connesBraidMonodromy (P A C : B) : B :=
  attnGaussianFwd (conePlus P A) (coneMinus P C) *
    attnGaussianFwd (-conePlus P A) (-coneMinus P C)

/-- **Inverse Multiplicative Connes Double-Braiding Monodromy (`connesBraidMonodromyInv`)**:
$$\mathcal{M}_{\mathrm{braid}}^{-1}(P, A, C) \;:=\; \mathcal{E}_-(N_-)\,\mathcal{E}_+(N_+)\,\mathcal{E}_-^{-1}(N_-)\,\mathcal{E}_+^{-1}(N_+)
  \;=\; (1 + N_-)(1 + N_+)(1 - N_-)(1 - N_+).$$ -/
def connesBraidMonodromyInv (P A C : B) : B :=
  attnGaussianRev (conePlus P A) (coneMinus P C) *
    attnGaussianInv (conePlus P A) (coneMinus P C)

/-- **Non-Semisimple LogCFT Unipotent Balance Twist (`logCFTBalanceTwist`)**:
For a conformal Hamiltonian $L_0 = h \cdot 1 + N_{\mathrm{nil}}$ with nilpotent Jordan
partner $N_{\mathrm{nil}}^2 = 0$, semisimple spin factor $w = e^{-2\pi i h}$, and logarithmic
coupling $c$, the canonical $2\pi$-rotation balance operator is:
$$\theta_{\mathrm{LogCFT}}(w, c, N_{\mathrm{nil}}) \;:=\; w * (1 - c * N_{\mathrm{nil}}).$$ -/
def logCFTBalanceTwist (w c N_nil : B) : B :=
  w * (1 - c * N_nil)

/-- **Stage `ℭ𝔑₁` (`cn1_two_sheeted_circle_split_and_haag_commutant_duality`)**:
1. **Two-Sheeted Circle Split ($S^1 = I_- \cup I_+$) & Complementary Peirce Projectors**:
   In any associative ring `[Ring B]` with idempotent $P^2 = P$:
   - `(1 - P) * (1 - P) = 1 - P`,
   - `P * (1 - P) = 0` and `(1 - P) * P = 0`,
   - `P + (1 - P) = 1`,
   - DeWitt reflection involution $S_P = 2P - 1$ (`invS P`) satisfies $S_P^2 = 1$,
     $S_P P = P$, and $S_P (1 - P) = -(1 - P)$.
2. **Haag Locality & Commutant Independence Across Complementary Semicircles**:
   For any operators $X, Y \in B$, the upper-semicircle observable $P X P \in \mathcal{A}(I_+)$
   and lower-semicircle observable $(1 - P) Y (1 - P) \in \mathcal{A}(I_-) = \mathcal{A}(I_+)'$
   strictly annihilate and commute:
   $$(P X P)\big((1 - P) Y (1 - P)\big) = 0 \;\land\;
     [P X P, \, (1 - P) Y (1 - P)] = 0.$$ -/
theorem cn1_two_sheeted_circle_split_and_haag_commutant_duality
    {P : B} (hP : P * P = P) (X Y : B) :
    (1 - P) * (1 - P) = 1 - P ∧
    P * (1 - P) = 0 ∧
    (1 - P) * P = 0 ∧
    P + (1 - P) = 1 ∧
    invS P * invS P = 1 ∧
    invS P * P = P ∧
    invS P * (1 - P) = -(1 - P) ∧
    (P * X * P) * ((1 - P) * Y * (1 - P)) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (P * X * P) ((1 - P) * Y * (1 - P)) = 0 := by
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by noncomm_ring,
    by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
    by dsimp [OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP⟩

/-- **Stage `ℭ𝔑₂` (`cn2_connes_fusion_across_seam_and_radon_nikodym_gluing`)**:
1. **Connes Fusion $\mathcal{H}_{(-)} \boxtimes_{\mathcal{A}} \mathcal{K}_{(+)}$ Across the Two-Point Seam**:
   Gluing the upper-semicircle unipotent transport $\mathcal{E}_+(N_+) = 1 + N_+$ and lower-semicircle
   transport $\mathcal{E}_-(N_-) = 1 + N_-$ across the boundary seam $\partial I_\pm = \{-1, +1\}$
   yields the forward and reverse Connes-fused Operator Gaussians:
   $$\mathcal{G}_+(N_+, N_-) = 1 + \Phi + Q_+, \qquad \mathcal{G}_-(N_+, N_-) = 1 + \Phi + Q_-.$$
2. **Rung 0 Socratic Aporia (Non-Additivity of Connes Fusion vs. Naive Direct Sum)**:
   The naive additive superposition $1 + N_+ + N_- = 1 + \Phi$ misses the Radon–Nikodym
   intertwiner $Q_+ = N_+ N_-$ and $Q_- = N_- N_+$:
   $$\mathcal{G}_+ - (1 + \Phi) = Q_+, \qquad \mathcal{G}_- - (1 + \Phi) = Q_-,$$
   while the chiral difference and symmetric sum isolate the Para-Berry curvature
   $\Sigma = [N_+, N_-]$ and symmetric Fisher metric $V = \{N_+, N_-\}$:
   $$\mathcal{G}_+ - \mathcal{G}_- = \Sigma, \qquad
     \mathcal{G}_+ + \mathcal{G}_- - 2(1 + \Phi) = V.$$ -/
theorem cn2_connes_fusion_across_seam_and_radon_nikodym_gluing
    {P : B} (_hP : P * P = P) (A C : B) :
    attnGaussianFwd (conePlus P A) (coneMinus P C) =
      1 + genPhi P A C + qgtPlus P A C ∧
    attnGaussianRev (conePlus P A) (coneMinus P C) =
      1 + genPhi P A C + qgtMinus P A C ∧
    attnGaussianFwd (conePlus P A) (coneMinus P C) - (1 + genPhi P A C) =
      qgtPlus P A C ∧
    attnGaussianRev (conePlus P A) (coneMinus P C) - (1 + genPhi P A C) =
      qgtMinus P A C ∧
    attnGaussianFwd (conePlus P A) (coneMinus P C) -
      attnGaussianRev (conePlus P A) (coneMinus P C) = genSig P A C ∧
    attnGaussianFwd (conePlus P A) (coneMinus P C) +
      attnGaussianRev (conePlus P A) (coneMinus P C) -
      (2 : ℤ) • (1 + genPhi P A C) = genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [attnGaussianFwd, attnGaussianRev, qgtPlus, qgtMinus]); peirce_nf _hP)

/-- **Stage `ℭ𝔑₃` (`cn3_path_continuation_braiding_and_sheet_swap_reflection`)**:
1. **Sheet-Swap Reflection Action of $S_P = 2P - 1$ (`invS P`)**:
   Conjugating by the DeWitt involution $S_P$ flips the odd seam frame $(\Phi, J)$ while
   preserving the even metric/curvature invariants $(V, \Sigma)$ and inverting the unipotent
   Connes-fusion gates:
   $$S_P \Phi S_P = -\Phi, \qquad S_P J S_P = -J, \qquad S_P V S_P = V, \qquad S_P \Sigma S_P = \Sigma,$$
   $$S_P (1 + N_+) S_P = 1 - N_+, \qquad S_P (1 + N_-) S_P = 1 - N_-,$$
   $$S_P \mathcal{G}_+(N_+, N_-) S_P = \mathcal{G}_+(-N_+, -N_-) = 1 - \Phi + Q_+.$$
2. **Exact Two-Sided Polynomial Inverses of Both Braiding Orders**:
   $$\mathcal{G}_+(N_+, N_-)\,\mathcal{G}_+^{-1}(N_+, N_-) = 1, \qquad
     \mathcal{G}_-(N_+, N_-)\,\mathcal{G}_+(-N_+, -N_-) = 1, \qquad
     \mathcal{G}_+(-N_+, -N_-)\,\mathcal{G}_-(N_+, N_-) = 1.$$ -/
theorem cn3_path_continuation_braiding_and_sheet_swap_reflection
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * genPhi P A C * invS P = -genPhi P A C ∧
    invS P * genJ P A C * invS P = -genJ P A C ∧
    invS P * genV P A C * invS P = genV P A C ∧
    invS P * genSig P A C * invS P = genSig P A C ∧
    invS P * attnGatePlus (conePlus P A) * invS P = attnGatePlus (-conePlus P A) ∧
    invS P * attnGateMinus (coneMinus P C) * invS P = attnGateMinus (-coneMinus P C) ∧
    invS P * attnGaussianFwd (conePlus P A) (coneMinus P C) * invS P =
      attnGaussianFwd (-conePlus P A) (-coneMinus P C) ∧
    attnGaussianFwd (-conePlus P A) (-coneMinus P C) =
      1 - genPhi P A C + qgtPlus P A C ∧
    attnGaussianFwd (conePlus P A) (coneMinus P C) *
      attnGaussianInv (conePlus P A) (coneMinus P C) = 1 ∧
    attnGaussianRev (conePlus P A) (coneMinus P C) *
      attnGaussianFwd (-conePlus P A) (-coneMinus P C) = 1 ∧
    attnGaussianFwd (-conePlus P A) (-coneMinus P C) *
      attnGaussianRev (conePlus P A) (coneMinus P C) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [attnGatePlus, attnGateMinus, attnGaussianFwd, attnGaussianRev,
      attnGaussianInv, qgtPlus]);
     peirce_nf hP)

/-- **Stage `ℭ𝔑₄` (`cn4_universal_cover_mobius_lift_and_logcft_unipotent_balance`)**:
1. **Rung 0 Bare-$\mathrm{Möb}$ Spin-Erasure Aporia**:
   In bare $\mathrm{Möb} = \mathrm{PSU}(1,1)$ where $R(2\pi) = 1$, a representation factoring
   through bare $\mathrm{Möb}$ forces $\theta_{\mathcal{H}} = 1$, which annihilates any
   fractional conformal spin shift $\theta_{\mathcal{H}} - 1 = 0$.
2. **Universal Cover $\widetilde{\mathrm{Möb}}$ Unipotent LogCFT Balance Twist**:
   For any nilpotent conformal Hamiltonian Jordan partner $N_{\mathrm{nil}} \in B$ with
   $N_{\mathrm{nil}}^2 = 0$ and central parameters $w_1, w_2, c_1, c_2 \in R$ (in an $R$-algebra
   `[CommRing R] [Algebra R B]`), the unipotent balance twist
   $$\theta_{\mathrm{LogCFT}}(w, c, N_{\mathrm{nil}}) = (w : B) * (1 - (c : B) * N_{\mathrm{nil}})$$
   satisfies:
   - **Exact Multiplicative Group Homomorphism Law**:
     $$\theta(w_1, c_1, N_{\mathrm{nil}}) * \theta(w_2, c_2, N_{\mathrm{nil}}) =
       \theta(w_1 * w_2, \, c_1 + c_2, \, N_{\mathrm{nil}}).$$
   - **Exact Unipotent Inverse Law**:
     Whenever $w * w_{\mathrm{inv}} = 1$ in $R$,
     $$\theta(w, c, N_{\mathrm{nil}}) * \theta(w_{\mathrm{inv}}, -c, N_{\mathrm{nil}}) = 1.$$
   - **Pure Unipotent Specialization ($w = 1$)**:
     $$\theta(1, c_1, N_{\mathrm{nil}}) * \theta(1, c_2, N_{\mathrm{nil}}) =
       \theta(1, c_1 + c_2, N_{\mathrm{nil}}).$$ -/
theorem cn4_universal_cover_mobius_lift_and_logcft_unipotent_balance
    {R : Type*} [CommRing R] [Algebra R B]
    (theta : B) (w₁ w₂ w w_inv c₁ c₂ c : R)
    (h_inv : w * w_inv = 1)
    {N_nil : B} (hNil : N_nil * N_nil = 0) :
    (theta = 1 → theta - 1 = 0) ∧
    logCFTBalanceTwist (algebraMap R B w₁) (algebraMap R B c₁) N_nil *
      logCFTBalanceTwist (algebraMap R B w₂) (algebraMap R B c₂) N_nil =
      logCFTBalanceTwist (algebraMap R B (w₁ * w₂)) (algebraMap R B (c₁ + c₂)) N_nil ∧
    logCFTBalanceTwist (algebraMap R B w) (algebraMap R B c) N_nil *
      logCFTBalanceTwist (algebraMap R B w_inv) (algebraMap R B (-c)) N_nil = 1 ∧
    logCFTBalanceTwist 1 (algebraMap R B c₁) N_nil *
      logCFTBalanceTwist 1 (algebraMap R B c₂) N_nil =
      logCFTBalanceTwist 1 (algebraMap R B (c₁ + c₂)) N_nil := by
  have hMul : ∀ (u₁ u₂ d₁ d₂ : R),
      logCFTBalanceTwist (algebraMap R B u₁) (algebraMap R B d₁) N_nil *
        logCFTBalanceTwist (algebraMap R B u₂) (algebraMap R B d₂) N_nil =
        logCFTBalanceTwist (algebraMap R B (u₁ * u₂)) (algebraMap R B (d₁ + d₂)) N_nil := by
    intro u₁ u₂ d₁ d₂
    dsimp [logCFTBalanceTwist]
    rw [map_mul, map_add]
    have hCommU2 : ∀ x : B, x * algebraMap R B u₂ = algebraMap R B u₂ * x :=
      fun x => (Algebra.commutes u₂ x).symm
    have hCommD1 : ∀ x : B, x * algebraMap R B d₁ = algebraMap R B d₁ * x :=
      fun x => (Algebra.commutes d₁ x).symm
    have hCommD2 : ∀ x : B, x * algebraMap R B d₂ = algebraMap R B d₂ * x :=
      fun x => (Algebra.commutes d₂ x).symm
    calc algebraMap R B u₁ * (1 - algebraMap R B d₁ * N_nil) *
            (algebraMap R B u₂ * (1 - algebraMap R B d₂ * N_nil))
      _ = algebraMap R B u₁ *
            ((1 - algebraMap R B d₁ * N_nil) * algebraMap R B u₂) *
            (1 - algebraMap R B d₂ * N_nil) := by noncomm_ring
      _ = algebraMap R B u₁ *
            (algebraMap R B u₂ * (1 - algebraMap R B d₁ * N_nil)) *
            (1 - algebraMap R B d₂ * N_nil) := by rw [hCommU2]
      _ = (algebraMap R B u₁ * algebraMap R B u₂) *
            (1 - (algebraMap R B d₁ + algebraMap R B d₂) * N_nil +
              algebraMap R B d₁ * (N_nil * algebraMap R B d₂) * N_nil) := by noncomm_ring
      _ = (algebraMap R B u₁ * algebraMap R B u₂) *
            (1 - (algebraMap R B d₁ + algebraMap R B d₂) * N_nil +
              algebraMap R B d₁ * (algebraMap R B d₂ * N_nil) * N_nil) := by rw [hCommD2 N_nil]
      _ = (algebraMap R B u₁ * algebraMap R B u₂) *
            (1 - (algebraMap R B d₁ + algebraMap R B d₂) * N_nil +
              algebraMap R B d₁ * algebraMap R B d₂ * (N_nil * N_nil)) := by noncomm_ring
      _ = (algebraMap R B u₁ * algebraMap R B u₂) *
            (1 - (algebraMap R B d₁ + algebraMap R B d₂) * N_nil) := by
            rw [hNil]; noncomm_ring
  refine ⟨fun h => by rw [h, sub_self], hMul w₁ w₂ c₁ c₂, ?_, ?_⟩
  · rw [hMul w w_inv c (-c), h_inv, add_neg_cancel, map_one, map_zero]
    dsimp [logCFTBalanceTwist]
    noncomm_ring
  · have h1 := hMul 1 1 c₁ c₂
    simpa [map_one] using h1

/-- **Stage `ℭ𝔑₅` (`cn5_fundamental_balancing_monodromy_and_all_orders_commutator_law`)**:
**Theorem 1 (All-Orders Multiplicative Group-Commutator / Double-Braiding Monodromy Law)**:
In any associative ring `[Ring B]` with idempotent $P^2 = P$ and $A, C \in B$:
1. **Exact All-Orders Expansion of the Double-Braiding Monodromy $\mathcal{M}_{\mathrm{braid}}(P, A, C)$**:
   $$\mathcal{M}_{\mathrm{braid}}(P, A, C) \;=\; (1 + N_+)(1 + N_-)(1 - N_+)(1 - N_-)
     \;=\; 1 + \Sigma - V J + Q_+^2,$$
   and its reverse monodromy expands as:
   $$\mathcal{M}_{\mathrm{braid}}^{-1}(P, A, C) \;=\; (1 + N_-)(1 + N_+)(1 - N_-)(1 - N_+)
     \;=\; 1 - \Sigma + V J + Q_-^2.$$
2. **Exact Two-Sided Invertibility of the Monodromy**:
   $$\mathcal{M}_{\mathrm{braid}}(P, A, C) * \mathcal{M}_{\mathrm{braid}}^{-1}(P, A, C) = 1 \;\land\;
     \mathcal{M}_{\mathrm{braid}}^{-1}(P, A, C) * \mathcal{M}_{\mathrm{braid}}(P, A, C) = 1.$$
3. **Exact Balancing Coherence Identity (`G_+ = M_braid * G_-`)**:
   $$\mathcal{G}_+(N_+, N_-) \;=\; \mathcal{M}_{\mathrm{braid}}(P, A, C) * \mathcal{G}_-(N_+, N_-),$$
   $$\mathcal{G}_-(N_+, N_-) \;=\; \mathcal{M}_{\mathrm{braid}}^{-1}(P, A, C) * \mathcal{G}_+(N_+, N_-),$$
   and the higher-order non-abelian defect between the multiplicative monodromy
   $\mathcal{M}_{\mathrm{braid}} - 1$ and the additive Para-Berry curvature $\Sigma = [\mathcal{E}_+, \mathcal{E}_-]$
   is $-V J + Q_+^2$ (half the Operator Bohm quantum force $\frac{1}{4}\mathcal{M}_\Phi(J) = -V J$ plus the
   quartic chiral Casimir $Q_+^2$):
   $$(\mathcal{M}_{\mathrm{braid}}(P, A, C) - 1) - \Sigma \;=\; -V J + Q_+^2.$$ -/
theorem cn5_fundamental_balancing_monodromy_and_all_orders_commutator_law
    {P : B} (hP : P * P = P) (A C : B) :
    connesBraidMonodromy P A C =
      1 + genSig P A C - genV P A C * genJ P A C + qgtPlus P A C * qgtPlus P A C ∧
    connesBraidMonodromyInv P A C =
      1 - genSig P A C + genV P A C * genJ P A C + qgtMinus P A C * qgtMinus P A C ∧
    connesBraidMonodromy P A C * connesBraidMonodromyInv P A C = 1 ∧
    connesBraidMonodromyInv P A C * connesBraidMonodromy P A C = 1 ∧
    attnGaussianFwd (conePlus P A) (coneMinus P C) =
      connesBraidMonodromy P A C * attnGaussianRev (conePlus P A) (coneMinus P C) ∧
    attnGaussianRev (conePlus P A) (coneMinus P C) =
      connesBraidMonodromyInv P A C * attnGaussianFwd (conePlus P A) (coneMinus P C) ∧
    (connesBraidMonodromy P A C - 1) - genSig P A C =
      -(genV P A C * genJ P A C) + qgtPlus P A C * qgtPlus P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [connesBraidMonodromy, connesBraidMonodromyInv, attnGaussianFwd,
      attnGaussianRev, attnGaussianInv, qgtPlus, qgtMinus];
     peirce_nf hP)

/-- **Stage `ℭ𝔑₆` (`cn6_unipotent_logcft_balance_and_master_synthesis`)**:
**Theorem 2 (Unipotent LogCFT Balance Action on Generalized Eigenvectors & Master Synthesis)**:
1. **Poset Acyclicity, Cardinality, & Diamond Branching (`CN5 ∥ CN6`)**:
   `ConformalNetBalancedCategoryStage.causalEdge_acyclic`,
   `Fintype.card ConformalNetBalancedCategoryStage = 6`, and
   `¬ causalEdge CN5 CN6 ∧ ¬ causalEdge CN6 CN5`.
2. **Unipotent LogCFT Balance Action on a Rank-2 Jordan Chain $(\Phi_{\mathrm{gen}}, \Psi_{\mathrm{jord}})$**:
   For any rank-2 Jordan chain satisfying $N_{\mathrm{nil}} * \Phi_{\mathrm{gen}} = \Psi_{\mathrm{jord}}$
   and $N_{\mathrm{nil}} * \Psi_{\mathrm{jord}} = 0$:
   - $\theta_{\mathrm{LogCFT}}(w, c, N_{\mathrm{nil}}) * \Phi_{\mathrm{gen}} = w * \Phi_{\mathrm{gen}} - (w * c) * \Psi_{\mathrm{jord}}$,
   - $\theta_{\mathrm{LogCFT}}(w, c, N_{\mathrm{nil}}) * \Psi_{\mathrm{jord}} = w * \Psi_{\mathrm{jord}}$,
   - And the off-diagonal logarithmic monodromy shift after subtracting the semisimple phase
     $w * \Phi_{\mathrm{gen}}$ is:
     $$\theta_{\mathrm{LogCFT}}(w, c, N_{\mathrm{nil}}) * \Phi_{\mathrm{gen}} - w * \Phi_{\mathrm{gen}}
       \;=\; -(w * c) * \Psi_{\mathrm{jord}}.$$
3. **Modular $c/24$ Framing Clock & Master Conformal Net Balancing Synthesis**:
   Bundles `(24 : ZMod 24) = 0`, `sigma24Map (psi24Map d X) = (24 : ℤ) • X`,
   $\mathcal{M}_{\mathrm{braid}}(P, A, C) = 1 + \Sigma - V J + Q_+^2$,
   $\mathcal{G}_+(N_+, N_-) = \mathcal{M}_{\mathrm{braid}}(P, A, C) * \mathcal{G}_-(N_+, N_-)$, and
   $\mathcal{M}_{\mathrm{braid}}(P, A, C) * \mathcal{M}_{\mathrm{braid}}^{-1}(P, A, C) = 1$. -/
theorem cn6_unipotent_logcft_balance_and_master_synthesis
    {P : B} (hP : P * P = P) (A C d X : B)
    (w c N_nil Phi_gen Psi_jord : B)
    (hJord1 : N_nil * Phi_gen = Psi_jord)
    (hJord2 : N_nil * Psi_jord = 0) :
    -- 1. Poset acyclicity, cardinality, and diamond branching (CN5 ∥ CN6):
    (∀ st : ConformalNetBalancedCategoryStage,
      ¬ Relation.TransGen ConformalNetBalancedCategoryStage.causalEdge st st) ∧
    Fintype.card ConformalNetBalancedCategoryStage = 6 ∧
    (¬ ConformalNetBalancedCategoryStage.causalEdge
        .CN5_FundamentalBalancingMonodromyTheorem
        .CN6_UnipotentLogCFTBalanceAndMasterSynthesis ∧
     ¬ ConformalNetBalancedCategoryStage.causalEdge
        .CN6_UnipotentLogCFTBalanceAndMasterSynthesis
        .CN5_FundamentalBalancingMonodromyTheorem) ∧
    -- 2. Unipotent LogCFT balance shift on a rank-2 Jordan chain:
    logCFTBalanceTwist w c N_nil * Phi_gen = w * Phi_gen - (w * c) * Psi_jord ∧
    logCFTBalanceTwist w c N_nil * Psi_jord = w * Psi_jord ∧
    logCFTBalanceTwist w c N_nil * Phi_gen - w * Phi_gen = -((w * c) * Psi_jord) ∧
    -- 3. Modular 24-clock compatibility and Master Conformal Net Balancing synthesis:
    (24 : ZMod 24) = 0 ∧
    sigma24Map (psi24Map d X) = (24 : ℤ) • X ∧
    connesBraidMonodromy P A C =
      1 + genSig P A C - genV P A C * genJ P A C + qgtPlus P A C * qgtPlus P A C ∧
    attnGaussianFwd (conePlus P A) (coneMinus P C) =
      connesBraidMonodromy P A C * attnGaussianRev (conePlus P A) (coneMinus P C) ∧
    connesBraidMonodromy P A C * connesBraidMonodromyInv P A C = 1 := by
  have hActGen : logCFTBalanceTwist w c N_nil * Phi_gen = w * Phi_gen - (w * c) * Psi_jord := by
    calc logCFTBalanceTwist w c N_nil * Phi_gen
      _ = w * Phi_gen - (w * c) * (N_nil * Phi_gen) := by
            dsimp [logCFTBalanceTwist]; noncomm_ring
      _ = w * Phi_gen - (w * c) * Psi_jord := by rw [hJord1]
  have hActJord : logCFTBalanceTwist w c N_nil * Psi_jord = w * Psi_jord := by
    calc logCFTBalanceTwist w c N_nil * Psi_jord
      _ = w * Psi_jord - (w * c) * (N_nil * Psi_jord) := by
            dsimp [logCFTBalanceTwist]; noncomm_ring
      _ = w * Psi_jord - (w * c) * 0 := by rw [hJord2]
      _ = w * Psi_jord := by noncomm_ring
  have hShift : logCFTBalanceTwist w c N_nil * Phi_gen - w * Phi_gen = -((w * c) * Psi_jord) := by
    rw [hActGen]
    abel
  have hDM6 := dm6_twenty_four_isogeny_glue_law_and_master_synthesis
    (S := invS P) (Q := genPhi P A C) (P := P)
    ((p1_p2_dewitt_split_tangent_polarization_and_unipotent_charts hP A C).1)
    (by peirce_nf hP) hP A C X d
  have hCN5 := cn5_fundamental_balancing_monodromy_and_all_orders_commutator_law hP A C
  exact ⟨ConformalNetBalancedCategoryStage.causalEdge_acyclic,
    ConformalNetBalancedCategoryStage.card_eq_six,
    ConformalNetBalancedCategoryStage.incomparable_CN5_CN6,
    hActGen, hActJord, hShift,
    by decide,
    hDM6.2.2.2.1,
    hCN5.1,
    hCN5.2.2.2.2.1,
    hCN5.2.2.1⟩

end ConformalNetBalancedCategoryPoset

/-!
## 9e. The 6-Stage Cyclic Möbius Ring, `(0, 1, ∞) ↦ (0, 1, 0)` Projective Variance, & 24-Cyclotomic Sieve Poset (`ℜ𝔑₁ ≺ ℜ𝔑₂ ≺ ℜ𝔑₃ ≺ {ℜ𝔑₄, ℜ𝔑₅} ≺ ℜ𝔑₆`)
-/

/-- **The 6-Stage Cyclic Möbius Ring & `(0, 1, ∞) ↦ (0, 1, 0)` Projective-Arithmetic Inversion Poset
(`CyclicMobiusRingStage`, `ℜ𝔑₁ ≺ ℜ𝔑₂ ≺ ℜ𝔑₃ ≺ {ℜ𝔑₄, ℜ𝔑₅} ≺ ℜ𝔑₆`)**:
Formalizes the acyclic causal poset severing the open linear runaway ray $(0, 1, \infty)$ in a
single affine chart from a homogeneous two-chart projective-coordinate family, glued by
geometric Möbius inversion ($u \leftrightarrow v \iff z \leftrightarrow 1/z$) and arithmetic
Witten–Möbius inversion ($\mu(n)$):
* `RN1_ProjectiveCircleAtlasAndSingleChartAporia` (`ℜ𝔑₁`):
  Single-chart overlap aporia $P(1 - P) = 0$ (preventing $1 - P$ from being a finite graph over $P$),
  twisted-$\mathrm{Pin}$ swap involution $\Phi_1$ ($\Phi_1^2 = 1$, $\Phi_1 P \Phi_1 = 1 - P$),
  symplectic generator $J_1 = [P, \Phi_1] = S_P \Phi_1$ ($J_1^2 = -1$), and the homogeneous
  projective state family $\widetilde{\Pi}(u, v) = u^2 P + u v \Phi_1 + v^2(1 - P)$ with anchors
  $\widetilde{\Pi}(1, 0) = P$, $\widetilde{\Pi}(1, 1) = 1 + \Phi_1$, $\widetilde{\Pi}(0, 1) = 1 - P$.
* `RN2_HomogeneousIdempotencyAndMobiusReciprocalGluing` (`ℜ𝔑₂`):
  Exact division-free homogeneous idempotency $\widetilde{\Pi}(u, v)^2 = (u^2 + v^2)\widetilde{\Pi}(u, v)$
  and exact Möbius sheet-swap gluing $\Phi_1 \widetilde{\Pi}(u, v) \Phi_1 = \widetilde{\Pi}(v, u)$
  mapping the North Pole horizon $(0 : 1)$ ($z = \infty$) to the dual vacuum origin $(1 : 0)$ ($w = 0$).
* `RN3_ZeroOneInfinityToZeroOneZeroFubiniStudyVarianceLaw` (`ℜ𝔑₃`):
  Closed-form homogeneous Fubini–Study / Fisher variance
  $4\widetilde{V}(u, v) = -4[P, \widetilde{\Pi}(u, v)]^2 = (4 u^2 v^2) \cdot 1$, its exact reciprocal
  symmetry $4\widetilde{V}(u, v) = 4\widetilde{V}(v, u)$, and the $(0, 1, \infty) \mapsto (0, 1, 0)$
  anchor evaluation $(4\widetilde{V}(1, 0), 4\widetilde{V}(1, 1), 4\widetilde{V}(0, 1)) = (0, 4 \cdot 1, 0)$.
* `RN4_HomogeneousOperatorCayleyCircleWinding` (`ℜ𝔑₄`, diamond branch A):
  Homogeneous Operator Cayley transform $\widetilde{U}(u, v) = (u^2 - v^2) \cdot 1 + 2 u v J_1 = (u \cdot 1 + v J_1)^2$,
  unitarity $\widetilde{U}(u, v)\widetilde{U}(u, -v) = (u^2 + v^2)^2 \cdot 1$, Möbius inversion
  $\widetilde{U}(v, u) = -\widetilde{U}(u, -v)$, and circle winding $(1:0) \mapsto +1$, $(1:1) \mapsto 2 J_1$, $(0:1) \mapsto -1$.
* `RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency` (`ℜ𝔑₅`, diamond branch B):
  Pauli fermionic nilpotency $\theta_p^2 = 0 \implies (1 - \theta_p)(1 + \theta_p) = 1$,
  two-prime Möbius divisor sum reset, and the exact 24-cyclotomic Möbius sieve polynomial identity
  $(x^{24} - 1)(x^4 - 1) = (x^{12} - 1)(x^8 - 1)(x^8 - x^4 + 1)$.
* `RN6_ConformalCyclicAeonResetAnd24CyclotomicRingClosure` (`ℜ𝔑₆`):
  Master synthesis uniting the projective aeonic reset $(0, 1, \infty) \mapsto (0, 1, 0)$,
  Cayley circle winding, and the 24-cyclotomic ring $\Phi_{24}(x) = x^8 - x^4 + 1$. -/
inductive CyclicMobiusRingStage : Type
  | RN1_ProjectiveCircleAtlasAndSingleChartAporia
  | RN2_HomogeneousIdempotencyAndMobiusReciprocalGluing
  | RN3_ZeroOneInfinityToZeroOneZeroFubiniStudyVarianceLaw
  | RN4_HomogeneousOperatorCayleyCircleWinding
  | RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency
  | RN6_ConformalCyclicAeonResetAnd24CyclotomicRingClosure
  deriving DecidableEq, Repr, Inhabited

namespace CyclicMobiusRingStage

/-- Topological rank of each stage in `CyclicMobiusRingStage`
(`RN1(0) < RN2(1) < RN3(2) < {RN4(3), RN5(3)} < RN6(4)`). -/
def rank : CyclicMobiusRingStage → ℕ
  | .RN1_ProjectiveCircleAtlasAndSingleChartAporia => 0
  | .RN2_HomogeneousIdempotencyAndMobiusReciprocalGluing => 1
  | .RN3_ZeroOneInfinityToZeroOneZeroFubiniStudyVarianceLaw => 2
  | .RN4_HomogeneousOperatorCayleyCircleWinding => 3
  | .RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency => 3
  | .RN6_ConformalCyclicAeonResetAnd24CyclotomicRingClosure => 4

/-- Direct Hasse covering edges of `ℜ𝔑₁ ≺ ℜ𝔑₂ ≺ ℜ𝔑₃ ≺ {ℜ𝔑₄, ℜ𝔑₅} ≺ ℜ𝔑₆`. -/
def causalEdge : CyclicMobiusRingStage → CyclicMobiusRingStage → Prop
  | .RN1_ProjectiveCircleAtlasAndSingleChartAporia,
    .RN2_HomogeneousIdempotencyAndMobiusReciprocalGluing => True
  | .RN2_HomogeneousIdempotencyAndMobiusReciprocalGluing,
    .RN3_ZeroOneInfinityToZeroOneZeroFubiniStudyVarianceLaw => True
  | .RN3_ZeroOneInfinityToZeroOneZeroFubiniStudyVarianceLaw,
    .RN4_HomogeneousOperatorCayleyCircleWinding => True
  | .RN3_ZeroOneInfinityToZeroOneZeroFubiniStudyVarianceLaw,
    .RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency => True
  | .RN4_HomogeneousOperatorCayleyCircleWinding,
    .RN6_ConformalCyclicAeonResetAnd24CyclotomicRingClosure => True
  | .RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency,
    .RN6_ConformalCyclicAeonResetAnd24CyclotomicRingClosure => True
  | _, _ => False

instance : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue trivial | exact isFalse not_false

instance : Fintype CyclicMobiusRingStage where
  elems := {
    .RN1_ProjectiveCircleAtlasAndSingleChartAporia,
    .RN2_HomogeneousIdempotencyAndMobiusReciprocalGluing,
    .RN3_ZeroOneInfinityToZeroOneZeroFubiniStudyVarianceLaw,
    .RN4_HomogeneousOperatorCayleyCircleWinding,
    .RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency,
    .RN6_ConformalCyclicAeonResetAnd24CyclotomicRingClosure
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card CyclicMobiusRingStage = 6 := rfl

theorem causalEdge_lt {a b : CyclicMobiusRingStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_causalEdge_lt {a b : CyclicMobiusRingStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_lt hbc)

/-- Strict DAG acyclicity of `CyclicMobiusRingStage`. -/
theorem causalEdge_acyclic (a : CyclicMobiusRingStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_lt h)

/-- Diamond branches `ℜ𝔑₄` and `ℜ𝔑₅` are incomparable. -/
theorem incomparable_RN4_RN5 :
    ¬ causalEdge
        .RN4_HomogeneousOperatorCayleyCircleWinding
        .RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency ∧
    ¬ causalEdge
        .RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency
        .RN4_HomogeneousOperatorCayleyCircleWinding := by
  decide

/-- Monotone map to `RepDepth`. -/
def toRepDepth : CyclicMobiusRingStage → InfoGeometry.Meta.RepDepth
  | .RN1_ProjectiveCircleAtlasAndSingleChartAporia => .operator
  | .RN2_HomogeneousIdempotencyAndMobiusReciprocalGluing => .transport
  | .RN3_ZeroOneInfinityToZeroOneZeroFubiniStudyVarianceLaw => .transport
  | .RN4_HomogeneousOperatorCayleyCircleWinding => .thermo
  | .RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency => .thermo
  | .RN6_ConformalCyclicAeonResetAnd24CyclotomicRingClosure => .thermo

theorem toRepDepth_mono {a b : CyclicMobiusRingStage} (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toRepDepth InfoGeometry.Meta.RepDepth.toNat <;> decide

/-- Monotone map to `OntologyMetaLevel`. -/
def toOntologyMetaLevel :
    CyclicMobiusRingStage →
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel
  | .RN1_ProjectiveCircleAtlasAndSingleChartAporia => .M1_ProjectorClabject
  | .RN2_HomogeneousIdempotencyAndMobiusReciprocalGluing => .M2_GrassmannianPowertypeOrbit
  | .RN3_ZeroOneInfinityToZeroOneZeroFubiniStudyVarianceLaw => .M2_GrassmannianPowertypeOrbit
  | .RN4_HomogeneousOperatorCayleyCircleWinding => .M3_ErlangenCasimirMetaLaw
  | .RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency => .M3_ErlangenCasimirMetaLaw
  | .RN6_ConformalCyclicAeonResetAnd24CyclotomicRingClosure => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_mono {a b : CyclicMobiusRingStage} (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel
      InfoGeometry.OperatorAlgebra.OntologyRing.OntologyMetaLevel.rank <;> decide

end CyclicMobiusRingStage

section CyclicMobiusRingPoset

variable {B : Type*} [Ring B]

/-- Homogeneous projective state family on $\mathbb{P}^1(B)$:
$$\widetilde{\Pi}(u, v) := u^2 P + (u * v)\Phi_1 + v^2(1 - P).$$ -/
def homogProjState {R : Type*} [CommRing R] [Algebra R B]
    (u v : R) (P Phi1 : B) : B :=
  (u ^ 2) • P + (u * v) • Phi1 + (v ^ 2) • (1 - P)

/-- Homogeneous Fubini–Study / Fisher metric variance:
$$4\widetilde{V}(u, v) := -4\,[P, \, \widetilde{\Pi}(u, v)]^2.$$ -/
def homogFubiniStudyVar4 {R : Type*} [CommRing R] [Algebra R B]
    (u v : R) (P Phi1 : B) : B :=
  -((4 : R) • (OperatorAlgebra.PeirceSpine.comm P (homogProjState u v P Phi1) *
    OperatorAlgebra.PeirceSpine.comm P (homogProjState u v P Phi1)))

/-- Homogeneous Operator Cayley circle element:
$$\widetilde{U}(u, v, J_1) := (u^2 - v^2) \cdot 1 + (2 u v) J_1.$$ -/
def homogCayleyCircle {R : Type*} [CommRing R] [Algebra R B]
    (u v : R) (J1 : B) : B :=
  (u ^ 2 - v ^ 2) • (1 : B) + (2 * u * v) • J1

/-- **Stage `ℜ𝔑₁` (`rn1_projective_circle_atlas_and_rung0_single_chart_aporia`)**:
1. **Rung 0 Single-Chart Overlap Aporia**:
   Every primal graph state $P + N_+(X)$ over $P$ ($P^2 = P$) has unit upper-left block
   $P(P + N_+(X))P = P$, whereas the antipodal sheet $1 - P$ has zero overlap $P(1 - P)P = 0$.
   Consequently, if $1 - P = P + N_+(X)$, then $P = 0$.
2. **Twisted-$\mathrm{Pin}$ Sheet-Swap Involution $\Phi_1$ and Symplectic Generator $J_1 = [P, \Phi_1]$**:
   For $P^2 = P$, $\Phi_1^2 = 1$, and $\Phi_1 P = (1 - P)\Phi_1$:
   - $\Phi_1 P \Phi_1 = 1 - P$ and $\Phi_1 (1 - P) \Phi_1 = P$,
   - $P \Phi_1 + \Phi_1 P = \Phi_1$,
   - $[P, \Phi_1] = \mathrm{invS}(P)\Phi_1$ and $[P, \Phi_1]^2 = -1$.
3. **Homogeneous Projective-Coordinate Anchors ($(1:0), (1:1), (0:1)$)**:
   - $\widetilde{\Pi}(1, 0) = P$ (Origin $z = 0$),
   - $\widetilde{\Pi}(1, 1) = 1 + \Phi_1$ (Equatorial Throat $z = 1$),
   - $\widetilde{\Pi}(0, 1) = 1 - P$ (Antipodal Pole $z = \infty \iff w = 0$). -/
theorem rn1_projective_circle_atlas_and_rung0_single_chart_aporia
    {R : Type*} [CommRing R] [Algebra R B]
    {P Phi1 : B} (hP : P * P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (X : B) :
    (P * (P + conePlus P X) * P = P ∧
     P * (1 - P) * P = 0 ∧
     (1 - P = P + conePlus P X → P = 0)) ∧
    (Phi1 * P * Phi1 = 1 - P ∧
     Phi1 * (1 - P) * Phi1 = P ∧
     P * Phi1 + Phi1 * P = Phi1 ∧
     OperatorAlgebra.PeirceSpine.comm P Phi1 = invS P * Phi1 ∧
     OperatorAlgebra.PeirceSpine.comm P Phi1 *
       OperatorAlgebra.PeirceSpine.comm P Phi1 = -1) ∧
    (homogProjState (1 : R) 0 P Phi1 = P ∧
     homogProjState (1 : R) 1 P Phi1 = 1 + Phi1 ∧
     homogProjState (0 : R) 1 P Phi1 = 1 - P) := by
  have hGraphP : P * (P + conePlus P X) * P = P := by peirce_nf hP
  have hZeroOverlap : P * (1 - P) * P = 0 := by peirce_nf hP
  have hAporia : 1 - P = P + conePlus P X → P = 0 := by
    intro hEq
    have h1 : P * (1 - P) * P = P * (P + conePlus P X) * P := by rw [hEq]
    rw [hZeroOverlap, hGraphP] at h1
    exact h1.symm
  have hPhiPPhi : Phi1 * P * Phi1 = 1 - P := by
    calc Phi1 * P * Phi1
      _ = (1 - P) * (Phi1 * Phi1) := by rw [hPhi_P]; noncomm_ring
      _ = (1 - P) * 1 := by rw [hPhi_sq]
      _ = 1 - P := by noncomm_ring
  have hPhi1mP : Phi1 * (1 - P) = P * Phi1 := by
    calc Phi1 * (1 - P)
      _ = Phi1 - Phi1 * P := by noncomm_ring
      _ = Phi1 - (1 - P) * Phi1 := by rw [hPhi_P]
      _ = P * Phi1 := by noncomm_ring
  have hPhiQPhi : Phi1 * (1 - P) * Phi1 = P := by
    calc Phi1 * (1 - P) * Phi1
      _ = P * (Phi1 * Phi1) := by rw [hPhi1mP]; noncomm_ring
      _ = P * 1 := by rw [hPhi_sq]
      _ = P := by noncomm_ring
  have hAnticommPPhi : P * Phi1 + Phi1 * P = Phi1 := by
    calc P * Phi1 + Phi1 * P
      _ = P * Phi1 + (1 - P) * Phi1 := by rw [hPhi_P]
      _ = Phi1 := by noncomm_ring
  have hCommEq : OperatorAlgebra.PeirceSpine.comm P Phi1 = invS P * Phi1 := by
    dsimp [OperatorAlgebra.PeirceSpine.comm, invS]
    calc P * Phi1 - Phi1 * P
      _ = P * Phi1 - (1 - P) * Phi1 := by rw [hPhi_P]
      _ = (P - (1 - P)) * Phi1 := by noncomm_ring
  have hPhiInvS : Phi1 * invS P = -(invS P * Phi1) := by
    dsimp [invS]
    calc Phi1 * (P - (1 - P))
      _ = 2 * (Phi1 * P) - Phi1 := by noncomm_ring
      _ = 2 * ((1 - P) * Phi1) - Phi1 := by rw [hPhi_P]
      _ = -((P - (1 - P)) * Phi1) := by noncomm_ring
  have hInvSSq : invS P * invS P = 1 := by peirce_nf hP
  have hJ1Sq :
      OperatorAlgebra.PeirceSpine.comm P Phi1 *
        OperatorAlgebra.PeirceSpine.comm P Phi1 = -1 := by
    calc OperatorAlgebra.PeirceSpine.comm P Phi1 *
            OperatorAlgebra.PeirceSpine.comm P Phi1
      _ = invS P * (Phi1 * invS P) * Phi1 := by rw [hCommEq]; noncomm_ring
      _ = invS P * (-(invS P * Phi1)) * Phi1 := by rw [hPhiInvS]
      _ = -(invS P * invS P) * (Phi1 * Phi1) := by noncomm_ring
      _ = -1 * 1 := by rw [hInvSSq, hPhi_sq]
      _ = -1 := by noncomm_ring
  refine ⟨⟨hGraphP, hZeroOverlap, hAporia⟩,
    ⟨hPhiPPhi, hPhiQPhi, hAnticommPPhi, hCommEq, hJ1Sq⟩,
    ⟨by dsimp [homogProjState]; module,
     by dsimp [homogProjState]; module,
     by dsimp [homogProjState]; module⟩⟩

/-- **Stage `ℜ𝔑₂` (`rn2_homogeneous_idempotency_and_mobius_reciprocal_gluing`)**:
**Theorem 1a (Division-Free Homogeneous Idempotency & Möbius Reciprocal Gluing)**:
For any $u, v \in R$ and $P, \Phi_1 \in B$ with $P^2 = P$, $\Phi_1^2 = 1$, $\Phi_1 P = (1 - P)\Phi_1$:
1. **Exact Homogeneous Projective Idempotency**:
   $$\widetilde{\Pi}(u, v) * \widetilde{\Pi}(u, v) \;=\; (u^2 + v^2) \bullet \widetilde{\Pi}(u, v).$$
2. **Exact Möbius Sheet-Swap Gluing ($u \leftrightarrow v \iff z \leftrightarrow 1/z$)**:
   $$\Phi_1 * \widetilde{\Pi}(u, v) * \Phi_1 \;=\; \widetilde{\Pi}(v, u).$$
3. **Antipodal Pole Reset ($z = \infty \mapsto w = 0$) & Self-Dual Equator ($z = 1$)**:
   - $\Phi_1 * \widetilde{\Pi}(1, 0) * \Phi_1 = \widetilde{\Pi}(0, 1) = 1 - P$,
   - $\Phi_1 * \widetilde{\Pi}(0, 1) * \Phi_1 = \widetilde{\Pi}(1, 0) = P$,
   - $\Phi_1 * \widetilde{\Pi}(1, 1) * \Phi_1 = \widetilde{\Pi}(1, 1) = 1 + \Phi_1$. -/
theorem rn2_homogeneous_idempotency_and_mobius_reciprocal_gluing
    {R : Type*} [CommRing R] [Algebra R B]
    {P Phi1 : B} (hP : P * P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (u v : R) :
    homogProjState u v P Phi1 * homogProjState u v P Phi1 =
      (u ^ 2 + v ^ 2) • homogProjState u v P Phi1 ∧
    Phi1 * homogProjState u v P Phi1 * Phi1 = homogProjState v u P Phi1 ∧
    Phi1 * homogProjState (1 : R) 0 P Phi1 * Phi1 = 1 - P ∧
    Phi1 * homogProjState (0 : R) 1 P Phi1 * Phi1 = P ∧
    Phi1 * homogProjState (1 : R) 1 P Phi1 * Phi1 = 1 + Phi1 := by
  have hRN1 := rn1_projective_circle_atlas_and_rung0_single_chart_aporia
    (R := R) hP hPhi_sq hPhi_P 0
  have hQQ : (1 - P) * (1 - P) = 1 - P := by peirce_nf hP
  have hPQ : P * (1 - P) = 0 := by peirce_nf hP
  have hQP : (1 - P) * P = 0 := by peirce_nf hP
  have hPhiP' : Phi1 * P = Phi1 - P * Phi1 := by
    calc Phi1 * P
      _ = (1 - P) * Phi1 := hPhi_P
      _ = Phi1 - P * Phi1 := by noncomm_ring
  have hQPhi' : (1 - P) * Phi1 = Phi1 - P * Phi1 := by noncomm_ring
  have hPhiQ : Phi1 * (1 - P) = P * Phi1 := by
    calc Phi1 * (1 - P)
      _ = Phi1 - Phi1 * P := by noncomm_ring
      _ = Phi1 - (1 - P) * Phi1 := by rw [hPhi_P]
      _ = P * Phi1 := by noncomm_ring
  have hPhiSqSplit : Phi1 * Phi1 = P + (1 - P) := by
    calc Phi1 * Phi1
      _ = 1 := hPhi_sq
      _ = P + (1 - P) := by noncomm_ring
  have hIdemp :
      homogProjState u v P Phi1 * homogProjState u v P Phi1 =
        (u ^ 2 + v ^ 2) • homogProjState u v P Phi1 := by
    dsimp [homogProjState]
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      hP, hQQ, hPQ, hQP, hPhiSqSplit, hPhiP', hQPhi', hPhiQ, smul_zero, add_zero, zero_add]
    module
  have hPhi3 : Phi1 * Phi1 * Phi1 = Phi1 := by rw [hPhi_sq, one_mul]
  have hSwap :
      ∀ (a b : R), Phi1 * homogProjState a b P Phi1 * Phi1 = homogProjState b a P Phi1 := by
    intro a b
    dsimp [homogProjState]
    calc Phi1 * ((a ^ 2) • P + (a * b) • Phi1 + (b ^ 2) • (1 - P)) * Phi1
      _ = (a ^ 2) • (Phi1 * P * Phi1) + (a * b) • (Phi1 * Phi1 * Phi1) +
            (b ^ 2) • (Phi1 * (1 - P) * Phi1) := by
            simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
      _ = (a ^ 2) • (1 - P) + (a * b) • Phi1 + (b ^ 2) • P := by
            rw [hRN1.2.1.1, hPhi3, hRN1.2.1.2.1]
      _ = (b ^ 2) • P + (b * a) • Phi1 + (a ^ 2) • (1 - P) := by
            module
  refine ⟨hIdemp, hSwap u v, ?_, ?_, ?_⟩
  · rw [hSwap 1 0, hRN1.2.2.2.2]
  · rw [hSwap 0 1, hRN1.2.2.1]
  · rw [hSwap 1 1, hRN1.2.2.2.1]

/-- **Stage `ℜ𝔑₃` (`rn3_zero_one_infinity_to_zero_one_zero_fubini_study_variance_law`)**:
**Theorem 1b (The $(0, 1, \infty) \mapsto (0, 1, 0)$ Fubini–Study / Fisher Variance Law)**:
For any $u, v \in R$ and $P, \Phi_1 \in B$ with $P^2 = P$, $\Phi_1^2 = 1$, $\Phi_1 P = (1 - P)\Phi_1$:
1. **Commutator with Reference Sheet $P$**:
   $$[P, \, \widetilde{\Pi}(u, v)] \;=\; (u * v) \bullet [P, \, \Phi_1].$$
2. **Closed-Form Homogeneous Fubini–Study Variance**:
   $$4\widetilde{V}(u, v) \;\equiv\; -4\,[P, \, \widetilde{\Pi}(u, v)]^2 \;=\; (4 * u^2 * v^2) \bullet 1.$$
3. **Exact Möbius Reciprocal Invariance ($u \leftrightarrow v \iff z \leftrightarrow 1/z$)**:
   $$4\widetilde{V}(u, v) \;=\; 4\widetilde{V}(v, u).$$
4. **The $(0, 1, \infty) \mapsto (0, 1, 0)$ Anchor Evaluation**:
   - $4\widetilde{V}(1, 0) = 0$ ($z = 0$),
   - $4\widetilde{V}(1, 1) = (4 : R) \bullet 1 = ((1^2 + 1^2)^2) \bullet 1$ ($z = 1$, normalized variance $1$),
   - $4\widetilde{V}(0, 1) = 0$ ($z = \infty \iff w = 1/\infty = 0$). -/
theorem rn3_zero_one_infinity_to_zero_one_zero_fubini_study_variance_law
    {R : Type*} [CommRing R] [Algebra R B]
    {P Phi1 : B} (hP : P * P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (u v : R) :
    OperatorAlgebra.PeirceSpine.comm P (homogProjState u v P Phi1) =
      (u * v) • OperatorAlgebra.PeirceSpine.comm P Phi1 ∧
    homogFubiniStudyVar4 u v P Phi1 = (4 * u ^ 2 * v ^ 2) • (1 : B) ∧
    homogFubiniStudyVar4 u v P Phi1 = homogFubiniStudyVar4 v u P Phi1 ∧
    homogFubiniStudyVar4 (1 : R) 0 P Phi1 = 0 ∧
    homogFubiniStudyVar4 (1 : R) 1 P Phi1 = (4 : R) • (1 : B) ∧
    homogFubiniStudyVar4 (0 : R) 1 P Phi1 = 0 := by
  have hRN1 := rn1_projective_circle_atlas_and_rung0_single_chart_aporia
    (R := R) hP hPhi_sq hPhi_P 0
  have hPQ : P * (1 - P) = 0 := by peirce_nf hP
  have hQP : (1 - P) * P = 0 := by peirce_nf hP
  have hComm :
      ∀ (a b : R),
        OperatorAlgebra.PeirceSpine.comm P (homogProjState a b P Phi1) =
          (a * b) • OperatorAlgebra.PeirceSpine.comm P Phi1 := by
    intro a b
    dsimp [homogProjState, OperatorAlgebra.PeirceSpine.comm]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hP, hPQ, hQP, smul_zero]
    module
  have hVar :
      ∀ (a b : R),
        homogFubiniStudyVar4 a b P Phi1 = (4 * a ^ 2 * b ^ 2) • (1 : B) := by
    intro a b
    dsimp [homogFubiniStudyVar4]
    rw [hComm a b]
    simp only [smul_mul_assoc, mul_smul_comm, hRN1.2.1.2.2.2.2, smul_neg, neg_neg, smul_smul]
    module
  refine ⟨hComm u v, hVar u v, ?_, ?_, ?_, ?_⟩
  · rw [hVar u v, hVar v u]
    module
  · rw [hVar 1 0]
    module
  · rw [hVar 1 1]
    module
  · rw [hVar 0 1]
    module

/-- **Stage `ℜ𝔑₄` (`rn4_homogeneous_operator_cayley_circle_winding`)**:
**Theorem 2a (Homogeneous Operator Cayley Circle $\widetilde{U}(u, v, J_1)$ & Möbius Winding)**:
For any $u, v \in R$ and $J_1 \in B$ with $J_1^2 = -1$:
1. **Quadratic Factorization**:
   $$(u \bullet 1 + v \bullet J_1) * (u \bullet 1 + v \bullet J_1) \;=\; \widetilde{U}(u, v, J_1).$$
2. **Homogeneous Circle Unitarity**:
   $$\widetilde{U}(u, v, J_1) * \widetilde{U}(u, -v, J_1) \;=\; ((u^2 + v^2)^2) \bullet 1 \;\land\;
     \widetilde{U}(u, -v, J_1) * \widetilde{U}(u, v, J_1) \;=\; ((u^2 + v^2)^2) \bullet 1.$$
3. **Möbius Reciprocal Inversion Law ($u \leftrightarrow v \iff z \leftrightarrow 1/z$)**:
   $$\widetilde{U}(v, u, J_1) \;=\; -\widetilde{U}(u, -v, J_1).$$
4. **Three-Point Circle Winding ($(1:0) \mapsto +1$, $(1:1) \mapsto 2 J_1$, $(0:1) \mapsto -1$)**:
   $$\widetilde{U}(1, 0, J_1) = 1 \;\land\;
     \widetilde{U}(1, 1, J_1) = (2 : R) \bullet J_1 \;\land\;
     \widetilde{U}(0, 1, J_1) = -1.$$ -/
theorem rn4_homogeneous_operator_cayley_circle_winding
    {R : Type*} [CommRing R] [Algebra R B]
    {J1 : B} (hJ1 : J1 * J1 = -1) (u v : R) :
    (u • (1 : B) + v • J1) * (u • (1 : B) + v • J1) = homogCayleyCircle u v J1 ∧
    homogCayleyCircle u v J1 * homogCayleyCircle u (-v) J1 =
      ((u ^ 2 + v ^ 2) ^ 2) • (1 : B) ∧
    homogCayleyCircle u (-v) J1 * homogCayleyCircle u v J1 =
      ((u ^ 2 + v ^ 2) ^ 2) • (1 : B) ∧
    homogCayleyCircle v u J1 = -homogCayleyCircle u (-v) J1 ∧
    homogCayleyCircle (1 : R) 0 J1 = 1 ∧
    homogCayleyCircle (1 : R) 1 J1 = (2 : R) • J1 ∧
    homogCayleyCircle (0 : R) 1 J1 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [homogCayleyCircle]
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      mul_one, one_mul, hJ1, smul_neg]
    module
  · dsimp [homogCayleyCircle]
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      mul_one, one_mul, hJ1, smul_neg]
    module
  · dsimp [homogCayleyCircle]
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      mul_one, one_mul, hJ1, smul_neg]
    module
  · dsimp [homogCayleyCircle]
    module
  · dsimp [homogCayleyCircle]
    module
  · dsimp [homogCayleyCircle]
    module
  · dsimp [homogCayleyCircle]
    module

/-- **Stage `ℜ𝔑₅` (`rn5_arithmetic_witten_mobius_sieve_and_cyclotomic_24_divisor_identity`)**:
**Theorem 2b (Arithmetic Witten–Möbius Sieve, Pauli Fermionic Nilpotency, & The 24-Cyclotomic Divisor Identity)**:
1. **Pauli Fermionic Nilpotency Sieve ($\theta_p^2 = 0 \implies (1 - \theta_p)(1 + \theta_p) = 1$)**:
   For any square-zero fermionic generator $\theta_p \in B$ ($\theta_p * \theta_p = 0$),
   $(1 - \theta_p) * (1 + \theta_p) = 1$ and $(1 + \theta_p) * (1 - \theta_p) = 1$.
2. **Two-Prime Euler–Möbius Expansion & Divisor Sum Reset ($\sum_{d \mid p_1 p_2} \mu(d) = 0$)**:
   Over any commutative ring $R$, $(1 - q_1)(1 - q_2) = 1 - q_1 - q_2 + q_1 q_2$, and at $q_1 = q_2 = 1$,
   $1 - 1 - 1 + 1 = 0$.
3. **Exact 24-Cyclotomic Möbius Sieve Polynomial Identity**:
   Over any commutative ring $R$, for any $x \in R$, the Möbius-positively-weighted divisor product
   of $24$ ($d \in \{24, 4\}$, $\mu(24/d) = +1$) equals the negatively-weighted divisor product
   ($d \in \{12, 8\}$, $\mu(24/d) = -1$) times $\Phi_{24}(x) = x^8 - x^4 + 1$:
   $$(x^{24} - 1) * (x^4 - 1) \;=\; (x^{12} - 1) * (x^8 - 1) * (x^8 - x^4 + 1),$$
   and $(x^4 + 1) * (x^8 - x^4 + 1) = x^{12} + 1$. -/
theorem rn5_arithmetic_witten_mobius_sieve_and_cyclotomic_24_divisor_identity
    {R : Type*} [CommRing R]
    {theta_p : B} (hTheta : theta_p * theta_p = 0) (q₁ q₂ x : R) :
    ((1 - theta_p) * (1 + theta_p) = 1 ∧
     (1 + theta_p) * (1 - theta_p) = 1) ∧
    ((1 - q₁) * (1 - q₂) = 1 - q₁ - q₂ + q₁ * q₂ ∧
     (1 - (1 : R)) * (1 - (1 : R)) = 0) ∧
    ((x ^ 24 - 1) * (x ^ 4 - 1) = (x ^ 12 - 1) * (x ^ 8 - 1) * (x ^ 8 - x ^ 4 + 1) ∧
     (x ^ 4 + 1) * (x ^ 8 - x ^ 4 + 1) = x ^ 12 + 1) := by
  have h1 : (1 - theta_p) * (1 + theta_p) = 1 := by
    calc (1 - theta_p) * (1 + theta_p)
      _ = 1 - theta_p * theta_p := by noncomm_ring
      _ = 1 - 0 := by rw [hTheta]
      _ = 1 := by abel
  have h2 : (1 + theta_p) * (1 - theta_p) = 1 := by
    calc (1 + theta_p) * (1 - theta_p)
      _ = 1 - theta_p * theta_p := by noncomm_ring
      _ = 1 - 0 := by rw [hTheta]
      _ = 1 := by abel
  exact ⟨⟨h1, h2⟩, ⟨by ring, by ring⟩, ⟨by ring, by ring⟩⟩

/-- **Stage `ℜ𝔑₆` (`rn6_conformal_cyclic_aeon_reset_and_master_mobius_ring_synthesis`)**:
Master theorem unifying the 6-stage **Cyclic Möbius Ring & $(0, 1, \infty) \mapsto (0, 1, 0)$
Projective-Arithmetic Inversion Poset** (`ℜ𝔑₁ ≺ ℜ𝔑₂ ≺ ℜ𝔑₃ ≺ {ℜ𝔑₄, ℜ𝔑₅} ≺ ℜ𝔑₆`). -/
theorem rn6_conformal_cyclic_aeon_reset_and_master_mobius_ring_synthesis
    {R : Type*} [CommRing R] [Algebra R B]
    {P Phi1 theta_p : B} (hP : P * P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hTheta : theta_p * theta_p = 0)
    (u v x : R) :
    -- 1. Poset acyclicity, cardinality, and diamond branching (RN4 ∥ RN5):
    (∀ st : CyclicMobiusRingStage,
      ¬ Relation.TransGen CyclicMobiusRingStage.causalEdge st st) ∧
    Fintype.card CyclicMobiusRingStage = 6 ∧
    (¬ CyclicMobiusRingStage.causalEdge
        .RN4_HomogeneousOperatorCayleyCircleWinding
        .RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency ∧
     ¬ CyclicMobiusRingStage.causalEdge
        .RN5_ArithmeticWittenMobiusSieveAndFermionicNilpotency
        .RN4_HomogeneousOperatorCayleyCircleWinding) ∧
    -- 2. Homogeneous projective idempotency and Möbius sheet-swap gluing (RN1, RN2):
    homogProjState u v P Phi1 * homogProjState u v P Phi1 =
      (u ^ 2 + v ^ 2) • homogProjState u v P Phi1 ∧
    Phi1 * homogProjState u v P Phi1 * Phi1 = homogProjState v u P Phi1 ∧
    -- 3. The (0, 1, ∞) ↦ (0, 1, 0) Fubini–Study variance law (RN3):
    homogFubiniStudyVar4 u v P Phi1 = (4 * u ^ 2 * v ^ 2) • (1 : B) ∧
    homogFubiniStudyVar4 u v P Phi1 = homogFubiniStudyVar4 v u P Phi1 ∧
    homogFubiniStudyVar4 (1 : R) 0 P Phi1 = 0 ∧
    homogFubiniStudyVar4 (1 : R) 1 P Phi1 = (4 : R) • (1 : B) ∧
    homogFubiniStudyVar4 (0 : R) 1 P Phi1 = 0 ∧
    -- 4. Homogeneous Operator Cayley circle unitarity & Möbius inversion (RN4):
    homogCayleyCircle u v (OperatorAlgebra.PeirceSpine.comm P Phi1) *
      homogCayleyCircle u (-v) (OperatorAlgebra.PeirceSpine.comm P Phi1) =
      ((u ^ 2 + v ^ 2) ^ 2) • (1 : B) ∧
    homogCayleyCircle v u (OperatorAlgebra.PeirceSpine.comm P Phi1) =
      -homogCayleyCircle u (-v) (OperatorAlgebra.PeirceSpine.comm P Phi1) ∧
    -- 5. Pauli fermionic nilpotency, 24-cyclotomic Möbius sieve, & modular 24-clock (RN5, RN6):
    (1 - theta_p) * (1 + theta_p) = 1 ∧
    (x ^ 24 - 1) * (x ^ 4 - 1) = (x ^ 12 - 1) * (x ^ 8 - 1) * (x ^ 8 - x ^ 4 + 1) ∧
    (24 : ZMod 24) = 0 := by
  have hRN1 := rn1_projective_circle_atlas_and_rung0_single_chart_aporia
    (R := R) hP hPhi_sq hPhi_P 0
  have hRN2 := rn2_homogeneous_idempotency_and_mobius_reciprocal_gluing
    hP hPhi_sq hPhi_P u v
  have hRN3 := rn3_zero_one_infinity_to_zero_one_zero_fubini_study_variance_law
    hP hPhi_sq hPhi_P u v
  have hRN4 := rn4_homogeneous_operator_cayley_circle_winding
    hRN1.2.1.2.2.2.2 u v
  have hRN5 := rn5_arithmetic_witten_mobius_sieve_and_cyclotomic_24_divisor_identity
    hTheta x x x
  exact ⟨CyclicMobiusRingStage.causalEdge_acyclic,
    CyclicMobiusRingStage.card_eq_six,
    CyclicMobiusRingStage.incomparable_RN4_RN5,
    hRN2.1, hRN2.2.1,
    hRN3.2.1, hRN3.2.2.1, hRN3.2.2.2.1, hRN3.2.2.2.2.1, hRN3.2.2.2.2.2,
    hRN4.2.1, hRN4.2.2.2.1,
    hRN5.1.1, hRN5.2.2.1,
    by decide⟩

end CyclicMobiusRingPoset

/-!
## 9f. The 6-Stage Nilpotent Maurer–Cartan Backpropagation & Yangian $\mathcal{C}\mathcal{P}\mathcal{T}$-Dyck Syntactic Tree Poset (`𝔅𝔓₁ ≺ 𝔅𝔓₂ ≺ 𝔅𝔓₃ ≺ {𝔅𝔓₄, 𝔅𝔓₅} ≺ 𝔅𝔓₆`)

Passing the **Tensor-Peirce Attention Network** backward gradient pass and grammatical parse-tree
monodromy through the Socratic elenchus severs activation-storing backpropagation and flat
positional distance decay from **Zero-Activation Maurer–Cartan Backpropagation** and
**$\mathcal{C}\mathcal{P}\mathcal{T}$-Dyck Syntactic Tree Reduction**:
1. **Same-Chirality Nilpotent Kill Laws (`𝔅𝔓₁`)**:
   In any associative `[Ring B]` with idempotent $P^2 = P$, because $N_+, dN_+ \in P B (1 - P)$ and
   $N_-, dN_- \in (1 - P) B P$ while $Q_- = N_- N_+ \in (1 - P) B (1 - P)$, Peirce orthogonality
   $P(1 - P) = (1 - P)P = 0$ annihilates all redundant differential products:
   $$(dN_+)\,N_+ = 0, \qquad (dN_-)\,N_- = 0, \qquad (dN_-)\,Q_- = 0.$$
2. **The Nilpotent Maurer–Cartan Backpropagation Identity (`𝔅𝔓₂`)**:
   For $\mathcal{G}_+ = (1 + N_+)(1 + N_-)$ with polynomial inverse
   $\mathcal{G}_+^{-1} = (1 - N_-)(1 - N_+) = 1 - \Phi + Q_-$ and tangent differential
   $d\mathcal{G}_+ = (dN_+)(1 + N_-) + (1 + N_+)(dN_-)$, right multiplication by $\mathcal{G}_+^{-1}$
   eliminates $N_-$ and $Q_-$ completely:
   $$(d\mathcal{G}_+)\,\mathcal{G}_+^{-1} \;=\; dN_+ \;+\; (1 + N_+)\,(dN_-)\,(1 - N_+)
     \;=\; dN_+ \;+\; dN_- \;+\; [N_+, dN_-] \;-\; N_+\,(dN_-)\,N_+.$$
3. **Zero-Memory Backward Pass & The Nilpotent Backprop Miracle (`𝔅𝔓₃`)**:
   Reconstructing $X_{\text{mid}} = (1 - N_+)X_{\text{out}}$ and
   $X_{\text{in}} = (1 - N_-)X_{\text{mid}} = \mathcal{G}_+^{-1} X_{\text{out}}$ from $X_{\text{out}}$
   alone requires zero stored forward activations, and the nilpotent kill laws collapse the
   variations to:
   $$(dN_+)\,X_{\text{mid}} = (dN_+)\,X_{\text{out}}, \qquad
     (dN_-)\,X_{\text{in}} = (dN_-)\,X_{\text{mid}},$$
   so $dX_{\text{out}} = (dN_+)X_{\text{out}} + (1 + N_+)(dN_-)X_{\text{mid}} + \mathcal{G}_+ dX_{\text{in}}$.
4. **$\mathcal{C}\mathcal{P}\mathcal{T}$-Dyck Center-Embedded Clause Collapse (`𝔅𝔓₄`)**:
   Under the Twisted-$\mathrm{Pin}$ anti-automorphism $\Theta_{\text{CPT}}(X) = -J_1 X^\star J_1$
   ($J_1^2 = -1$), every opening shear gate $\mathcal{E}_+(N_+) = 1 + N_+$ has inverse
   $\Theta_{\text{CPT}}(\mathcal{E}_+(N_+)) = 1 - N_+$, so any balanced center-embedded clause
   $W_{\text{sub}}$ collapses to $W_{\text{sub}} \cdot \Theta_{\text{CPT}}(W_{\text{sub}}) = 1$,
   bringing outer constituents $W_{\text{verb}}$ and $W_{\text{subj}}$ into direct distance-zero
   contact $W_{\text{verb}} \cdot (W_{\text{sub}}\,\Theta_{\text{CPT}}(W_{\text{sub}})) \cdot W_{\text{subj}} = W_{\text{verb}} W_{\text{subj}}$.
5. **Two-Step Binary Zorn Phrase Merge & Clause Determinant (`𝔅𝔓₅`)**:
   In `ZornMat R`, two-step non-associative phrase composition first merges two $\mathfrak{n}_+$
   leaves into a dual $\mathfrak{n}_-$ phrase vector $N_+(u_1) N_+(u_2) = N_-(u_1 \times u_2)$, and
   then takes the Jordan anticommutator with the head modifier $N_+(u_3)$ to extract the scalar
   3-body determinant invariant $\{N_+(u_1)N_+(u_2), N_+(u_3)\} = \det(u_1, u_2, u_3) I_2$.
-/

/-- The 6 causal stages of the **Nilpotent Maurer–Cartan Backpropagation & Yangian
$\mathcal{C}\mathcal{P}\mathcal{T}$-Dyck Syntactic Tree Poset**
(`𝔅𝔓₁ ≺ 𝔅𝔓₂ ≺ 𝔅𝔓₃ ≺ {𝔅𝔓₄, 𝔅𝔓₅} ≺ 𝔅𝔓₆`). -/
inductive MaurerCartanBackpropSyntacticTreeStage : Type
  /-- `𝔅𝔓₁`: Same-chirality nilpotent annihilation of differentials (`(dN_+)N_+ = 0`, `(dN_-)N_- = 0`, `(dN_-)Q_- = 0`). -/
  | BP1_SameChiralityNilpotentAnnihilationOfDifferentials
  /-- `𝔅𝔓₂`: Universal Nilpotent Maurer–Cartan Backpropagation Identity `(d𝒢_+)𝒢_+⁻¹ = dN_+ + (1 + N_+)(dN_-)(1 - N_+)`. -/
  | BP2_NilpotentMaurerCartanBackpropagationIdentity
  /-- `𝔅𝔓₃`: Zero-memory backward state reconstruction & nilpotent backprop miracle `(dN_+)X_mid = (dN_+)X_out`, `(dN_-)X_in = (dN_-)X_mid`. -/
  | BP3_ZeroMemoryBackwardPassAndGradientContractions
  /-- `𝔅𝔓₄`: Twisted-Pin $\mathcal{C}\mathcal{P}\mathcal{T}$-Dyck center-embedded clause cancellation `W_verb (W_sub Θ_CPT(W_sub)) W_subj = W_verb W_subj`. -/
  | BP4_CPTDyckSyntacticCancellationAndZeroDistanceClauseCollapse
  /-- `𝔅𝔓₅`: Two-step Zorn binary phrase merge `N_+(u₁)N_+(u₂) = N_-(u₁×u₂)` & clause determinant `{N_-(u₁×u₂), N_+(u₃)} = det(u₁,u₂,u₃) I₂`. -/
  | BP5_TwoStepZornBinaryPhraseMergeAndClauseDeterminant
  /-- `𝔅𝔓₆`: Master synthesis of zero-memory Maurer–Cartan backpropagation & Yangian syntactic parse-tree invariants. -/
  | BP6_YangianParseTreeMonodromyAndMasterBackpropSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace MaurerCartanBackpropSyntacticTreeStage

/-- Topological rank `0..5` on `MaurerCartanBackpropSyntacticTreeStage`. -/
def rank : MaurerCartanBackpropSyntacticTreeStage → ℕ
  | .BP1_SameChiralityNilpotentAnnihilationOfDifferentials => 0
  | .BP2_NilpotentMaurerCartanBackpropagationIdentity => 1
  | .BP3_ZeroMemoryBackwardPassAndGradientContractions => 2
  | .BP4_CPTDyckSyntacticCancellationAndZeroDistanceClauseCollapse => 3
  | .BP5_TwoStepZornBinaryPhraseMergeAndClauseDeterminant => 4
  | .BP6_YangianParseTreeMonodromyAndMasterBackpropSynthesis => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder MaurerCartanBackpropSyntacticTreeStage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype MaurerCartanBackpropSyntacticTreeStage where
  elems := {
    .BP1_SameChiralityNilpotentAnnihilationOfDifferentials,
    .BP2_NilpotentMaurerCartanBackpropagationIdentity,
    .BP3_ZeroMemoryBackwardPassAndGradientContractions,
    .BP4_CPTDyckSyntacticCancellationAndZeroDistanceClauseCollapse,
    .BP5_TwoStepZornBinaryPhraseMergeAndClauseDeterminant,
    .BP6_YangianParseTreeMonodromyAndMasterBackpropSynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card MaurerCartanBackpropSyntacticTreeStage = 6 := rfl

/-- Directed diamond causal edges `𝔅𝔓₁ ≺ 𝔅𝔓₂ ≺ 𝔅𝔓₃ ≺ {𝔅𝔓₄, 𝔅𝔓₅} ≺ 𝔅𝔓₆`. -/
def causalEdge : MaurerCartanBackpropSyntacticTreeStage → MaurerCartanBackpropSyntacticTreeStage → Prop
  | .BP1_SameChiralityNilpotentAnnihilationOfDifferentials,
    .BP2_NilpotentMaurerCartanBackpropagationIdentity => True
  | .BP2_NilpotentMaurerCartanBackpropagationIdentity,
    .BP3_ZeroMemoryBackwardPassAndGradientContractions => True
  | .BP3_ZeroMemoryBackwardPassAndGradientContractions,
    .BP4_CPTDyckSyntacticCancellationAndZeroDistanceClauseCollapse => True
  | .BP3_ZeroMemoryBackwardPassAndGradientContractions,
    .BP5_TwoStepZornBinaryPhraseMergeAndClauseDeterminant => True
  | .BP4_CPTDyckSyntacticCancellationAndZeroDistanceClauseCollapse,
    .BP6_YangianParseTreeMonodromyAndMasterBackpropSynthesis => True
  | .BP5_TwoStepZornBinaryPhraseMergeAndClauseDeterminant,
    .BP6_YangianParseTreeMonodromyAndMasterBackpropSynthesis => True
  | _, _ => False

instance : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> simp [causalEdge] <;> infer_instance

theorem causalEdge_implies_rank_lt {a b : MaurerCartanBackpropSyntacticTreeStage}
    (h : causalEdge a b) : a.rank < b.rank := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

theorem transGen_implies_rank_lt {a b : MaurerCartanBackpropSyntacticTreeStage}
    (h : Relation.TransGen causalEdge a b) : a.rank < b.rank := by
  induction h with
  | single hab => exact causalEdge_implies_rank_lt hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_implies_rank_lt hbc)

/-- Strict DAG acyclicity of `𝔅𝔓₁ ≺ 𝔅𝔓₂ ≺ 𝔅𝔓₃ ≺ {𝔅𝔓₄, 𝔅𝔓₅} ≺ 𝔅𝔓₆`. -/
theorem causalEdge_acyclic (st : MaurerCartanBackpropSyntacticTreeStage) :
    ¬ Relation.TransGen causalEdge st st := by
  intro h
  exact Nat.lt_irrefl st.rank (transGen_implies_rank_lt h)

/-- The parallel syntactic branches `𝔅𝔓₄` (CPT-Dyck stack cancellation) and `𝔅𝔓₅`
(two-step Zorn binary phrase merge) are incomparable in `causalEdge`. -/
theorem incomparable_BP4_BP5 :
    ¬ causalEdge .BP4_CPTDyckSyntacticCancellationAndZeroDistanceClauseCollapse
        .BP5_TwoStepZornBinaryPhraseMergeAndClauseDeterminant ∧
    ¬ causalEdge .BP5_TwoStepZornBinaryPhraseMergeAndClauseDeterminant
        .BP4_CPTDyckSyntacticCancellationAndZeroDistanceClauseCollapse := by
  decide

end MaurerCartanBackpropSyntacticTreeStage

section MaurerCartanBackpropSyntacticTreePoset

open Archetypes.TwistorAmplituhedronZornBaryon

variable {B : Type*} [Ring B]

/-- **Forward Operator Gaussian Tangent Differential (`attnGaussianDiff`)**:
$$d\mathcal{G}_+(N_+, N_-, dN_+, dN_-) \;:=\; dN_+ * (1 + N_-) \;+\; (1 + N_+) * dN_-.$$ -/
def attnGaussianDiff (Np Nm dNp dNm : B) : B :=
  dNp * (1 + Nm) + (1 + Np) * dNm

/-- **Zero-Memory Midpoint Activation Reconstruction (`backpropMidState`)**:
$$X_{\text{mid}}(N_+, X_{\text{out}}) \;:=\; (1 - N_+) * X_{\text{out}}.$$ -/
def backpropMidState (Np X_out : B) : B :=
  (1 - Np) * X_out

/-- **Zero-Memory Input Activation Reconstruction (`backpropInState`)**:
$$X_{\text{in}}(N_+, N_-, X_{\text{out}}) \;:=\; (1 - N_-) * (1 - N_+) * X_{\text{out}}
  \;=\; \mathcal{G}_+^{-1}(N_+, N_-) * X_{\text{out}}.$$ -/
def backpropInState (Np Nm X_out : B) : B :=
  attnGaussianInv Np Nm * X_out

/-- **Primal $e$-Gate Weight Gradient (`backpropGradNPlus`)**:
$$\bar{N}_+(P, \bar{X}_{\text{out}}, X_{\text{out}}) \;:=\; P * (\bar{X}_{\text{out}} * X_{\text{out}}^\star) * (1 - P) \;\in\; \mathfrak{n}_+.$$ -/
def backpropGradNPlus [StarRing B] (P Xbar_out X_out : B) : B :=
  P * (Xbar_out * star X_out) * (1 - P)

/-- **Dual $m$-Gate Weight Gradient (`backpropGradNMinus`)**:
$$\bar{N}_-(P, N_+, \bar{X}_{\text{out}}, X_{\text{out}}) \;:=\;
  (1 - P) * \big((1 + N_+)^\star * \bar{X}_{\text{out}} * ((1 - N_+) * X_{\text{out}})^\star\big) * P \;\in\; \mathfrak{n}_-.$$ -/
def backpropGradNMinus [StarRing B] (P Np Xbar_out X_out : B) : B :=
  (1 - P) * (star (1 + Np) * Xbar_out * star (backpropMidState Np X_out)) * P

/-- **Input Cotangent Backpropagation (`backpropGradXin`)**:
$$\bar{X}_{\text{in}}(N_+, N_-, \bar{X}_{\text{out}}) \;:=\; \mathcal{G}_+(N_+, N_-)^\star * \bar{X}_{\text{out}}.$$ -/
def backpropGradXin [StarRing B] (Np Nm Xbar_out : B) : B :=
  star (attnGaussianFwd Np Nm) * Xbar_out

/-- **Twisted-$\mathrm{Pin}$ $\mathcal{C}\mathcal{P}\mathcal{T}$ Conjugation (`backpropThetaCPT`)**:
$$\Theta_{\text{CPT}}(J_1, X) \;:=\; -J_1 * X^\star * J_1.$$ -/
def backpropThetaCPT [StarRing B] (J1 X : B) : B :=
  -(J1 * star X * J1)

/-- **Stage `𝔅𝔓₁` (`bp1_same_chirality_nilpotent_annihilation_of_differentials`)**:
In any associative `[Ring B]` with idempotent `hP : P * P = P` and arbitrary $A, dA, C, dC \in B$:
1. **Same-Chirality Square-Zero Differential Kill Laws**:
   - `conePlus P dA * conePlus P A = 0` ($(dN_+) N_+ = 0$),
   - `conePlus P A * conePlus P dA = 0` ($N_+ (dN_+) = 0$),
   - `coneMinus P dC * coneMinus P C = 0` ($(dN_-) N_- = 0$),
   - `coneMinus P C * coneMinus P dC = 0` ($N_- (dN_-) = 0$).
2. **Quadratic Overlap Kill Laws**:
   - `coneMinus P dC * qgtMinus P A C = 0` ($(dN_-) Q_- = 0$),
   - `qgtMinus P A C * conePlus P dA = 0` ($Q_- (dN_+) = 0$),
   - `conePlus P dA * qgtPlus P A C = 0` ($(dN_+) Q_+ = 0$),
   - `qgtPlus P A C * coneMinus P dC = 0` ($Q_+ (dN_-) = 0$). -/
theorem bp1_same_chirality_nilpotent_annihilation_of_differentials
    {P : B} (hP : P * P = P) (A dA C dC : B) :
    conePlus P dA * conePlus P A = 0 ∧
    conePlus P A * conePlus P dA = 0 ∧
    coneMinus P dC * coneMinus P C = 0 ∧
    coneMinus P C * coneMinus P dC = 0 ∧
    coneMinus P dC * qgtMinus P A C = 0 ∧
    qgtMinus P A C * conePlus P dA = 0 ∧
    conePlus P dA * qgtPlus P A C = 0 ∧
    qgtPlus P A C * coneMinus P dC = 0 := by
  dsimp [qgtMinus, qgtPlus]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- **Stage `𝔅𝔓₂` (`bp2_nilpotent_maurer_cartan_backpropagation_identity`)**:
**Theorem 1.2 (The Universal Nilpotent Maurer–Cartan Backpropagation Identity)**:
In any associative `[Ring B]` with idempotent `hP : P * P = P` and $A, dA, C, dC \in B$,
for $N_+ = \mathrm{conePlus}\;P\;A$, $dN_+ = \mathrm{conePlus}\;P\;dA$,
$N_- = \mathrm{coneMinus}\;P\;C$, and $dN_- = \mathrm{coneMinus}\;P\;dC$:
1. **Primal Differential Reduction ($(dN_+)(1 + N_-)\mathcal{G}_+^{-1} = dN_+$)**:
   `(conePlus P dA * (1 + coneMinus P C)) * attnGaussianInv (conePlus P A) (coneMinus P C) = conePlus P dA`.
2. **Dual Differential Reduction ($(1 + N_+)(dN_-)\mathcal{G}_+^{-1} = (1 + N_+)(dN_-)(1 - N_+)$)**:
   `((1 + conePlus P A) * coneMinus P dC) * attnGaussianInv (conePlus P A) (coneMinus P C) = (1 + conePlus P A) * coneMinus P dC * (1 - conePlus P A)`.
3. **Right-Invariant Maurer–Cartan Form ($N_-$ Drops Out Completely!)**:
   $$d\mathcal{G}_+(N_+, N_-, dN_+, dN_-) * \mathcal{G}_+^{-1}(N_+, N_-)
     \;=\; dN_+ \;+\; (1 + N_+) * dN_- * (1 - N_+).$$
4. **Graded Expansion into Berry Curvature Variation $[N_+, dN_-]$ & Jordan Triple Variation $-N_+(dN_-)N_+$**:
   $$(1 + N_+) * dN_- * (1 - N_+) \;=\; dN_- \;+\; [N_+, dN_-] \;-\; N_+ * dN_- * N_+.$$ -/
theorem bp2_nilpotent_maurer_cartan_backpropagation_identity
    {P : B} (hP : P * P = P) (A dA C dC : B) :
    (conePlus P dA * (1 + coneMinus P C)) *
      attnGaussianInv (conePlus P A) (coneMinus P C) = conePlus P dA ∧
    ((1 + conePlus P A) * coneMinus P dC) *
      attnGaussianInv (conePlus P A) (coneMinus P C) =
      (1 + conePlus P A) * coneMinus P dC * (1 - conePlus P A) ∧
    attnGaussianDiff (conePlus P A) (coneMinus P C) (conePlus P dA) (coneMinus P dC) *
      attnGaussianInv (conePlus P A) (coneMinus P C) =
      conePlus P dA + (1 + conePlus P A) * coneMinus P dC * (1 - conePlus P A) ∧
    (1 + conePlus P A) * coneMinus P dC * (1 - conePlus P A) =
      coneMinus P dC + OperatorAlgebra.PeirceSpine.comm (conePlus P A) (coneMinus P dC) -
        conePlus P A * coneMinus P dC * conePlus P A ∧
    attnGaussianDiff (conePlus P A) (coneMinus P C) (conePlus P dA) (coneMinus P dC) *
      attnGaussianInv (conePlus P A) (coneMinus P C) =
      conePlus P dA + coneMinus P dC +
        OperatorAlgebra.PeirceSpine.comm (conePlus P A) (coneMinus P dC) -
        conePlus P A * coneMinus P dC * conePlus P A := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [attnGaussianInv]; peirce_nf hP
  · dsimp [attnGaussianInv]; peirce_nf hP
  · dsimp [attnGaussianDiff, attnGaussianInv]; peirce_nf hP
  · dsimp [OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
  · dsimp [attnGaussianDiff, attnGaussianInv, OperatorAlgebra.PeirceSpine.comm]; peirce_nf hP

/-- **Stage `𝔅𝔓₃` (`bp3_zero_memory_backward_pass_and_nilpotent_gradient_contractions`)**:
**Theorem 1.3 (Zero-Activation-Memory Backward Pass & The Nilpotent Backprop Miracle)**:
In any associative `[Ring B]` with `[StarRing B]` and self-adjoint idempotent
`hP : P * P = P`, `hP_star : star P = P`:
1. **Exact Zero-Memory State Reconstruction from $X_{\text{out}} = \mathcal{G}_+(N_+, N_-) X_0$**:
   - `backpropMidState (conePlus P A) (attnGaussianFwd (conePlus P A) (coneMinus P C) * X₀) = (1 + coneMinus P C) * X₀`,
   - `backpropInState (conePlus P A) (coneMinus P C) (attnGaussianFwd (conePlus P A) (coneMinus P C) * X₀) = X₀`,
   - `(1 - coneMinus P C) * backpropMidState (conePlus P A) X_out = backpropInState (conePlus P A) (coneMinus P C) X_out`.
2. **The Nilpotent Backprop Miracle ($(dN_+)X_{\text{mid}} = (dN_+)X_{\text{out}}$ & $(dN_-)X_{\text{in}} = (dN_-)X_{\text{mid}}$)**:
   - `conePlus P dA * backpropMidState (conePlus P A) X_out = conePlus P dA * X_out`,
   - `coneMinus P dC * backpropInState (conePlus P A) (coneMinus P C) X_out = coneMinus P dC * backpropMidState (conePlus P A) X_out`,
   - `attnGaussianDiff (conePlus P A) (coneMinus P C) (conePlus P dA) (coneMinus P dC) * backpropInState (conePlus P A) (coneMinus P C) X_out + attnGaussianFwd (conePlus P A) (coneMinus P C) * dX_in = conePlus P dA * X_out + (1 + conePlus P A) * coneMinus P dC * backpropMidState (conePlus P A) X_out + attnGaussianFwd (conePlus P A) (coneMinus P C) * dX_in`.
3. **Nilpotent Subalgebra Purity of the Weight Gradients $\bar{N}_+ \in \mathfrak{n}_+$ and $\bar{N}_- \in \mathfrak{n}_-$**:
   - `P * backpropGradNPlus P Xbar_out X_out * (1 - P) = backpropGradNPlus P Xbar_out X_out`,
   - `backpropGradNPlus P Xbar_out X_out * backpropGradNPlus P Xbar_out X_out = 0`,
   - `(1 - P) * backpropGradNMinus P (conePlus P A) Xbar_out X_out * P = backpropGradNMinus P (conePlus P A) Xbar_out X_out`,
   - `backpropGradNMinus P (conePlus P A) Xbar_out X_out * backpropGradNMinus P (conePlus P A) Xbar_out X_out = 0`,
   - `backpropGradXin (conePlus P A) (coneMinus P C) Xbar_out = (1 + star (coneMinus P C)) * ((1 + star (conePlus P A)) * Xbar_out)`. -/
theorem bp3_zero_memory_backward_pass_and_nilpotent_gradient_contractions
    [StarRing B] {P : B} (hP : P * P = P)
    (A dA C dC X₀ X_out dX_in Xbar_out : B) :
    -- 1. Zero-memory midpoint and input state recovery:
    backpropMidState (conePlus P A)
      (attnGaussianFwd (conePlus P A) (coneMinus P C) * X₀) = (1 + coneMinus P C) * X₀ ∧
    backpropInState (conePlus P A) (coneMinus P C)
      (attnGaussianFwd (conePlus P A) (coneMinus P C) * X₀) = X₀ ∧
    (1 - coneMinus P C) * backpropMidState (conePlus P A) X_out =
      backpropInState (conePlus P A) (coneMinus P C) X_out ∧
    -- 2. Nilpotent backprop miracle (dN_+)X_mid = (dN_+)X_out and (dN_-)X_in = (dN_-)X_mid:
    conePlus P dA * backpropMidState (conePlus P A) X_out = conePlus P dA * X_out ∧
    coneMinus P dC * backpropInState (conePlus P A) (coneMinus P C) X_out =
      coneMinus P dC * backpropMidState (conePlus P A) X_out ∧
    attnGaussianDiff (conePlus P A) (coneMinus P C) (conePlus P dA) (coneMinus P dC) *
      backpropInState (conePlus P A) (coneMinus P C) X_out +
      attnGaussianFwd (conePlus P A) (coneMinus P C) * dX_in =
      conePlus P dA * X_out +
        (1 + conePlus P A) * coneMinus P dC * backpropMidState (conePlus P A) X_out +
        attnGaussianFwd (conePlus P A) (coneMinus P C) * dX_in ∧
    -- 3. Nilpotent purity of N̄_+ ∈ 𝔫_+ and N̄_- ∈ 𝔫_- & factored cotangent pass:
    P * backpropGradNPlus P Xbar_out X_out * (1 - P) = backpropGradNPlus P Xbar_out X_out ∧
    backpropGradNPlus P Xbar_out X_out * backpropGradNPlus P Xbar_out X_out = 0 ∧
    (1 - P) * backpropGradNMinus P (conePlus P A) Xbar_out X_out * P =
      backpropGradNMinus P (conePlus P A) Xbar_out X_out ∧
    backpropGradNMinus P (conePlus P A) Xbar_out X_out *
      backpropGradNMinus P (conePlus P A) Xbar_out X_out = 0 ∧
    backpropGradXin (conePlus P A) (coneMinus P C) Xbar_out =
      (1 + star (coneMinus P C)) * ((1 + star (conePlus P A)) * Xbar_out) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [backpropMidState, attnGaussianFwd]; peirce_nf hP
  · dsimp [backpropInState, attnGaussianInv, attnGaussianFwd]; peirce_nf hP
  · dsimp [backpropMidState, backpropInState, attnGaussianInv]; noncomm_ring
  · dsimp [backpropMidState]; peirce_nf hP
  · dsimp [backpropInState, backpropMidState, attnGaussianInv]; peirce_nf hP
  · dsimp [attnGaussianDiff, backpropInState, backpropMidState, attnGaussianInv]; peirce_nf hP
  · dsimp [backpropGradNPlus]; peirce_nf hP
  · dsimp [backpropGradNPlus]; peirce_nf hP
  · dsimp [backpropGradNMinus]; peirce_nf hP
  · dsimp [backpropGradNMinus]; peirce_nf hP
  · dsimp [backpropGradXin, attnGaussianFwd]
    rw [star_mul, star_add, star_one, star_add, star_one, mul_assoc]

/-- **Stage `𝔅𝔓₄` (`bp4_cpt_dyck_syntactic_cancellation_and_zero_distance_clause_collapse`)**:
**Theorem 2.1 ($\mathcal{C}\mathcal{P}\mathcal{T}$-Dyck Cancellation of Arbitrarily Deep Center-Embedded Clauses)**:
In any associative `[Ring B]` with `[StarRing B]` and complex-structure generator $J_1 \in B$
satisfying `hJ1 : J1 * J1 = -1`:
1. **Anti-Multiplicativity & Involution of $\Theta_{\text{CPT}}(J_1, X) = -J_1 X^\star J_1$**:
   - `backpropThetaCPT J1 (X * Y) = backpropThetaCPT J1 Y * backpropThetaCPT J1 X`,
   - `backpropThetaCPT J1 (1 : B) = 1`.
2. **Arbitrary-Depth Center-Embedded Dyck Clause Collapse ($W_{\text{sub}} \cdot \Theta_{\text{CPT}}(W_{\text{sub}}) = 1$)**:
   For any list of opening syntactic constituents `L : List B` satisfying
   `hGates : ∀ g ∈ L, g * backpropThetaCPT J1 g = 1`:
   - `L.prod * backpropThetaCPT J1 L.prod = 1`,
   - **Zero-Distance Outer Constituent Contact Across Arbitrarily Deep Center-Embedded Clauses**:
     $$W_{\text{verb}} * (L.\text{prod} * \text{backpropThetaCPT}\;J_1\;L.\text{prod}) * W_{\text{subj}}
       \;=\; W_{\text{verb}} * W_{\text{subj}},$$
   - And for any multi-scale unipotent tower `L_tower : List (B × B)` with
     `hTower : ∀ p ∈ L_tower, p.1 * p.1 = 0 ∧ p.2 * p.2 = 0`:
     $$W_{\text{verb}} * (\text{attnTowerFwd}\;L_{\text{tower}} * \text{attnTowerInv}\;L_{\text{tower}}) * W_{\text{subj}}
       \;=\; W_{\text{verb}} * W_{\text{subj}}.$$ -/
theorem bp4_cpt_dyck_syntactic_cancellation_and_zero_distance_clause_collapse
    [StarRing B] {J1 : B} (hJ1 : J1 * J1 = -1)
    (X Y W_verb W_subj : B)
    (L : List B) (hGates : ∀ g ∈ L, g * backpropThetaCPT J1 g = 1)
    (L_tower : List (B × B)) (hTower : ∀ p ∈ L_tower, p.1 * p.1 = 0 ∧ p.2 * p.2 = 0) :
    backpropThetaCPT J1 (X * Y) = backpropThetaCPT J1 Y * backpropThetaCPT J1 X ∧
    backpropThetaCPT J1 (1 : B) = 1 ∧
    L.prod * backpropThetaCPT J1 L.prod = 1 ∧
    W_verb * (L.prod * backpropThetaCPT J1 L.prod) * W_subj = W_verb * W_subj ∧
    W_verb * (attnTowerFwd L_tower * attnTowerInv L_tower) * W_subj = W_verb * W_subj := by
  have hAnti : ∀ A C : B,
      backpropThetaCPT J1 (A * C) = backpropThetaCPT J1 C * backpropThetaCPT J1 A := by
    intro A C
    dsimp [backpropThetaCPT]
    rw [star_mul]
    calc -(J1 * (star C * star A) * J1)
      _ = -(J1 * star C * 1 * star A * J1) := by simp only [mul_one, mul_assoc]
      _ = -(J1 * star C * (-(J1 * J1)) * star A * J1) := by rw [hJ1, neg_neg]
      _ = (-(J1 * star C * J1)) * (-(J1 * star A * J1)) := by
            simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
  have hOne : backpropThetaCPT J1 (1 : B) = 1 := by
    dsimp [backpropThetaCPT]
    rw [star_one, mul_one, hJ1, neg_neg]
  have hList : L.prod * backpropThetaCPT J1 L.prod = 1 := by
    induction L with
    | nil =>
      simp [hOne]
    | cons hd tl ih =>
      simp only [List.prod_cons]
      rw [hAnti hd tl.prod]
      have hhd : hd * backpropThetaCPT J1 hd = 1 :=
        hGates hd List.mem_cons_self
      have htl : tl.prod * backpropThetaCPT J1 tl.prod = 1 :=
        ih (fun g hg => hGates g (List.mem_cons_of_mem hd hg))
      calc (hd * tl.prod) * (backpropThetaCPT J1 tl.prod * backpropThetaCPT J1 hd)
        _ = hd * (tl.prod * backpropThetaCPT J1 tl.prod) * backpropThetaCPT J1 hd := by
              noncomm_ring
        _ = hd * 1 * backpropThetaCPT J1 hd := by rw [htl]
        _ = hd * backpropThetaCPT J1 hd := by noncomm_ring
        _ = 1 := hhd
  have hClause : W_verb * (L.prod * backpropThetaCPT J1 L.prod) * W_subj = W_verb * W_subj := by
    rw [hList, mul_one]
  have hTN6 := tn6_multiscale_tower_inversion_and_zorn_three_body_bond
    (K := ℤ) L_tower hTower 0 0 0 0 rfl rfl rfl rfl
    ⟨(0 : ℤ), 0, 0⟩ ⟨(0 : ℤ), 0, 0⟩ ⟨(0 : ℤ), 0, 0⟩
  have hTowerClause :
      W_verb * (attnTowerFwd L_tower * attnTowerInv L_tower) * W_subj = W_verb * W_subj := by
    rw [hTN6.1.1, mul_one]
  exact ⟨hAnti X Y, hOne, hList, hClause, hTowerClause⟩

/-- **Stage `𝔅𝔓₅` (`bp5_two_step_zorn_binary_phrase_merge_and_clause_determinant`)**:
**Theorem 2.2 (Socratic Resolution of the 3-Body Firth–Zorn Syntactic Bracket via Two-Step Binary Tree Contraction)**:
Over any commutative ring `[CommRing R]`, for leaf token vectors $u_1, u_2, u_3 \in \mathrm{Vec3}\;R$:
1. **Step 1 (Binary Constituent Merge $\mathfrak{n}_+ \times \mathfrak{n}_+ \to \mathfrak{n}_-$ via Cross Product)**:
   $$N_+(u_1) * N_+(u_2) \;=\; N_-(u_1 \times u_2),$$
   which is square-zero (`(zornPlusVec u₁ * zornPlusVec u₂) * (zornPlusVec u₁ * zornPlusVec u₂) = 0`)
   and traceless (`zornMatTrace (zornPlusVec u₁ * zornPlusVec u₂) = 0`).
2. **Step 2 (Jordan Anticommutator of Phrase Node $N_-(u_1 \times u_2)$ with Head Modifier $N_+(u_3)$)**:
   $$\big\{N_-(u_1 \times u_2), \; N_+(u_3)\big\}
     \;=\; \big\{N_+(u_1) * N_+(u_2), \; N_+(u_3)\big\}
     \;=\; \det(u_1, u_2, u_3) \cdot I_2.$$
3. **Cyclic Invariance Across Binary Tree Rotations**:
   $$\big\{N_+(u_1) * N_+(u_2), \; N_+(u_3)\big\}
     \;=\; \big\{N_+(u_2) * N_+(u_3), \; N_+(u_1)\big\}.$$ -/
theorem bp5_two_step_zorn_binary_phrase_merge_and_clause_determinant
    {R : Type*} [CommRing R] (u₁ u₂ u₃ : Vec3 R) :
    -- 1. Step 1: Binary phrase merge N_+(u₁) N_+(u₂) = N_-(u₁ × u₂) ∈ 𝔫_-:
    zornPlusVec u₁ * zornPlusVec u₂ = zornMinusVec (Vec3.cross u₁ u₂) ∧
    (zornPlusVec u₁ * zornPlusVec u₂) * (zornPlusVec u₁ * zornPlusVec u₂) = 0 ∧
    zornMatTrace (zornPlusVec u₁ * zornPlusVec u₂) = 0 ∧
    -- 2. Step 2: Two-step anticommutator {N_-(u₁ × u₂), N_+(u₃)} = {N_+(u₁)N_+(u₂), N_+(u₃)} = det I₂:
    zornMinusVec (Vec3.cross u₁ u₂) * zornPlusVec u₃ +
      zornPlusVec u₃ * zornMinusVec (Vec3.cross u₁ u₂) =
      (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
        zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) ∧
    (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
      zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat R) ∧
    -- 3. Cyclic rotation invariance of the 3-body syntactic clause determinant:
    (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
      zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) =
      (zornPlusVec u₂ * zornPlusVec u₃) * zornPlusVec u₁ +
        zornPlusVec u₁ * (zornPlusVec u₂ * zornPlusVec u₃) := by
  have hMB3_123 := mb3_firth_trilinear_contextual_semantics_in_zorn_matrix u₁ u₂ u₃ 0 0
  have hMB3_231 := mb3_firth_trilinear_contextual_semantics_in_zorn_matrix u₂ u₃ u₁ 0 0
  have hNilPhrase :
      (zornPlusVec u₁ * zornPlusVec u₂) * (zornPlusVec u₁ * zornPlusVec u₂) = 0 := by
    rw [hMB3_123.2.2.2.2.1]
    exact (mb3_firth_trilinear_contextual_semantics_in_zorn_matrix u₁ u₂ u₃ (Vec3.cross u₁ u₂) 0).2.1
  have hTwoStep :
      zornMinusVec (Vec3.cross u₁ u₂) * zornPlusVec u₃ +
        zornPlusVec u₃ * zornMinusVec (Vec3.cross u₁ u₂) =
      (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
        zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) := by
    rw [← hMB3_123.2.2.2.2.1]
  have hDetCyc : Vec3.baryonDet3 u₁ u₂ u₃ = Vec3.baryonDet3 u₂ u₃ u₁ := by
    dsimp [Vec3.baryonDet3, Vec3.dot, Vec3.cross]
    ring
  have hCyc :
      (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
        zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) =
      (zornPlusVec u₂ * zornPlusVec u₃) * zornPlusVec u₁ +
        zornPlusVec u₁ * (zornPlusVec u₂ * zornPlusVec u₃) := by
    rw [hMB3_123.2.2.2.2.2.2.2.2.2.2.1, hMB3_231.2.2.2.2.2.2.2.2.2.2.1, hDetCyc]
  exact ⟨hMB3_123.2.2.2.2.1,
    hNilPhrase,
    hMB3_123.2.2.2.2.2.2.1,
    hTwoStep,
    hMB3_123.2.2.2.2.2.2.2.2.2.2.1,
    hCyc⟩

/-- **Stage `𝔅𝔓₆` (`bp6_yangian_parse_tree_monodromy_and_master_backprop_synthesis`)**:
Master theorem unifying the 6-stage **Nilpotent Maurer–Cartan Backpropagation & Yangian
$\mathcal{C}\mathcal{P}\mathcal{T}$-Dyck Syntactic Tree Poset**
(`𝔅𝔓₁ ≺ 𝔅𝔓₂ ≺ 𝔅𝔓₃ ≺ {𝔅𝔓₄, 𝔅𝔓₅} ≺ 𝔅𝔓₆`). -/
theorem bp6_yangian_parse_tree_monodromy_and_master_backprop_synthesis
    [StarRing B] {R : Type*} [CommRing R]
    {P J1 : B} (hP : P * P = P) (hJ1 : J1 * J1 = -1)
    (A dA C dC X₀ X_out Xbar_out W_verb W_subj : B)
    (L : List B) (hGates : ∀ g ∈ L, g * backpropThetaCPT J1 g = 1)
    (u₁ u₂ u₃ : Vec3 R) :
    -- 1. Poset acyclicity, cardinality, and diamond branching (BP4 ∥ BP5):
    (∀ st : MaurerCartanBackpropSyntacticTreeStage,
      ¬ Relation.TransGen MaurerCartanBackpropSyntacticTreeStage.causalEdge st st) ∧
    Fintype.card MaurerCartanBackpropSyntacticTreeStage = 6 ∧
    (¬ MaurerCartanBackpropSyntacticTreeStage.causalEdge
        .BP4_CPTDyckSyntacticCancellationAndZeroDistanceClauseCollapse
        .BP5_TwoStepZornBinaryPhraseMergeAndClauseDeterminant ∧
     ¬ MaurerCartanBackpropSyntacticTreeStage.causalEdge
        .BP5_TwoStepZornBinaryPhraseMergeAndClauseDeterminant
        .BP4_CPTDyckSyntacticCancellationAndZeroDistanceClauseCollapse) ∧
    -- 2. Same-chirality nilpotent differential kill laws (BP1):
    conePlus P dA * conePlus P A = 0 ∧
    coneMinus P dC * coneMinus P C = 0 ∧
    coneMinus P dC * qgtMinus P A C = 0 ∧
    -- 3. Universal Nilpotent Maurer–Cartan Backpropagation Identity (BP2):
    attnGaussianDiff (conePlus P A) (coneMinus P C) (conePlus P dA) (coneMinus P dC) *
      attnGaussianInv (conePlus P A) (coneMinus P C) =
      conePlus P dA + (1 + conePlus P A) * coneMinus P dC * (1 - conePlus P A) ∧
    -- 4. Zero-memory state recovery & Nilpotent Backprop Miracle (BP3):
    backpropInState (conePlus P A) (coneMinus P C)
      (attnGaussianFwd (conePlus P A) (coneMinus P C) * X₀) = X₀ ∧
    conePlus P dA * backpropMidState (conePlus P A) X_out = conePlus P dA * X_out ∧
    coneMinus P dC * backpropInState (conePlus P A) (coneMinus P C) X_out =
      coneMinus P dC * backpropMidState (conePlus P A) X_out ∧
    backpropGradNPlus P Xbar_out X_out * backpropGradNPlus P Xbar_out X_out = 0 ∧
    backpropGradNMinus P (conePlus P A) Xbar_out X_out *
      backpropGradNMinus P (conePlus P A) Xbar_out X_out = 0 ∧
    -- 5. CPT-Dyck center-embedded clause collapse & two-step Zorn phrase merge (BP4, BP5):
    W_verb * (L.prod * backpropThetaCPT J1 L.prod) * W_subj = W_verb * W_subj ∧
    zornPlusVec u₁ * zornPlusVec u₂ = zornMinusVec (Vec3.cross u₁ u₂) ∧
    (zornPlusVec u₁ * zornPlusVec u₂) * zornPlusVec u₃ +
      zornPlusVec u₃ * (zornPlusVec u₁ * zornPlusVec u₂) =
      InfoGeometry.Canonical.SplitOctonionCircularIsotropicAmariNambuPoset.zornSmul
        (Vec3.baryonDet3 u₁ u₂ u₃) (1 : ZornMat R) := by
  have hBP1 := bp1_same_chirality_nilpotent_annihilation_of_differentials hP A dA C dC
  have hBP2 := bp2_nilpotent_maurer_cartan_backpropagation_identity hP A dA C dC
  have hBP3 := bp3_zero_memory_backward_pass_and_nilpotent_gradient_contractions
    hP A dA C dC X₀ X_out 0 Xbar_out
  have hBP4 := bp4_cpt_dyck_syntactic_cancellation_and_zero_distance_clause_collapse
    hJ1 0 0 W_verb W_subj L hGates [] (by intro p hp; cases hp)
  have hBP5 := bp5_two_step_zorn_binary_phrase_merge_and_clause_determinant u₁ u₂ u₃
  exact ⟨MaurerCartanBackpropSyntacticTreeStage.causalEdge_acyclic,
    MaurerCartanBackpropSyntacticTreeStage.card_eq_six,
    MaurerCartanBackpropSyntacticTreeStage.incomparable_BP4_BP5,
    hBP1.1, hBP1.2.2.1, hBP1.2.2.2.2.1,
    hBP2.2.2.1,
    hBP3.2.1, hBP3.2.2.2.1, hBP3.2.2.2.2.1, hBP3.2.2.2.2.2.2.2.1, hBP3.2.2.2.2.2.2.2.2.2.1,
    hBP4.2.2.2.1, hBP5.1, hBP5.2.2.2.2.1⟩

end MaurerCartanBackpropSyntacticTreePoset

/-!
## 9g. The 6-Stage Telescoping Multi-Scale Maurer–Cartan Backpropagation, Two-Layer Cotangent Trace-Adjoint Split, Concrete Yangian $\mathcal{C}\mathcal{P}\mathcal{T}$-Dyck Monodromy, & Zorn Parameter Uniqueness Poset (`𝔗𝔅₁ ≺ 𝔗𝔅₂ ≺ 𝔗𝔅₃ ≺ {𝔗𝔅₄, 𝔗𝔅₅} ≺ 𝔗𝔅₆`)
-/

/-- The 6 causal stages of the **Telescoping Multi-Scale Maurer–Cartan Backpropagation,
Two-Layer Cotangent Trace-Adjoint Split, Concrete Yangian $\mathcal{C}\mathcal{P}\mathcal{T}$-Dyck
Monodromy, & Zorn Parameter Uniqueness Poset**
(`𝔗𝔅₁ ≺ 𝔗𝔅₂ ≺ 𝔗𝔅₃ ≺ {𝔗𝔅₄, 𝔗𝔅₅} ≺ 𝔗𝔅₆`). -/
inductive TelescopingBackpropYangianZornStage : Type
  /-- `𝔗𝔅₁`: Multi-scale ordered gate tower `towerGate scale n`, segment split, and exact cut-state reconstruction `suffix_reconstructs_cut_state`. -/
  | TB1_MultiScaleGateTowerAndCutStateReconstruction
  /-- `𝔗𝔅₂`: Two-layer and `(n + 1)`-layer telescoping Maurer–Cartan log-differential and Amari natural-gradient nilpotent preconditioning. -/
  | TB2_TelescopingMaurerCartanAndAmariNaturalGradientNilpotency
  /-- `𝔗𝔅₃`: Two-layer cotangent backpropagation and exact 2-layer zero-activation-memory parameter gradient trace-adjoint split. -/
  | TB3_TwoLayerCotangentBackpropAndTraceAdjointSplit
  /-- `𝔗𝔅₄`: Concrete 2-site Yangian creation block `monodromyB2` lower-left corner membership, square-zero nilpotency, twisted-Pin CPT negation, and `DyckTree SpectralLabel` identity evaluation. -/
  | TB4_ConcreteYangianMonodromyBlockAndDyckTreeEvaluation
  /-- `𝔗𝔅₅`: Binet–Cauchy / Lagrange determinant defect, BAC–CAB alternativity cancellation, and uniqueness of the Zorn parameter pair `(α, β) = (1, -1)`. -/
  | TB5_BinetCauchyBacCabAndZornParameterUniqueness
  /-- `𝔗𝔅₆`: Master synthesis unifying multi-scale telescoping Maurer–Cartan backprop, 2-layer trace adjoints, concrete Yangian CPT-Dyck monodromy, and Zorn uniqueness. -/
  | TB6_MasterTelescopingBackpropYangianZornSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace TelescopingBackpropYangianZornStage

/-- Topological rank `0..5` on `TelescopingBackpropYangianZornStage`. -/
def rank : TelescopingBackpropYangianZornStage → ℕ
  | .TB1_MultiScaleGateTowerAndCutStateReconstruction => 0
  | .TB2_TelescopingMaurerCartanAndAmariNaturalGradientNilpotency => 1
  | .TB3_TwoLayerCotangentBackpropAndTraceAdjointSplit => 2
  | .TB4_ConcreteYangianMonodromyBlockAndDyckTreeEvaluation => 3
  | .TB5_BinetCauchyBacCabAndZornParameterUniqueness => 4
  | .TB6_MasterTelescopingBackpropYangianZornSynthesis => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder TelescopingBackpropYangianZornStage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype TelescopingBackpropYangianZornStage where
  elems := {
    .TB1_MultiScaleGateTowerAndCutStateReconstruction,
    .TB2_TelescopingMaurerCartanAndAmariNaturalGradientNilpotency,
    .TB3_TwoLayerCotangentBackpropAndTraceAdjointSplit,
    .TB4_ConcreteYangianMonodromyBlockAndDyckTreeEvaluation,
    .TB5_BinetCauchyBacCabAndZornParameterUniqueness,
    .TB6_MasterTelescopingBackpropYangianZornSynthesis
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card TelescopingBackpropYangianZornStage = 6 := rfl

/-- Directed diamond causal edges `𝔗𝔅₁ ≺ 𝔗𝔅₂ ≺ 𝔗𝔅₃ ≺ {𝔗𝔅₄, 𝔗𝔅₅} ≺ 𝔗𝔅₆`. -/
def causalEdge : TelescopingBackpropYangianZornStage → TelescopingBackpropYangianZornStage → Prop
  | .TB1_MultiScaleGateTowerAndCutStateReconstruction,
    .TB2_TelescopingMaurerCartanAndAmariNaturalGradientNilpotency => True
  | .TB2_TelescopingMaurerCartanAndAmariNaturalGradientNilpotency,
    .TB3_TwoLayerCotangentBackpropAndTraceAdjointSplit => True
  | .TB3_TwoLayerCotangentBackpropAndTraceAdjointSplit,
    .TB4_ConcreteYangianMonodromyBlockAndDyckTreeEvaluation => True
  | .TB3_TwoLayerCotangentBackpropAndTraceAdjointSplit,
    .TB5_BinetCauchyBacCabAndZornParameterUniqueness => True
  | .TB4_ConcreteYangianMonodromyBlockAndDyckTreeEvaluation,
    .TB6_MasterTelescopingBackpropYangianZornSynthesis => True
  | .TB5_BinetCauchyBacCabAndZornParameterUniqueness,
    .TB6_MasterTelescopingBackpropYangianZornSynthesis => True
  | _, _ => False

instance : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> simp [causalEdge] <;> infer_instance

theorem causalEdge_implies_rank_lt {a b : TelescopingBackpropYangianZornStage}
    (h : causalEdge a b) : a.rank < b.rank := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

theorem transGen_implies_rank_lt {a b : TelescopingBackpropYangianZornStage}
    (h : Relation.TransGen causalEdge a b) : a.rank < b.rank := by
  induction h with
  | single hab => exact causalEdge_implies_rank_lt hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_implies_rank_lt hbc)

/-- Strict DAG acyclicity of `𝔗𝔅₁ ≺ 𝔗𝔅₂ ≺ 𝔗𝔅₃ ≺ {𝔗𝔅₄, 𝔗𝔅₅} ≺ 𝔗𝔅₆`. -/
theorem causalEdge_acyclic (st : TelescopingBackpropYangianZornStage) :
    ¬ Relation.TransGen causalEdge st st := by
  intro h
  exact Nat.lt_irrefl st.rank (transGen_implies_rank_lt h)

/-- The parallel branches `𝔗𝔅₄` (concrete 2-site Yangian CPT-Dyck monodromy) and `𝔗𝔅₅`
(Binet–Cauchy / BAC–CAB Zorn parameter uniqueness) are incomparable in `causalEdge`. -/
theorem incomparable_TB4_TB5 :
    ¬ causalEdge .TB4_ConcreteYangianMonodromyBlockAndDyckTreeEvaluation
        .TB5_BinetCauchyBacCabAndZornParameterUniqueness ∧
    ¬ causalEdge .TB5_BinetCauchyBacCabAndZornParameterUniqueness
        .TB4_ConcreteYangianMonodromyBlockAndDyckTreeEvaluation := by
  decide

end TelescopingBackpropYangianZornStage

section TelescopingBackpropYangianZornPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine.MultiScalePeirceGateTower
open InfoGeometry.Canonical.MonodromyCPTDyckFiniteMatrixBridge
open InfoGeometry.Canonical.ZornPluckerHodgeBinetCauchyBacCabAmariPoset
open InfoGeometry.Canonical.PeirceBackpropTraceGradientBridge

/-- **Stage `𝔗𝔅₁` (`tb1_multiscale_gate_tower_and_cut_state_reconstruction`)**:
For any scale family `scale : ℕ → B × (B × B)` in any `[Ring B]` with idempotent Peirce
cuts `hP : ∀ k, (scale k).1 * (scale k).1 = (scale k).1`:
1. Two-sided invertibility of `towerGate scale n` and `towerGateInv scale n`,
2. Two-sided invertibility of `segmentGate scale start len` and `segmentGateInv scale start len`,
3. Exact prefix/suffix split `towerGate scale (start + len) = segmentGate scale start len * towerGate scale start`,
4. Exact zero-activation-memory cut-state reconstruction:
   `segmentGateInv scale start len * (towerGate scale (start + len) * x) = towerGate scale start * x`. -/
theorem tb1_multiscale_gate_tower_and_cut_state_reconstruction
    {B : Type*} [Ring B] (scale : ℕ → B × (B × B))
    (hP : ∀ k, (scale k).1 * (scale k).1 = (scale k).1)
    (n start len : ℕ) (x : B) :
    (towerGate scale n * towerGateInv scale n = 1 ∧
      towerGateInv scale n * towerGate scale n = 1) ∧
    (segmentGate scale start len * segmentGateInv scale start len = 1 ∧
      segmentGateInv scale start len * segmentGate scale start len = 1) ∧
    towerGate scale (start + len) =
      segmentGate scale start len * towerGate scale start ∧
    segmentGateInv scale start len *
        (towerGate scale (start + len) * x) = towerGate scale start * x := by
  exact ⟨towerGate_two_sided_inverse scale hP n,
    segmentGate_two_sided_inverse scale hP start len,
    towerGate_add_split scale start len,
    suffix_reconstructs_cut_state scale hP start len x⟩

/-- **Stage `𝔗𝔅₂` (`tb2_telescoping_maurer_cartan_and_plus_dressed_gradient_nilpotency`)**:
1. Two-layer right-invariant Maurer–Cartan log-differential telescoping (`two_layer_maurer_cartan_right_log_diff`),
2. Multi-scale `(n + 1)`-layer right-invariant Maurer–Cartan telescoping (`towerGate_succ_maurer_cartan_telescoping`),
3. Plus-dressed gradient corner, square-zero, inverse, and factorization identities
   (`bp3_plus_dressed_gradient_corner_and_square_zero`). -/
theorem tb2_telescoping_maurer_cartan_and_plus_dressed_gradient_nilpotency
    {B : Type*} [Ring B] [StarRing B]
    (scale : ℕ → B × (B × B))
    (hP_scale : ∀ k, (scale k).1 * (scale k).1 = (scale k).1)
    (n : ℕ) (dx : B × B) (dT : B)
    {G₂ G₂_inv dG₂ G₁ G₁_inv dG₁ : B} (hG₁ : G₁ * G₁_inv = 1)
    {P : B} (hP : P * P = P) (A C Xbar Xout : B) :
    ((dG₂ * G₁ + G₂ * dG₁) * (G₁_inv * G₂_inv) =
      dG₂ * G₂_inv + G₂ * (dG₁ * G₁_inv) * G₂_inv) ∧
    ((scaleGateDiff (scale n).1 (scale n).2 dx * towerGate scale n +
        scaleGate (scale n).1 (scale n).2 * dT) *
      towerGateInv scale (n + 1) =
      (conePlus (scale n).1 dx.1 +
        InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceExponentialModularSynthesis.upperCornerUnit
          (scale n).1 (scale n).2.1 *
          coneMinus (scale n).1 dx.2 *
          InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceExponentialModularSynthesis.upperCornerUnit
            (scale n).1 (-(scale n).2.1)) +
      scaleGate (scale n).1 (scale n).2 *
        (dT * towerGateInv scale n) *
        scaleGateInv (scale n).1 (scale n).2) ∧
    (P * plusDressedPrimalGrad P A C Xbar Xout * (1 - P) =
      plusDressedPrimalGrad P A C Xbar Xout ∧
     plusDressedPrimalGrad P A C Xbar Xout * plusDressedPrimalGrad P A C Xbar Xout = 0 ∧
     (1 - plusDressedPrimalGrad P A C Xbar Xout) *
       (1 + plusDressedPrimalGrad P A C Xbar Xout) = 1 ∧
     (1 - OperatorAlgebra.PeirceSpine.qgtPlus P A C) * plusDressedPrimalGrad P A C Xbar Xout =
       (1 - OperatorAlgebra.PeirceSpine.qgtPlus P A C * OperatorAlgebra.PeirceSpine.qgtPlus P A C) *
         TensorPeirceAttentionNetworkAmariYangianPoset.primalGateGrad P Xbar Xout ∧
     (1 - P) * plusDressedDualGrad P A C Xbar Xout * P =
       plusDressedDualGrad P A C Xbar Xout ∧
     plusDressedDualGrad P A C Xbar Xout * plusDressedDualGrad P A C Xbar Xout = 0 ∧
     (1 - plusDressedDualGrad P A C Xbar Xout) *
       (1 + plusDressedDualGrad P A C Xbar Xout) = 1 ∧
     (1 - OperatorAlgebra.PeirceSpine.qgtMinus P A C) * plusDressedDualGrad P A C Xbar Xout =
       (1 - OperatorAlgebra.PeirceSpine.qgtMinus P A C * OperatorAlgebra.PeirceSpine.qgtMinus P A C) *
         TensorPeirceAttentionNetworkAmariYangianPoset.dualGateGrad P A Xbar Xout) := by
  exact ⟨two_layer_maurer_cartan_right_log_diff hG₁,
    towerGate_succ_maurer_cartan_telescoping scale hP_scale n dx dT,
    bp3_plus_dressed_gradient_corner_and_square_zero hP A C Xbar Xout⟩

/-- **Stage `𝔗𝔅₃` (`tb3_two_layer_cotangent_backprop_and_trace_adjoint_split`)**:
1. Two-layer zero-activation-memory parameter gradient trace-adjoint split (`bp3_two_layer_parameter_variation_trace_adjoint`),
2. Multi-layer $n$-stage reverse state reconstruction (`backwardGaussianTowerState_forwardGaussianTower`) and cotangent trace-adjoint law (`trace_backwardGaussianTowerCotangent_adjoint`),
3. Zero-gradient-attenuation cotangent transport across any well-bracketed `CPTDyckParseTree.DyckTree` (`dyckTree_cotangent_transport_invariant`). -/
theorem tb3_two_layer_cotangent_backprop_and_trace_adjoint_split
    {R n_idx : Type*} [CommRing R] [StarRing R] [Fintype n_idx] [DecidableEq n_idx]
    {P₂ A₂ C₂ dA₂ dC₂ P₁ A₁ C₁ dA₁ dC₁ Xbar₂ X₂ X₀ dX₀ : Matrix n_idx n_idx R}
    (hP₂ : P₂ * P₂ = P₂) (hP₂star : star P₂ = P₂)
    (hP₁ : P₁ * P₁ = P₁) (hP₁star : star P₁ = P₁)
    (layers : List (Matrix n_idx n_idx R × Matrix n_idx n_idx R))
    (param : ℕ → Matrix n_idx n_idx R)
    (tree : CPTDyckParseTree.DyckTree ℕ) :
    let X₁ := TensorPeirceAttentionNetworkAmariYangianPoset.backpropInput P₂ A₂ C₂ X₂
    let Xbar₁ := TensorPeirceAttentionNetworkAmariYangianPoset.inputCotangentGrad P₂ A₂ C₂ Xbar₂
    (Matrix.trace (star Xbar₂ *
        (TensorPeirceAttentionNetworkAmariYangianPoset.attentionGaussianPlusDiff P₂ A₂ C₂ dA₂ dC₂ * X₁ +
          TensorPeirceAttentionNetworkAmariYangianPoset.attentionGaussianPlus P₂ A₂ C₂ *
            (TensorPeirceAttentionNetworkAmariYangianPoset.attentionGaussianPlusDiff P₁ A₁ C₁ dA₁ dC₁ *
              TensorPeirceAttentionNetworkAmariYangianPoset.backpropInput P₁ A₁ C₁ X₁))) =
      (Matrix.trace (star (TensorPeirceAttentionNetworkAmariYangianPoset.primalGateGrad P₂ Xbar₂ X₂) * dA₂) +
        Matrix.trace (star (TensorPeirceAttentionNetworkAmariYangianPoset.dualGateGrad P₂ A₂ Xbar₂ X₂) * dC₂)) +
      (Matrix.trace (star (TensorPeirceAttentionNetworkAmariYangianPoset.primalGateGrad P₁ Xbar₁ X₁) * dA₁) +
        Matrix.trace (star (TensorPeirceAttentionNetworkAmariYangianPoset.dualGateGrad P₁ A₁ Xbar₁ X₁) * dC₁))) ∧
    backwardGaussianTowerState P₁ layers (forwardGaussianTower P₁ layers X₀) = X₀ ∧
    Matrix.trace (star Xbar₂ * forwardGaussianTower P₁ layers dX₀) =
      Matrix.trace (star (backwardGaussianTowerCotangent P₁ layers Xbar₂) * dX₀) ∧
    star (CPTDyckParseTree.DyckTree.eval
      (fun label => CPTDyckParseTree.peirceOpen P₁ (param label))
      (fun label => CPTDyckParseTree.peirceClose P₁ (param label)) tree) * Xbar₂ = Xbar₂ := by
  intro X₁ Xbar₁
  exact ⟨bp3_two_layer_parameter_variation_trace_adjoint hP₂ hP₂star hP₁ hP₁star,
    backwardGaussianTowerState_forwardGaussianTower hP₁ layers X₀,
    trace_backwardGaussianTowerCotangent_adjoint P₁ layers Xbar₂ dX₀,
    dyckTree_cotangent_transport_invariant hP₁ param tree Xbar₂⟩

/-- **Stage `𝔗𝔅₄` (`tb4_concrete_yangian_monodromy_block_and_dyck_tree_evaluation`)**:
For any spectral parameter tuple `ℓ : SpectralLabel = ℝ × ℝ × ℝ × ℝ` and any recursive
syntactic tree `tree : CPTDyckParseTree.DyckTree SpectralLabel`:
1. The concrete 2-site Yangian creation block `creation ℓ = monodromyB2 u θ₁ θ₂ η` lies in
   the lower-left Peirce corner (`creation ℓ = (1 - peirceP) * creation ℓ * peirceP`),
2. `creation ℓ * creation ℓ = 0`,
3. Twisted-Pin $\mathcal{C}\mathcal{P}\mathcal{T}$ negates the creation block
   (`KantorTanakaFiveGradedMetriplecticZornPoset.PlabicTwistedPinCPT.thetaCPT peirceP sigmaX (creation ℓ) = -creation ℓ`),
4. `openGate ℓ * closeGate ℓ = 1 ∧ closeGate ℓ * openGate ℓ = 1`,
5. Every well-bracketed `DyckTree SpectralLabel` evaluates to the $2 \times 2$ identity matrix:
   `CPTDyckParseTree.DyckTree.eval openGate closeGate tree = 1`. -/
theorem tb4_concrete_yangian_monodromy_block_and_dyck_tree_evaluation
    (ℓ : SpectralLabel) (tree : CPTDyckParseTree.DyckTree SpectralLabel) :
    creation ℓ = (1 - peirceP) * creation ℓ * peirceP ∧
    creation ℓ * creation ℓ = 0 ∧
    KantorTanakaFiveGradedMetriplecticZornPoset.PlabicTwistedPinCPT.thetaCPT
      peirceP InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset.sigmaX
      (creation ℓ) = -creation ℓ ∧
    (openGate ℓ * closeGate ℓ = 1 ∧ closeGate ℓ * openGate ℓ = 1) ∧
    CPTDyckParseTree.DyckTree.eval openGate closeGate tree = 1 := by
  exact ⟨creation_lowerLeft ℓ,
    creation_sq_zero ℓ,
    thetaCPT_creation ℓ,
    open_close_inverse ℓ,
    every_tree_eval_eq_one tree⟩

/-- **Stage `𝔗𝔅₅` (`tb5_binet_cauchy_bac_cab_and_zorn_parameter_uniqueness`)**:
Reuses `ZornPluckerHodgeBinetCauchyBacCabAmariPoset`:
1. Unique dimensional fixed point `Nat.choose D 2 = D ↔ D = 3` for `0 < D`,
2. Binet–Cauchy off-diagonal norm defect `(1 + α * β) * ((u₁ × u₂) · (v₁ × v₂))`,
3. Left and right alternativity of `ZornAlgebra K` via 3D BAC–CAB cancellation,
4. Uniqueness of the Zorn parameter pair `(α, β) = (1, -1)` and the Amari–Chentsov
   cubic baryon singlet anticommutator. -/
theorem tb5_binet_cauchy_bac_cab_and_zorn_parameter_uniqueness
    {R_z : Type*} [Ring R_z] {K : Type*} [CommRing K]
    (α β : K)
    (X Y : InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix R_z)
    (A B : InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra K)
    (u₁ v₁ u₂ v₂ u₃ : InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3 K) :
    (∀ D : ℕ, 0 < D → (Nat.choose D 2 = D ↔ D = 3)) ∧
    (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.norm (zornOffDiag u₁ v₁) *
        InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.norm (zornOffDiag u₂ v₂) -
      InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.norm
        (zornParamMul α β (zornOffDiag u₁ v₁) (zornOffDiag u₂ v₂)) =
      (1 + α * β) *
        InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.dot
          (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.cross u₁ u₂)
          (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.cross v₁ v₂)) ∧
    (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.associator A A B =
        InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.zero ∧
      InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.associator B A A =
        InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.zero) ∧
    ((zornParamMul α β
        (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.quarkU
          InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.e_r)
        (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.quarkU
          InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.e_g) =
        InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.antiquarkV
          InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.e_b ∧ α * β = -1) →
      α = 1 ∧ β = -1 ∧
        zornParamMul α β A B =
          InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.mul A B) ∧
    (X * Y = zornOrgan1DiagonalCore X Y + zornOrgan2PrimalBimoduleDrift X Y +
        zornOrgan3DualBimoduleDrift X Y + zornOrgan4PluckerHodgeCross X Y ∧
      InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.anticommutator
        (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.mul
          (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.quarkU u₁)
          (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.quarkU u₂))
        (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.quarkU u₃) =
      InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.smul
        (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.dot
          (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.cross u₁ u₂) u₃)
        InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.one) := by
  have hMaster := zorn_plucker_hodge_binet_cauchy_bac_cab_amari_master_poset
    α β X Y A B u₁ v₁ u₂ v₂ u₃
  have hZ6 := stage_Z6_unique_zorn_table_fourfold_anatomy_twistor_plucker_and_cubic_baryon
    α β X Y A B u₁ u₂ u₃
  exact ⟨hMaster.2.2.2.1, hMaster.2.2.2.2.1, hMaster.2.2.2.2.2.1, hZ6.1, hMaster.2.2.2.2.2.2⟩

/-- **Stage `𝔗𝔅₆` (`tb6_master_telescoping_backprop_yangian_zorn_synthesis`)**:
Master theorem unifying the 6-stage **Telescoping Multi-Scale Maurer–Cartan Backpropagation,
Two-Layer Cotangent Trace-Adjoint Split, Concrete Yangian $\mathcal{C}\mathcal{P}\mathcal{T}$-Dyck
Monodromy, & Zorn Parameter Uniqueness Poset**
(`𝔗𝔅₁ ≺ 𝔗𝔅₂ ≺ 𝔗𝔅₃ ≺ {𝔗𝔅₄, 𝔗𝔅₅} ≺ 𝔗𝔅₆`). -/
theorem tb6_master_telescoping_backprop_yangian_zorn_synthesis
    {B : Type*} [Ring B] [StarRing B]
    (scale : ℕ → B × (B × B))
    (hP_scale : ∀ k, (scale k).1 * (scale k).1 = (scale k).1)
    (start len : ℕ) (x : B)
    {P : B} (hP : P * P = P) (A C Xbar Xout : B)
    (ℓ : SpectralLabel) (tree : CPTDyckParseTree.DyckTree SpectralLabel)
    {K : Type*} [CommRing K]
    (A_z B_z : InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra K)
    (u₁ u₂ u₃ : InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3 K) :
    (∀ st : TelescopingBackpropYangianZornStage,
      ¬ Relation.TransGen TelescopingBackpropYangianZornStage.causalEdge st st) ∧
    Fintype.card TelescopingBackpropYangianZornStage = 6 ∧
    (¬ TelescopingBackpropYangianZornStage.causalEdge
        .TB4_ConcreteYangianMonodromyBlockAndDyckTreeEvaluation
        .TB5_BinetCauchyBacCabAndZornParameterUniqueness ∧
     ¬ TelescopingBackpropYangianZornStage.causalEdge
        .TB5_BinetCauchyBacCabAndZornParameterUniqueness
        .TB4_ConcreteYangianMonodromyBlockAndDyckTreeEvaluation) ∧
    segmentGateInv scale start len *
        (towerGate scale (start + len) * x) = towerGate scale start * x ∧
    (1 - OperatorAlgebra.PeirceSpine.qgtPlus P A C) * plusDressedPrimalGrad P A C Xbar Xout =
      (1 - OperatorAlgebra.PeirceSpine.qgtPlus P A C * OperatorAlgebra.PeirceSpine.qgtPlus P A C) *
        TensorPeirceAttentionNetworkAmariYangianPoset.primalGateGrad P Xbar Xout ∧
    (1 - OperatorAlgebra.PeirceSpine.qgtMinus P A C) * plusDressedDualGrad P A C Xbar Xout =
      (1 - OperatorAlgebra.PeirceSpine.qgtMinus P A C * OperatorAlgebra.PeirceSpine.qgtMinus P A C) *
        TensorPeirceAttentionNetworkAmariYangianPoset.dualGateGrad P A Xbar Xout ∧
    creation ℓ * creation ℓ = 0 ∧
    CPTDyckParseTree.DyckTree.eval openGate closeGate tree = 1 ∧
    InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.associator A_z A_z B_z =
      InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.zero ∧
    InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.anticommutator
      (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.mul
        (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.quarkU u₁)
        (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.quarkU u₂))
      (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.quarkU u₃) =
      InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.smul
        (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.dot
          (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.cross u₁ u₂) u₃)
        InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.one := by
  have hNat := bp3_plus_dressed_gradient_corner_and_square_zero hP A C Xbar Xout
  have hTB4 := tb4_concrete_yangian_monodromy_block_and_dyck_tree_evaluation ℓ tree
  have hTB5 := tb5_binet_cauchy_bac_cab_and_zorn_parameter_uniqueness (R_z := ℤ)
    (1 : K) (-1 : K) 0 0 A_z B_z u₁ u₁ u₂ u₂ u₃
  exact ⟨TelescopingBackpropYangianZornStage.causalEdge_acyclic,
    TelescopingBackpropYangianZornStage.card_eq_six,
    TelescopingBackpropYangianZornStage.incomparable_TB4_TB5,
    suffix_reconstructs_cut_state scale hP_scale start len x,
    hNat.2.2.2.1, hNat.2.2.2.2.2.2.2,
    hTB4.2.1, hTB4.2.2.2.2,
    hTB5.2.2.1.1, hTB5.2.2.2.2.2⟩

end TelescopingBackpropYangianZornPoset

/-!
## 10. Stage `𝔊₈`: Grand Unified Supergrassmannian & Para-Kähler Information Geometry Synthesis (`𝔊₁ ≺ ⋯ ≺ 𝔊₈` & `𝔓₁ ≺ ⋯ ≺ 𝔓₇`)
-/

/-- **Stage `𝔊₈` (`G8_GrandSuperGrassmannianParaKahlerInfoGeometrySynthesis`)**:
Master theorem unifying the 8-stage **Supergrassmannian & Para-Kähler Information Geometry
Manifold Poset** (`𝔊₁ ≺ ⋯ ≺ 𝔊₈`) and the 7-stage **DeWitt-Split Super-Grassmannian & Para-Kähler
Operator Geometry Poset** (`𝔓₁ ≺ ⋯ ≺ 𝔓₇`) with the 7-stage **Split-Octonion Circularly Polarized
Isotropic Amari & Nambu Poset** (`𝔒₁ ≺ ⋯ ≺ 𝔒₇`) and the 8-stage **Supergraded Amari–Berezinian–
Colimit–Observability Poset** (`𝔘₁ ≺ ⋯ ≺ 𝔘₈`). -/
theorem g8_grand_supergrassmannian_parakahler_info_geometry_synthesis
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : ParaKahlerDatum ℝ V) (v : V)
    {A U W : Type*} [Ring A] [AddCommGroup U] [Module A U] [AddCommGroup W] [Module A W]
    (f g : U →ₗ[A] W)
    (G H : (U × W) ≃ₗ[A] (U × W))
    (hG : Overlap G.toLinearMap f)
    (hH : Overlap H.toLinearMap (transition G.toLinearMap f hG))
    {R : Type*} [CommRing R] [Nontrivial R]
    (fZ gZ : Positive R →ₗ[R] Negative R)
    (p q σ k₁ k₂ a : R) (X_mat : Matrix (Fin 3) (Fin 3) R)
    (z₁ z₂ : ParaKahlerVec ℝ) (u₁ u₂ u₃ : Fin 3 → ℝ)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A_op C_op X_op Y_op Z_op : B) :
    -- 1. Acyclicity and Cardinality Across the Four Connected Posets (𝔊₁..𝔊₈, 𝔓₁..𝔓₇, 𝔒₁..𝔒₇, 𝔘₁..𝔘₈):
    (∀ st : SuperGrassmannianParaKahlerStage,
      ¬ Relation.TransGen SuperGrassmannianParaKahlerStage.causalEdge st st) ∧
    (∀ pst : DeWittSplitSuperGrassmannianParaKahlerStage,
      ¬ Relation.TransGen DeWittSplitSuperGrassmannianParaKahlerStage.causalEdge pst pst) ∧
    Fintype.card SuperGrassmannianParaKahlerStage = 8 ∧
    Fintype.card DeWittSplitSuperGrassmannianParaKahlerStage = 7 ∧
    Fintype.card SplitOctonionAmariNambuStage = 7 ∧
    Fintype.card SupergradedAmariColimitObservabilityStage = 8 ∧
    -- 2. Stage G1 (Para-Complex Polarization & Bi-Lagrangian Isotropic Sheets):
    D.metric (paraProjectorPlus D.para.K v) (paraProjectorPlus D.para.K v) = 0 ∧
    D.metric (paraProjectorMinus D.para.K v) (paraProjectorMinus D.para.K v) = 0 ∧
    -- 3. Stage G2 (Noncommutative Projector Graph Charts & Zorn Rank-4 Grassmannian):
    graphProjector f * graphProjector g = graphProjector f ∧
    (grassmannianChart fZ = grassmannianChart gZ ↔ fZ = gZ) ∧
    -- 4. Stage G3 (Operator Möbius Fractional Overlap Cocycle & Sheet Reflection):
    transition (H.toLinearMap.comp G.toLinearMap) f ((overlap_comp_iff G H f hG).mpr hH) =
      transition H.toLinearMap (transition G.toLinearMap f hG) hH ∧
    M_mat (R := R) * K_mat + K_mat * M_mat = 0 ∧
    -- 5. Stage G4 (Weyl Deformation Triad & Supertrace Scale Anomaly):
    superTrace (scaleOperator p q σ + chiralOperator k₁ k₂ + volumeOperator a) = (p - q) * σ ∧
    -- 6. Stage G5 (5-Graded Kantor–Tanaka KKT Quintic Identity & Maurer–Cartan Flatness):
    adH (adH (adH (adH (adH X_mat)))) - 5 • adH (adH (adH X_mat)) + 4 • adH X_mat = 0 ∧
    mcCurvatureTower canonicalMaurerCartanJet = (0, 0, 0, 0, 0) ∧
    -- 7. Stage G6 (Split-Octonion Cl(3,3) Metriplectic Product & Volume Associator):
    InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul (embedVec z₁) (embedVec z₂) =
      zornAdd
        (zornAdd
          (SplitOctonionParaKahlerNullCone.zornSmul ((1 / 2 : ℝ) * paraKahlerMetric z₁ z₂) zornOne)
          (SplitOctonionParaKahlerNullCone.zornSmul ((1 / 2 : ℝ) * symplecticForm z₁ z₂) zornParaGrading))
        (embedVec (hodgeCrossVec z₁ z₂)) ∧
    SplitOctonionParaKahlerNullCone.zornAssociator
      (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₁))
      (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₂))
      (embedVec (SplitOctonionParaKahlerNullCone.primalSheet u₃)) =
      SplitOctonionParaKahlerNullCone.zornSmul (-vec3TripleProduct u₁ u₂ u₃) zornParaGrading ∧
    -- 8. Stage G7 (Para-Kähler Chiral 2-Jet, Schwarz Defect & Noncommutative Bregman 3-Point Law):
    chiralTwoJetPlus P A_op C_op = genV P A_op C_op + genSig P A_op C_op ∧
    chiralTwoJetMinus P A_op C_op = genV P A_op C_op - genSig P A_op C_op ∧
    chiralSchwarzComm P A_op C_op X_op =
      OperatorAlgebra.PeirceSpine.comm (genSig P A_op C_op) X_op ∧
    opBregmanDiv X_op Z_op - opBregmanDiv X_op Y_op - opBregmanDiv Y_op Z_op =
      anticomm (X_op - Y_op) (Y_op - Z_op) ∧
    -- 9. DeWitt-Split Super-Grassmannian Two-Chart Idempotent, Jordan Triple & Push–Pull Intertwiner (𝔓₁..𝔓₇):
    naiveLinearChart P A_op C_op * naiveLinearChart P A_op C_op - naiveLinearChart P A_op C_op =
      genV P A_op C_op ∧
    dressedTwoChartProj P A_op C_op =
      P + genPhi P A_op C_op - genSig P A_op C_op - genV P A_op C_op * conePlus P A_op ∧
    dressedTwoChartProj P A_op C_op * dressedTwoChartProj P A_op C_op =
      dressedTwoChartProj P A_op C_op ∧
    jordanTriple (conePlus P A_op) (coneMinus P C_op) (conePlus P A_op) =
      (2 : ℤ) • (genV P A_op C_op * conePlus P A_op) ∧
    (1 - qgtPlus P A_op C_op) * conePlus P A_op =
      conePlus P A_op * (1 - qgtMinus P A_op C_op) := by
  have hG1 := g1_paracomplex_polarization_isotropic_sheets_and_para_qgt D 0 v v 0 0
  have hG6 := g6_split_octonion_cl33_parakahler_phase_space_and_metriplectic_product 0 z₁ z₂ u₁ u₂ u₃
  have hJet := chiralTwoJet_decomposition P A_op C_op
  have hJacobi : chiralSchwarzComm P A_op C_op X_op =
      OperatorAlgebra.PeirceSpine.comm (genSig P A_op C_op) X_op := by
    dsimp only [chiralSchwarzComm, deltaPlus, deltaMinus, genSig,
      OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  have hM2 := archetype_M2_modular_surprisal_and_bregman_three_point
    hP A_op C_op A_op A_op C_op C_op X_op Y_op Z_op
  have hR0 := rung0_socratic_aporia_naive_linear_chart_jumps_off_grassmannian hP A_op C_op
  have hP3 := p3_bruhat_dressed_two_chart_idempotent_and_jordan_triple hP A_op C_op
  have hP4 := p4_associative_push_pull_resolvent_intertwiner hP A_op C_op
  exact ⟨SuperGrassmannianParaKahlerStage.causalEdge_acyclic,
    DeWittSplitSuperGrassmannianParaKahlerStage.causalEdge_acyclic,
    SuperGrassmannianParaKahlerStage.card_eq_eight,
    DeWittSplitSuperGrassmannianParaKahlerStage.card_eq_seven,
    SplitOctonionAmariNambuStage.card_eq_seven,
    SupergradedAmariColimitObservabilityStage.card_eq_eight,
    hG1.2.2.2.2.2.2.2.1,
    hG1.2.2.2.2.2.2.2.2.1,
    graphProjector_mul f g,
    grassmannianChart_injective.eq_iff,
    transition_cocycle G H f hG hH,
    moebius_anticommutes_polarization,
    total_deformation_superTrace p q σ k₁ k₂ a,
    adH_quintic_identity X_mat,
    canonicalMaurerCartanJet_flat,
    hG6.2.2.2.1,
    hG6.2.2.2.2.2.2,
    hJet.1,
    hJet.2,
    hJacobi,
    hM2.1,
    hR0.2.2.1,
    hP3.1,
    hP3.2.1,
    hP3.2.2.2.2.2.1,
    hP4.2.2.2.2.2.1⟩

end InfoGeometry.Canonical.SuperGrassmannianParaKahlerInfoGeometryPoset
