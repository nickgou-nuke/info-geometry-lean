/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NonAssocDerivation
import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.Canonical.OperatorFrechetForms
import InfoGeometry.Thermo.OnsagerDifferentialFormsBridge
import InfoGeometry.Thermo.GenericMetriplecticFlow
import InfoGeometry.Canonical.FreeEnergyDissipationRate
import InfoGeometry.Canonical.BKMOnsagerMobilityBridge
import InfoGeometry.Canonical.CEBKMOnsagerSystem
import InfoGeometry.Canonical.ErlangenOperator2Bridge
import InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceArchetypeCausalSynthesis
import InfoGeometry.SuperMetriplectic.CartanOnsagerParityBridge
import InfoGeometry.SuperMetriplectic.PeirceCutCartanDerivationBridge
import InfoGeometry.Canonical.CEBKMParityUnificationBridge
import InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw
import InfoGeometry.Canonical.ModularDerivationLaneBridge
import InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge

/-!
# Umbrella Architectural Capstone: Unified Leibniz–Derivation–Fréchet–Onsager Framework

Connects the four repository ontology pillars (`Leibniz`, `Derivation`, `Fréchet`, `Onsager`)
and all four closed bridge lanes (`Gap A` through `Gap D`) into a diamond-free canonical
synthesis:

1. **Core Spine Structures (`UnifiedDerivationOnsagerFormSpine`, `LeibnizDerivationFrechetOnsagerSpine`):**
   Genuine `Type`-level data-carrying structures bundling `DerivationLieLane`,
   `CartanOnsagerSplit`, `PeirceCut`, `FaithfulDensityOperator`, `ParityOnsagerSystem`,
   `ParityOnsagerFormPairing`, `ErlangenOperatorDatum`, and `DerivationOperatorForm`,
   with canonical constructors (`ofParitySystem`, `canonicalStarCapstoneSpine`,
   `canonicalAutCapstoneSpine`).
2. **All Six Cross-Gap Pair Integration Theorems:**
   - `Gap A + Gap B` (`gapAB_peirceCut_ceBKM_parity_bridge`, `gapAB_cartanSplit_parityFormPairing_bridge`),
   - `Gap B + Gap C` (`gapBC_frechetHessian_gibbsTrajectory_secondLaw`),
   - `Gap A + Gap D` (`gapAD_peirceCut_superAnticomm_cartan_bridge`, `gapAD_bridgedLane_cartanOnsager_bridge`),
   - `Gap D + Gap B` (`gapDB_modularDerivation_ceBKM_parityForm_bridge`, `gapDB_superBraided_ceBKM_curvature_bridge`),
   - `Gap C + Gap D` (`gapCD_modularDerivation_metriplecticFlow_secondLaw`, `gapCD_exceptionalSuperDerivation_metriplecticFlow_secondLaw`),
   - `Gap A + Gap C` (`gapAC_cartanSchur_metriplecticFlow_secondLaw`, `gapAC_peirceCut_matrixKuboMori_secondLaw`).
3. **Master Four-Pillar Synthesis & Noncommutative `n = 2` Witness:**
   `four_pillar_unified_capstone` and `capstone_qubit_nondegenerate_witness`.

## Scope and Hygiene
- Zero global `instance` declarations and zero global `open scoped` overrides
  (`Matrix.Norms.L2Operator` and `LieRing.ofAssociativeRing` / `LieAlgebra.ofAssociativeAlgebra`
  are strictly section-local).
- Proved over finite `FiniteOperatorAlgebra n` / `GibbsOperator n` for concrete Gibbs/BKM
  theorems, and over arbitrary normed spaces for Banach-level metriplectic trajectories
  (full-interval non-equilibrium ODE existence remains external).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 800000

noncomputable section

namespace InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone

open InfoGeometry.Core
open InfoGeometry.Algebra
open InfoGeometry.Algebra.NonAssocDerivation
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Thermo
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem
open InfoGeometry.Thermo.OnsagerFormsBridge
open InfoGeometry.SuperMetriplectic
open InfoGeometry.SuperMetriplectic.CartanOnsagerParityBridge
open InfoGeometry.SuperMetriplectic.PeirceCutCartanDerivationBridge
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes
open InfoGeometry.Canonical.CEOneFormNOperatorBridge
open InfoGeometry.Canonical.CEBKMOnsagerSystem
open InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration
open InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily
open InfoGeometry.Canonical.CEBKMParityUnificationBridge
open InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw
open InfoGeometry.Canonical.ModularDerivationLaneBridge
open InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.BKMOnsagerMobilityBridge
open InfoGeometry.Canonical.ErlangenOperator2 (ErlangenOperatorDatum)
open SouriauOnsagerBKM

/-! ## Section 1: Core `Type`-Level Unification Spine Structures -/

section CoreSpineStructures

universe u_A u_L

/-- Genuine `Type`-level cross-pillar spine unifying a faithful `DerivationLieLane ℝ A`
(`Leibniz` + `Derivation`), an `OnsagerCasimirSystem A` (`Onsager`), arbitrary-degree
`ParityOnsagerFormPairing K.L A m` across `DerivationOperatorForm`, and a connection
`1`-form `DerivationOperatorForm K 1`. -/
structure UnifiedDerivationOnsagerFormSpine (A : Type u_A)
    [NonUnitalNonAssocRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] where
  lane : DerivationLieLane.{0, u_A, u_L} ℝ A
  onsager : OnsagerCasimirSystem A
  observable : A
  evalForm : ∀ (m : ℕ), (Fin m → lane.L) → ParityOnsagerFormPairing lane.L A m
  connectionForm : DerivationOperatorForm lane 1
  induced_eval : ∀ x y : lane.L,
    (inducedDerivationLaneOnsagerSystem onsager lane observable).totalGenerator x y =
      onsager.totalGenerator (lane.operatorAction x observable)
        (lane.operatorAction y observable)
  form_reciprocity : ∀ (m : ℕ) (v : Fin m → lane.L)
    (ω η : DerivationOperatorForm lane m),
    (evalForm m v).totalGenerator ((evalForm m v).T.op ω) ((evalForm m v).T.op η) =
      (evalForm m v).totalGenerator η ω

/-- Canonical constructor lifting any `DerivationLieLane ℝ A`, `ParityOnsagerSystem A`,
observable `a : A`, and connection `OneForm K` into `UnifiedDerivationOnsagerFormSpine A`. -/
def UnifiedDerivationOnsagerFormSpine.ofParitySystem
    {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (K : DerivationLieLane.{0, u_A, u_L} ℝ A) (PS : ParityOnsagerSystem A)
    (a : A) (Γ : OneForm K) :
    UnifiedDerivationOnsagerFormSpine.{u_A, u_L} A where
  lane := K
  onsager := PS.toOnsagerCasimirSystem
  observable := a
  evalForm m v := ParityOnsagerFormPairing.ofValueParity PS v
  connectionForm := oneFormAlternatingLinearEquiv K Γ
  induced_eval x y :=
    inducedDerivationLaneOnsagerSystem_totalGenerator PS.toOnsagerCasimirSystem K a x y
  form_reciprocity m v ω η :=
    onsager_pairing_derivationForm_reciprocity K (ParityOnsagerFormPairing.ofValueParity PS v) ω η

/-- Concrete `n = 2` inhabitant of `UnifiedDerivationOnsagerFormSpine (FiniteOperatorAlgebra 2)`
anchored at `d63FrechetOperatorCut` and `tiltOp2`/`switchOp2`. -/
def canonicalUnifiedDerivationOnsagerFormSpine :
    UnifiedDerivationOnsagerFormSpine (FiniteOperatorAlgebra 2) :=
  UnifiedDerivationOnsagerFormSpine.ofParitySystem
    (peirceCutDerivationLieLane 2)
    (peirceCartanParityOnsagerSystem d63FrechetOperatorCut 0)
    switchOp2
    (exteriorDerivativeZero (peirceCutDerivationLieLane 2) tiltOp2)

/-- Genuine `Type`-level 4-pillar capstone spine on `GibbsOperator n` integrating:
- **Gap A**: `PeirceCut n`, `peirceCartanOnsagerSplit`, `peirceDerivCartanOnsagerSplit`,
  `peirceCutDerivationLieLane`, and `peirceCartanParityOnsagerSystem`,
- **Gap B**: `CEBKMParityUnificationBridge` (`ParityOnsagerSystem (Carrier n)`),
  `frechetFormParityOnsagerPairing*` (`Fréchet` exterior forms), and
  `ErlangenOperatorDatum` (`Unit`-sector 1-operator family),
- **Fréchet**: `secondFDerivLogPartitionReadout` BKM Hessian alignment. -/
structure LeibnizDerivationFrechetOnsagerSpine (n : ℕ) where
  peirceCut : PeirceCut n
  peirceCartan : CartanOnsagerSplit (GibbsOperator n)
  peirceDerivCartan : CartanOnsagerSplit (NonAssocDerivation.derivations ℝ (GibbsOperator n))
  peirceLane : DerivationLieLane ℝ (GibbsOperator n)
  hamiltonian : GibbsOperator n
  observable : GibbsOperator n
  probe : GibbsOperator n
  hH : IsSelfAdjoint hamiltonian
  hZ : 0 < gibbsPartitionReal hamiltonian
  density : FaithfulDensityOperator n
  hpow : Continuous density.rpow
  ceParitySystem : ParityOnsagerSystem (Carrier n)
  peirceParitySystem : ParityOnsagerSystem (GibbsOperator n)
  frechetFormPairing : ∀ (m : ℕ),
    (Fin m → (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L) →
      ParityOnsagerFormPairing (frechetVectorFieldDerivationLane ℝ (GibbsOperator n)).L
        (SmoothOpMap ℝ (GibbsOperator n)) m
  erlangenDatum : ErlangenOperatorDatum ℝ Unit Unit (FamilyCarrier 1 n)
  peirce_split_compat :
    LinearMap.ker (peirceAdMap peirceCut ∘ₗ peirceAdMap peirceCut) = peirceCartan.drazinCore ∧
      LinearMap.range (peirceAdMap peirceCut) = peirceCartan.dissipativeRange
  dissipative_eq_hessian :
    ∀ D₁ D₂ : FrechetOperatorDerivation ℂ (GibbsOperator n),
      IsSelfAdjoint (finiteCEOperatorForm n observable (finiteCEFrechetDirection D₁)) →
      (secondFDerivLogPartitionReadout hamiltonian
        (finiteCEOperatorForm n observable (finiteCEFrechetDirection D₁))
        (finiteCEOperatorForm n observable (finiteCEFrechetDirection D₂))).re =
        ceParitySystem.dissipative (finiteCEFrechetDirection D₁) (finiteCEFrechetDirection D₂)
  ce_reciprocity : ∀ x y : Carrier n,
    ceParitySystem.totalGenerator (ceParitySystem.T.op x) (ceParitySystem.T.op y) =
      ceParitySystem.totalGenerator y x
  peirce_reciprocity : ∀ X Y : GibbsOperator n,
    peirceParitySystem.totalGenerator (peirceParitySystem.T.op X) (peirceParitySystem.T.op Y) =
      peirceParitySystem.totalGenerator Y X

/-- Canonical `star`-reversal constructor for `LeibnizDerivationFrechetOnsagerSpine n`
(`IsSelfAdjoint a`, `IsSelfAdjoint Q`). -/
def canonicalStarCapstoneSpine {n : ℕ}
    (P : PeirceCut n) (H a Q : GibbsOperator n)
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (ha : IsSelfAdjoint a) (hQ : IsSelfAdjoint Q)
    (η_peirce : LinearMap.BilinForm ℝ (GibbsOperator n)) :
    LeibnizDerivationFrechetOnsagerSpine n where
  peirceCut := P
  peirceCartan := peirceCartanOnsagerSplit P
  peirceDerivCartan := peirceDerivCartanOnsagerSplit P
  peirceLane := peirceCutDerivationLieLane n
  hamiltonian := H
  observable := a
  probe := Q
  hH := hH
  hZ := hZ
  density := faithfulGibbsDensity H hH hZ
  hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
  ceParitySystem := finiteGibbsCEParityOnsagerSystem H hH hZ a Q ha hQ
  peirceParitySystem := peirceCartanParityOnsagerSystem P η_peirce
  frechetFormPairing _ v :=
    frechetFormParityOnsagerPairing
      (faithfulGibbsDensity H hH hZ) (continuous_faithfulGibbsDensity_rpow H hH hZ) Q hQ H v
  erlangenDatum :=
    gibbsNOperatorFamilyStarErlangenDatum (G := Unit) H hH hZ
      (fun _ => a) (fun _ => ha) (fun _ => 1) Q hQ
  peirce_split_compat := ⟨peirceAdSq_ker_eq_k P, peirceAd_range_eq_p P⟩
  dissipative_eq_hessian D₁ D₂ hA₁ := by
    change (secondFDerivLogPartitionReadout H _ _).re =
      (finiteGibbsCEOnsagerSystem H hH hZ a Q).dissipative
        (finiteCEFrechetDirection D₁) (finiteCEFrechetDirection D₂)
    exact finiteGibbsCEOnsagerSystem_dissipative_eq_logPartitionHessian H a Q hH hZ D₁ D₂ hA₁
  ce_reciprocity x y :=
    (finiteGibbsCEParityOnsagerSystem H hH hZ a Q ha hQ).onsager_casimir_master_reciprocity x y
  peirce_reciprocity X Y :=
    (peirceCartanParityOnsagerSystem P η_peirce).onsager_casimir_master_reciprocity X Y

/-- Canonical involutive `*`-automorphism `τ` constructor for
`LeibnizDerivationFrechetOnsagerSpine n` (`τ H = H`, `τ a = a`, `τ Q = -Q`),
supporting genuinely non-degenerate reversible curvature alongside positive BKM Hessian. -/
def canonicalAutCapstoneSpine {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (P : PeirceCut n) (H a Q : GibbsOperator n)
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (ha : τ a = a) (hQ : τ Q = -Q)
    (η_peirce : LinearMap.BilinForm ℝ (GibbsOperator n)) :
    LeibnizDerivationFrechetOnsagerSpine n where
  peirceCut := P
  peirceCartan := peirceCartanOnsagerSplit P
  peirceDerivCartan := peirceDerivCartanOnsagerSplit P
  peirceLane := peirceCutDerivationLieLane n
  hamiltonian := H
  observable := a
  probe := Q
  hH := hH
  hZ := hZ
  density := faithfulGibbsDensity H hH hZ
  hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
  ceParitySystem :=
    finiteGibbsCEParityOnsagerSystemOfAut τ hτ_inv H hH hZ hτ_H hτ_tr a Q ha hQ
  peirceParitySystem := peirceCartanParityOnsagerSystem P η_peirce
  frechetFormPairing _ v :=
    frechetFormParityOnsagerPairingOfAut τ hτ_inv
      (faithfulGibbsDensity H hH hZ) (continuous_faithfulGibbsDensity_rpow H hH hZ)
      (aut_faithfulGibbsDensity_rho τ H hH hZ hτ_H) hτ_tr Q hQ H v
  erlangenDatum :=
    gibbsNOperatorFamilyAutErlangenDatum (G := Unit) τ hτ_inv H hH hZ hτ_H hτ_tr
      (fun _ => a) (fun _ => ha) (fun _ => 1) Q hQ
  peirce_split_compat := ⟨peirceAdSq_ker_eq_k P, peirceAd_range_eq_p P⟩
  dissipative_eq_hessian D₁ D₂ hA₁ := by
    change (secondFDerivLogPartitionReadout H _ _).re =
      (finiteGibbsCEOnsagerSystem H hH hZ a Q).dissipative
        (finiteCEFrechetDirection D₁) (finiteCEFrechetDirection D₂)
    exact finiteGibbsCEOnsagerSystem_dissipative_eq_logPartitionHessian H a Q hH hZ D₁ D₂ hA₁
  ce_reciprocity x y :=
    (finiteGibbsCEParityOnsagerSystemOfAut τ hτ_inv H hH hZ hτ_H hτ_tr a Q ha hQ).onsager_casimir_master_reciprocity x y
  peirce_reciprocity X Y :=
    (peirceCartanParityOnsagerSystem P η_peirce).onsager_casimir_master_reciprocity X Y

/-- Concrete `n = 2` noncommutative inhabitant of `LeibnizDerivationFrechetOnsagerSpine 2`
using `d63FrechetOperatorCut`, `conjStarAlgEquiv 2`, `tiltOp2`, `switchOp2`, and
`Complex.I • switchOp2`. -/
def capstoneQubitSpine : LeibnizDerivationFrechetOnsagerSpine 2 :=
  canonicalAutCapstoneSpine
    (conjStarAlgEquiv 2)
    (conjStarAlgEquiv_involutive (n := 2))
    d63FrechetOperatorCut
    tiltOp2
    switchOp2
    (Complex.I • switchOp2)
    tiltOp2_isSelfAdjoint
    (tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint)
    conj_tiltOp2
    (conjStarAlgEquiv_trace_re (n := 2))
    conj_switchOp2
    (conjStarAlgEquiv_purelyImaginary_odd switchOp2 conj_switchOp2)
    0

end CoreSpineStructures

/-! ## Section 2: Gap A + Gap B Integration (`T3-AB-01`, `T3-AB-02`) -/

section GapAB_CartanPeirceCEBKM

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- **`T3-AB-01` (Gap A + Gap B):** Embeds Peirce `cutDerivation P` via
`FrechetBridge.toRealDerivation (cutDerivation P) : Carrier n` (`= peirceCutGenerator P`
under `peirceCutDerivationLieLane n`) into `finiteGibbsCEParityOnsagerSystem`, verifying
exact centered BKM dissipation, CE curvature probe pairing, nonnegativity, and
Onsager–Casimir master reciprocity. -/
theorem gapAB_peirceCut_ceBKM_parity_bridge {n : ℕ}
    (P : PeirceCut n) (H a Q : GibbsOperator n)
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (ha : IsSelfAdjoint a) (hQ : IsSelfAdjoint Q)
    (y : Carrier n) :
    let d_cut : Carrier n := FrechetBridge.toRealDerivation (cutDerivation P)
    let PS := finiteGibbsCEParityOnsagerSystem H hH hZ a Q ha hQ
    let D := faithfulGibbsDensity H hH hZ
    let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
    ((peirceCutDerivationLieLane n).operatorAction (peirceCutGenerator P) a =
        finiteCEOperatorForm n a d_cut) ∧
      PS.dissipative d_cut d_cut = centeredCEBKMForm D hpow a d_cut d_cut ∧
      PS.reversible d_cut y = ceCurvatureBKMProbeForm D hpow a Q d_cut y ∧
      0 ≤ PS.totalGenerator d_cut d_cut ∧
      PS.totalGenerator (PS.T.op d_cut) (PS.T.op y) = PS.totalGenerator y d_cut := by
  intro d_cut PS D hpow
  refine ⟨rfl, ?_, ?_, PS.entropy_production_nonneg d_cut,
    PS.onsager_casimir_master_reciprocity d_cut y⟩
  · dsimp only [PS, finiteGibbsCEParityOnsagerSystem, finiteCEParityOnsagerSystem,
      finiteCEParityOnsagerSystem_of_parity, finiteCEOnsagerSystem]
  · dsimp only [PS, finiteGibbsCEParityOnsagerSystem, finiteCEParityOnsagerSystem,
      finiteCEParityOnsagerSystem_of_parity, finiteCEOnsagerSystem]

/-- **`T3-AB-02` (Gap A + Gap B):** Lifts any `CartanOnsagerSplit A` parity system
(`cartanParityOnsagerSystemOfForms`) along a frame `v : Fin m → K.L` into
`ParityOnsagerFormPairing K.L A m`, establishing `T`-even dissipation, `T`-odd
reversibility, `ceCurvature_eq` compatibility (`m = 2`), and master reciprocity. -/
theorem gapAB_cartanSplit_parityFormPairing_bridge
    {A : Type*} [Ring A] [Algebra ℝ A]
    (C : CartanOnsagerSplit A) (K : DerivationLieLane ℝ A)
    (g : LinearMap.BilinForm ℝ A)
    (hg_symm : ∀ x y, g x y = g y x) (hg_nonneg : ∀ x, 0 ≤ g x x)
    (η : LinearMap.BilinForm ℝ A)
    (Γ₁ Γ₂ : OneForm K) (v : Fin 2 → K.L) :
    let PS := cartanParityOnsagerSystemOfForms C g hg_symm hg_nonneg η
    let PP := ParityOnsagerFormPairing.ofValueParity PS v
    let F₁ := ceCurvature K (oneFormAlternatingLinearEquiv K Γ₁)
    let F₂ := ceCurvature K (oneFormAlternatingLinearEquiv K Γ₂)
    PP.dissipative (PP.T.op F₁) (PP.T.op F₂) = PP.dissipative F₁ F₂ ∧
      PP.reversible (PP.T.op F₁) (PP.T.op F₂) = -PP.reversible F₁ F₂ ∧
      F₁ = twoCochainEquivDerivationOperatorForm K (connectionCurvature K Γ₁) ∧
      PP.totalGenerator (PP.T.op F₁) (PP.T.op F₂) = PP.totalGenerator F₂ F₁ := by
  intro PS PP F₁ F₂
  refine ⟨PP.dissipative_T_even F₁ F₂, PP.reversible_T_odd F₁ F₂, ceCurvature_eq K Γ₁,
    onsager_pairing_ceCurvature_reciprocity K PP
      (oneFormAlternatingLinearEquiv K Γ₁) (oneFormAlternatingLinearEquiv K Γ₂)⟩

end GapAB_CartanPeirceCEBKM

/-! ## Section 3: Gap B + Gap C Integration (`T3-BC-01`, `T3-BC-02`) -/

section GapBC_FrechetCEBKMTrajectory

open scoped Matrix.Norms.L2Operator

/-- **`T3-BC-01` & `T3-BC-02` (Gap B + Gap C):** Along a differentiable self-adjoint
Hamiltonian curve `H : ℝ → GibbsOperator n` whose normalized matrix density
`rho t := matrixOfOp (normalizedExponential (H t))` satisfies a `MetriplecticDissipativeSystem`
trajectory for `Φ : Matrix (Fin n) (Fin n) ℂ → ℝ`, simultaneously proves:
1. Instantaneous Fréchet log-partition exterior derivative vanishes (`frechetExtDeriv = 0`)
   and BKM Hessian equals `centeredBKMRealCovariance` and the `CEBKM` dissipative form,
2. Instantaneous `finiteGibbsCEParityOnsagerSystemOfAut` Onsager–Casimir reciprocity, and
3. Trajectory-level `HasDerivAt (Φ ∘ rho) _ t` with `deriv (Φ ∘ rho) t ≤ 0` and
   convex-interval `AntitoneOn (Φ ∘ rho) I`. -/
theorem gapBC_frechetHessian_gibbsTrajectory_secondLaw
    {n : ℕ} [Nonempty (Fin n)]
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H : ℝ → GibbsOperator n) (a Q : GibbsOperator n)
    {I : Set ℝ} (hI : Convex ℝ I)
    (hH : ∀ t ∈ I, IsSelfAdjoint (H t))
    (hτ_H : ∀ t ∈ I, τ (H t) = H t)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (ha : τ a = a) (hQ : τ Q = -Q)
    (D₁ D₂ : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hA₁ : IsSelfAdjoint (finiteCEOperatorForm n a (finiteCEFrechetDirection D₁)))
    (hA₂ : IsSelfAdjoint (finiteCEOperatorForm n a (finiteCEFrechetDirection D₂)))
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (dΦ : ℝ → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ))
    (sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n))
    (hcont : ContinuousOn (fun s => Φ (matrixOfOp (normalizedExponential (H s)))) I)
    (hmob : ∀ (t : ℝ) (ht : t ∈ interior I) (X : Matrix (Fin n) (Fin n) ℂ),
      (sys t).Onsager X =
        matrixKuboMoriMobility
          (faithfulGibbsDensity (H t) (hH t (interior_subset ht))
            (tracedExponential_re_pos_of_isSelfAdjoint (H t) (hH t (interior_subset ht))))
          (continuous_faithfulGibbsDensity_rpow (H t) (hH t (interior_subset ht))
            (tracedExponential_re_pos_of_isSelfAdjoint (H t) (hH t (interior_subset ht)))) X)
    (hrev : ∀ t ∈ interior I,
      (Matrix.trace (star (sys t).grad_F *
        (-Complex.I • ((sys t).H * (sys t).rho - (sys t).rho * (sys t).H)))).re = 0)
    (hrho : ∀ t ∈ interior I,
      HasDerivAt (fun s => matrixOfOp (normalizedExponential (H s)))
        (MetriplecticDissipation.stateEvolution (sys t)) t)
    (hΦ : ∀ t ∈ interior I,
      HasFDerivAt Φ (dΦ t) (matrixOfOp (normalizedExponential (H t))))
    (hdΦ : ∀ t ∈ interior I, ∀ V, dΦ t V = (Matrix.trace (star (sys t).grad_F * V)).re) :
    (∀ t (ht : t ∈ I),
      let hZ := tracedExponential_re_pos_of_isSelfAdjoint (H t) (hH t ht)
      let x₁ := finiteCEFrechetDirection D₁
      let x₂ := finiteCEFrechetDirection D₂
      let A₁ := finiteCEOperatorForm n a x₁
      let A₂ := finiteCEOperatorForm n a x₂
      let PS := finiteGibbsCEParityOnsagerSystemOfAut τ hτ_inv (H t) (hH t ht) hZ
        (hτ_H t ht) hτ_tr a Q ha hQ
      frechetExtDeriv (logPartitionOneForm n) (H t) ![A₁, A₂] = 0 ∧
        (secondFDerivLogPartitionReadout (H t) A₁ A₂).re = PS.dissipative x₁ x₂ ∧
        PS.totalGenerator (PS.T.op x₁) (PS.T.op x₂) = PS.totalGenerator x₂ x₁) ∧
      (∀ t ∈ interior I,
        HasDerivAt (fun s => Φ (matrixOfOp (normalizedExponential (H s))))
          (MetriplecticDissipation.freeEnergyRate (sys t)) t ∧
        deriv (fun s => Φ (matrixOfOp (normalizedExponential (H s)))) t ≤ 0) ∧
      AntitoneOn (fun s => Φ (matrixOfOp (normalizedExponential (H s)))) I := by
  let rho : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun s => matrixOfOp (normalizedExponential (H s))
  let D_op : ℝ → FaithfulDensityOperator n := fun t =>
    by
      classical
      exact if ht : IsSelfAdjoint (H t) then
        faithfulGibbsDensity (H t) ht (tracedExponential_re_pos_of_isSelfAdjoint (H t) ht)
      else
        maximallyMixedFaithfulDensity n
  have hD_pow : ∀ t, Continuous (D_op t).rpow := fun t => by
    classical
    by_cases ht : IsSelfAdjoint (H t)
    · simp only [D_op, dif_pos ht]
      exact continuous_faithfulGibbsDensity_rpow (H t) ht
        (tracedExponential_re_pos_of_isSelfAdjoint (H t) ht)
    · simp only [D_op, dif_neg ht]
      exact continuous_maximallyMixedFaithfulDensity_rpow n
  have hmob' : ∀ t ∈ interior I, ∀ X,
      (sys t).Onsager X = matrixKuboMoriMobility (D_op t) (hD_pow t) X := by
    intro t ht X
    have hHt : IsSelfAdjoint (H t) := hH t (interior_subset ht)
    have hD_eq : D_op t = faithfulGibbsDensity (H t) hHt
        (tracedExponential_re_pos_of_isSelfAdjoint (H t) hHt) := by
      classical
      simp [D_op, hHt]
    have hD_eq_fun : ∀ (h1 : Continuous (D_op t).rpow)
        (h2 : Continuous (faithfulGibbsDensity (H t) hHt
          (tracedExponential_re_pos_of_isSelfAdjoint (H t) hHt)).rpow),
        matrixKuboMoriMobility (D_op t) h1 X =
          matrixKuboMoriMobility (faithfulGibbsDensity (H t) hHt
            (tracedExponential_re_pos_of_isSelfAdjoint (H t) hHt)) h2 X := by
      intro h1 h2
      subst hD_eq
      rfl
    rw [hmob t ht X]
    exact (hD_eq_fun (hD_pow t) _).symm
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hZ := tracedExponential_re_pos_of_isSelfAdjoint (H t) (hH t ht)
    have huni := logPartitionOneForm_finiteGibbs_aut_unification τ hτ_inv (H t) a Q
      (hH t ht) hZ (hτ_H t ht) hτ_tr ha hQ D₁ D₂ hA₁ hA₂
    exact ⟨huni.2.2.1, huni.2.2.2.1, huni.2.2.2.2⟩
  · intro t ht
    exact ⟨hasDerivAt_freeEnergy_of_matrixKuboMoriMobility Φ dΦ rho sys
        (hrho t ht) (hΦ t ht) (hdΦ t ht),
      deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility_of_reversible_orthogonal Φ dΦ rho sys
        D_op hD_pow (hmob' t ht) (hrev t ht) (hrho t ht) (hΦ t ht) (hdΦ t ht)⟩
  · exact antitoneOn_freeEnergy_of_matrixKuboMoriMobility_of_reversible_orthogonal Φ dΦ rho sys
      D_op hD_pow hI hcont hmob' hrev hrho hΦ hdΦ

end GapBC_FrechetCEBKMTrajectory

/-! ## Section 4: Gap A + Gap D Integration (`T3-AD-01`, `T3-AD-02`) -/

section GapAD_PeirceSuperModularCartan

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- **`T3-AD-01` (Gap A + Gap D):** Unifies the Peirce cut derivation
`FrechetBridge.toRealDerivation (cutDerivation P)` with the odd super-anticommutator
`{differentialPlusLinear ℝ P.1 A, differentialMinusLinear ℝ P.1 C}` inside
`NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n)`, proves exact inner
identification with `genV P.1 A C`, Cartan decomposition under `peirceDerivCartanOnsagerSplit P`,
and time-reversal involution on `peirceCartanTimeReversal P`. -/
theorem gapAD_peirceCut_superAnticomm_cartan_bridge {n : ℕ}
    (P : PeirceCut n) (A C X : FiniteOperatorAlgebra n) :
    let d_cut : NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n) :=
      FrechetBridge.toRealDerivation (cutDerivation P)
    let d_anti : NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n) :=
      superAnticommLinearToDerivations (invS_sq P.property)
        (differentialPlusLinear_isOdd (R := ℝ) P.property A)
        (differentialMinusLinear_isOdd (R := ℝ) P.property C)
    let S_der := peirceDerivCartanOnsagerSplit P
    let S_op := peirceSymmetricLieAlgebra P
    d_cut ∈ S_der.drazinCore ∧
      (d_anti : Module.End ℝ (FiniteOperatorAlgebra n)) X =
        genV (P : FiniteOperatorAlgebra n) A C * X -
          X * genV (P : FiniteOperatorAlgebra n) A C ∧
      (peirceCartanTimeReversal P).op (S_op.P_plus X) = -S_op.P_plus X ∧
      (peirceCartanTimeReversal P).op (S_op.P_minus X) = S_op.P_minus X := by
  intro d_cut d_anti S_der S_op
  refine ⟨?_, ?_, peirce_P_plus_cartanTimeReversal P X,
    peirce_P_minus_cartanTimeReversal P X⟩
  · change d_cut ∈ (cutStabilizer (P : FiniteOperatorAlgebra n)).toSubmodule
    exact cutDerivation_mem_cutStabilizer P
  · change differentialPlus P.1 A (differentialMinus P.1 C X) +
        differentialMinus P.1 C (differentialPlus P.1 A X) = _
    simpa [PureNonCommutativeOperatorSpine.comm] using
      differentialPlus_differentialMinus_pair A C X P.property

/-- **`T3-AD-02` (Gap A + Gap D):** Given any `DerivationLieLane ℝ A` equipped with
an involutive Lie algebra automorphism `InvolutiveLieAut K.L` (including bridged
`Modular.KMSState.LinearDerivation` via `realDerivationLieLane`, `CrossProdCarrier` via
`crossProdCarrierDerivationLieLane`, and `ZornVectorMatrix` via `zornVectorMatrixDerivationLieLane`),
constructs the induced `CartanOnsagerSplit K.L` (`onsager := S.P_minus`) and
`ParityOnsagerSystem K.L`, proving PSD dissipation and Onsager–Casimir reciprocity. -/
theorem gapAD_bridgedLane_cartanOnsager_bridge
    {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (K : DerivationLieLane ℝ A)
    (θ : InvolutiveLieAut K.L)
    (g : LinearMap.BilinForm ℝ K.L)
    (hg_symm : ∀ x y, g x y = g y x) (hg_nonneg : ∀ x, 0 ≤ g x x)
    (η : LinearMap.BilinForm ℝ K.L)
    (x y : K.L) :
    let S : SymmetricLieAlgebra K.L := { toInvolutiveLieAut := θ }
    let C : CartanOnsagerSplit K.L :=
      { S := S
        onsager := S.P_minus
        drazinCore := S.𝔨
        dissipativeRange := S.𝔭
        drazinCore_eq_k := rfl
        dissipativeRange_eq_p := rfl }
    let PS := cartanParityOnsagerSystemOfForms C g hg_symm hg_nonneg η
    0 ≤ PS.dissipative x x ∧
      PS.totalGenerator (PS.T.op x) (PS.T.op y) = PS.totalGenerator y x := by
  intro S C PS
  exact ⟨PS.dissipative_nonneg x, PS.onsager_casimir_master_reciprocity x y⟩

end GapAD_PeirceSuperModularCartan

/-! ## Section 5: Gap D + Gap B Integration (`T3-DB-01`, `T3-DB-02`) -/

section GapDB_ModularSuperBraidedCEBKM

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- **`T3-DB-01` (Gap D + Gap B):** Transports `Modular.KMSState.LinearDerivation ℝ (GibbsOperator n)`
and `Modular.SemidirectExterior.Derivation ℝ (GibbsOperator n)` into `Carrier n`
(`NonAssocDerivation.derivations ℝ (GibbsOperator n)`), evaluating `finiteGibbsCEParityOnsagerSystemOfAut`
and `ParityOnsagerFormPairing (Carrier n) (GibbsOperator n) 1` with `T`-even dissipation,
`T`-odd reversibility, and master reciprocity. -/
theorem gapDB_modularDerivation_ceBKM_parityForm_bridge {n : ℕ}
    (τ : GibbsOperator n ≃⋆ₐ[ℝ] GibbsOperator n) (hτ_inv : ∀ X, τ (τ X) = X)
    (H a Q : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hτ_H : τ H = H)
    (hτ_tr : ∀ X : GibbsOperator n, (finiteOperatorTrace (τ X)).re = (finiteOperatorTrace X).re)
    (ha : τ a = a) (hQ : τ Q = -Q)
    (D_kms : InfoGeometry.Modular.KMSState.LinearDerivation ℝ (GibbsOperator n))
    (D_semi : InfoGeometry.Modular.SemidirectExterior.Derivation ℝ (GibbsOperator n)) :
    let d₁ : Carrier n := kmsStateLinearDerivationEquivDerivations D_kms
    let d₂ : Carrier n := semidirectDerivationEquivDerivations D_semi
    let PS := finiteGibbsCEParityOnsagerSystemOfAut τ hτ_inv H hH hZ hτ_H hτ_tr a Q ha hQ
    let D := faithfulGibbsDensity H hH hZ
    let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
    let PP := ParityOnsagerFormPairing.ofValueParity PS ![d₁]
    let ω₁ : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) 1 :=
      oneFormAlternatingLinearEquiv (realDerivationsLane (GibbsOperator n))
        (exteriorDerivativeZero (realDerivationsLane (GibbsOperator n)) a)
    let ω₂ : DerivationOperatorForm (realDerivationsLane (GibbsOperator n)) 1 :=
      oneFormAlternatingLinearEquiv (realDerivationsLane (GibbsOperator n))
        (exteriorDerivativeZero (realDerivationsLane (GibbsOperator n)) (a + Q))
    PS.dissipative d₁ d₂ = centeredBKMRealCovariance D hpow (D_kms.toLinearMap a) (D_semi a) ∧
      PS.totalGenerator (PS.T.op d₁) (PS.T.op d₂) = PS.totalGenerator d₂ d₁ ∧
      PP.totalGenerator (PP.T.op ω₁) (PP.T.op ω₂) = PP.totalGenerator ω₂ ω₁ := by
  intro d₁ d₂ PS D hpow PP ω₁ ω₂
  refine ⟨?_, PS.onsager_casimir_master_reciprocity d₁ d₂,
    onsager_pairing_derivationForm_reciprocity (realDerivationsLane (GibbsOperator n)) PP ω₁ ω₂⟩
  change centeredCEBKMForm D hpow a d₁ d₂ = _
  rw [centeredCEBKMForm_apply]
  rfl

/-- **`T3-DB-02` (Gap D + Gap B):** Transports the odd Peirce super-anticommutator
`{differentialPlusLinear ℝ P.1 A, differentialMinusLinear ℝ P.1 C}` and any
ordinary-Leibniz `GradedBraidedDerivation` (`gradedBraidedDerivationToDerivations`) on
`GibbsOperator n` into `Carrier n`, evaluating `centeredCEBKMForm`, `ceCurvatureBKMProbeForm`,
and `ceCurvature` reciprocity under `starDerivationTimeReversal`. -/
theorem gapDB_superBraided_ceBKM_curvature_bridge {n : ℕ}
    {Γ : Type*} [AddCommMonoid Γ]
    {B : InfoGeometry.Canonical.GradingBicharacter Γ ℝ} {grade : Γ → AddSubgroup (GibbsOperator n)}
    (P : PeirceCut n) (A C H a Q : GibbsOperator n)
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (ha : IsSelfAdjoint a) (hQ : IsSelfAdjoint Q)
    (D_br : GradedBraidedDerivation Γ ℝ (GibbsOperator n) B grade)
    (hL : IsLeibniz ℝ (GibbsOperator n) (gradedBraidedDerivationToLinearMap D_br)) :
    let d_super : Carrier n :=
      superAnticommLinearToDerivations (invS_sq P.property)
        (differentialPlusLinear_isOdd (R := ℝ) P.property A)
        (differentialMinusLinear_isOdd (R := ℝ) P.property C)
    let d_br : Carrier n := gradedBraidedDerivationToDerivations D_br hL
    let PS := finiteGibbsCEParityOnsagerSystem H hH hZ a Q ha hQ
    let D := faithfulGibbsDensity H hH hZ
    let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
    let K := realDerivationsLane (GibbsOperator n)
    let PP2 := centeredBKMOnsagerFormPairing_ofValueParity D hpow Q hQ ![d_super, d_br]
    let Γ_ce := oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K a)
    PS.dissipative d_super d_br =
        centeredBKMRealCovariance D hpow (genV P.1 A C * a - a * genV P.1 A C) (D_br a) ∧
      PS.reversible d_super d_br = ceCurvatureBKMProbeForm D hpow a Q d_super d_br ∧
      PP2.totalGenerator (PP2.T.op (ceCurvature K Γ_ce)) (PP2.T.op (ceCurvature K Γ_ce)) =
        PP2.totalGenerator (ceCurvature K Γ_ce) (ceCurvature K Γ_ce) := by
  intro d_super d_br PS D hpow K PP2 Γ_ce
  refine ⟨?_, rfl, centeredBKM_ceCurvature_reciprocity PP2 Γ_ce Γ_ce⟩
  change centeredCEBKMForm D hpow a d_super d_br = _
  rw [centeredCEBKMForm_apply]
  have hsuper : finiteCEOperatorForm n a d_super = genV P.1 A C * a - a * genV P.1 A C := by
    change differentialPlus P.1 A (differentialMinus P.1 C a) +
        differentialMinus P.1 C (differentialPlus P.1 A a) = _
    simpa [PureNonCommutativeOperatorSpine.comm] using
      differentialPlus_differentialMinus_pair A C a P.property
  rw [hsuper]
  rfl

end GapDB_ModularSuperBraidedCEBKM

/-! ## Section 6: Gap C + Gap D Integration (`T3-CD-01`, `T3-CD-02`) -/

section GapCD_ModularExceptionalTrajectory

/-- **`T3-CD-01` (Gap C + Gap D):** Couples a bridged `Modular.TimeSemigroup.Derivation A`
(via `timeSemigroupDerivationEquivDerivations`) into a normed `GenericMetriplecticFlow.System V`
trajectory (`x'(t) = (sys t).flow` with dissipative drift induced by a linear readout of the
bridged derivation), proving `HasDerivAt (Φ ∘ x) _ t` with nonpositive slope and `AntitoneOn`. -/
theorem gapCD_modularDerivation_metriplecticFlow_secondLaw
    {A V : Type*} [Ring A] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D_mod : InfoGeometry.Modular.TimeSemigroup.Derivation A)
    (embed : NonAssocDerivation.derivations ℤ A →+ V)
    (a : A)
    (sys : ℝ → GenericMetriplecticFlow.System V)
    (Φ : V → ℝ) (dΦ : V → (V →L[ℝ] ℝ))
    (x : ℝ → V) {I : Set ℝ} (hI : Convex ℝ I)
    (hcont : ContinuousOn (fun s => Φ (x s)) I)
    (hΦ : ∀ t ∈ interior I, HasFDerivAt Φ (dΦ (x t)) (x t))
    (h_diss_eq : ∀ t ∈ interior I,
      (sys t).M (sys t).dS = embed (timeSemigroupDerivationEquivDerivations D_mod))
    (hx : ∀ t ∈ interior I,
      HasDerivAt x ((sys t).L (sys t).dH +
        embed (timeSemigroupDerivationEquivDerivations D_mod)) t)
    (hrev : ∀ t ∈ interior I, dΦ (x t) ((sys t).L (sys t).dH) = 0)
    (hdiss : ∀ t ∈ interior I,
      dΦ (x t) (embed (timeSemigroupDerivationEquivDerivations D_mod)) ≤ 0) :
    (D_mod (a * a) = D_mod a * a + a * D_mod a) ∧
      (∀ t ∈ interior I,
        HasDerivAt (fun s => Φ (x s)) (dΦ (x t) ((sys t).M (sys t).dS)) t ∧
        dΦ (x t) ((sys t).M (sys t).dS) ≤ 0) ∧
      AntitoneOn (fun s => Φ (x s)) I := by
  refine ⟨D_mod.leibniz' a a, ?_, ?_⟩
  · intro t ht
    have hpt := banach_metriplectic_hasDerivAt_nonpos
      (v_rev := fun s => (sys s).L (sys s).dH)
      (v_diss := fun s => (sys s).M (sys s).dS)
      (hΦ t ht) (by simpa only [h_diss_eq t ht] using hx t ht)
      (hrev t ht) (by simpa only [h_diss_eq t ht] using hdiss t ht)
    exact hpt
  · exact banach_metriplectic_antitoneOn
      (v_rev := fun s => (sys s).L (sys s).dH)
      (v_diss := fun s => (sys s).M (sys s).dS)
      hI hcont hΦ
      (fun t ht => by simpa only [h_diss_eq t ht] using hx t ht)
      hrev
      (fun t ht => by simpa only [h_diss_eq t ht] using hdiss t ht)

/-- **`T3-CD-02` (Gap C + Gap D):** Couples a bridged exceptional `H3ZornF4Derivations`
element (via `h3ZornF4DerivationLane : DerivationLieLane ℝ (H3Zorn ℝ)`) into a normed
`GenericMetriplecticFlow.System V` trajectory (preserving zero global typeclass diamonds),
proving Leibniz action and convex-interval `AntitoneOn` free-energy decay. -/
theorem gapCD_exceptionalSuperDerivation_metriplecticFlow_secondLaw
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D_f4 : H3ZornF4Derivations) (x_zorn y_zorn : H3Zorn ℝ)
    (sys : ℝ → GenericMetriplecticFlow.System V)
    (H_fn S_fn : V → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (dH_clm dS_clm : ℝ → (V →L[ℝ] ℝ))
    (x : ℝ → V) {I : Set ℝ} (hI : Convex ℝ I)
    (hcont : ContinuousOn (fun s => H_fn (x s) - T * S_fn (x s)) I)
    (hdH : ∀ t ∈ interior I, ∀ v, dH_clm t v = (sys t).dH v)
    (hdS : ∀ t ∈ interior I, ∀ v, dS_clm t v = (sys t).dS v)
    (hH : ∀ t ∈ interior I, HasFDerivAt H_fn (dH_clm t) (x t))
    (hS : ∀ t ∈ interior I, HasFDerivAt S_fn (dS_clm t) (x t))
    (hx : ∀ t ∈ interior I, HasDerivAt x (sys t).flow t) :
    h3ZornF4DerivationLane.operatorAction D_f4 (x_zorn * y_zorn) =
        h3ZornF4DerivationLane.operatorAction D_f4 x_zorn * y_zorn +
          x_zorn * h3ZornF4DerivationLane.operatorAction D_f4 y_zorn ∧
      (∀ t ∈ interior I,
        HasDerivAt (fun s => H_fn (x s) - T * S_fn (x s))
          (-(T * (sys t).dS ((sys t).M (sys t).dS))) t ∧
        -(T * (sys t).dS ((sys t).M (sys t).dS)) ≤ 0) ∧
      AntitoneOn (fun s => H_fn (x s) - T * S_fn (x s)) I := by
  refine ⟨h3ZornF4DerivationLane.operatorAction_leibniz D_f4 x_zorn y_zorn, ?_, ?_⟩
  · intro t ht
    exact genericMetriplectic_freeEnergy_hasDerivAt_nonpos hT
      (hdH t ht) (hdS t ht) (hH t ht) (hS t ht) (hx t ht)
  · exact genericMetriplectic_freeEnergy_antitoneOn hT hI hcont hdH hdS hH hS hx

end GapCD_ModularExceptionalTrajectory

/-! ## Section 7: Gap A + Gap C Integration (`T3-AC-01`, `T3-AC-02`) -/

section GapAC_CartanSchurPeirceTrajectory

open scoped Matrix.Norms.L2Operator

/-- **`T3-AC-01` (Gap A + Gap C):** Couples a `CartanOnsagerSplit V` and a
`DrazinPenroseSchurTriad` (`bodyForce ≠ 0`) with a normed `GenericMetriplecticFlow.System V`
whose reversible drift `(sys t).L (sys t).dH` lies in `C.drazinCore` (`𝔨`) and
dissipative drift `(sys t).M (sys t).dS` lies in `C.dissipativeRange` (`𝔭`), proving
exact `cartanTimeReversal` signs, `energy_rate = 0`, `0 ≤ triad.entropy.production`,
and Banach trajectory `AntitoneOn`. -/
theorem gapAC_cartanSchur_metriplecticFlow_secondLaw
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : CartanOnsagerSplit V) (triad : DrazinPenroseSchurTriad)
    (hForce : triad.entropy.bodyForce ≠ 0)
    (sys : ℝ → GenericMetriplecticFlow.System V)
    (H_fn S_fn : V → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (dH_clm dS_clm : ℝ → (V →L[ℝ] ℝ))
    (x : ℝ → V) {I : Set ℝ} (hI : Convex ℝ I)
    (hcont : ContinuousOn (fun s => H_fn (x s) - T * S_fn (x s)) I)
    (hdH : ∀ t ∈ interior I, ∀ v, dH_clm t v = (sys t).dH v)
    (hdS : ∀ t ∈ interior I, ∀ v, dS_clm t v = (sys t).dS v)
    (hH : ∀ t ∈ interior I, HasFDerivAt H_fn (dH_clm t) (x t))
    (hS : ∀ t ∈ interior I, HasFDerivAt S_fn (dS_clm t) (x t))
    (hx : ∀ t ∈ interior I, HasDerivAt x (sys t).flow t)
    (hCore : ∀ t ∈ interior I, (sys t).L (sys t).dH ∈ C.drazinCore)
    (hRange : ∀ t ∈ interior I, (sys t).M (sys t).dS ∈ C.dissipativeRange) :
    (∀ t ∈ interior I,
      (cartanTimeReversal C).op ((sys t).L (sys t).dH) = -((sys t).L (sys t).dH) ∧
      (cartanTimeReversal C).op ((sys t).M (sys t).dS) = (sys t).M (sys t).dS ∧
      (sys t).dH (sys t).flow = 0) ∧
      0 ≤ (triadEffectiveParityOnsagerSystem triad hForce).dissipative
        triad.entropy.bodyForce triad.entropy.bodyForce ∧
      AntitoneOn (fun s => H_fn (x s) - T * S_fn (x s)) I := by
  refine ⟨?_, ?_, genericMetriplectic_freeEnergy_antitoneOn hT hI hcont hdH hdS hH hS hx⟩
  · intro t ht
    exact ⟨cartanTimeReversal_eq_neg_of_mem_drazinCore C (hCore t ht),
      cartanTimeReversal_eq_self_of_mem_dissipativeRange C (hRange t ht),
      (sys t).energy_rate⟩
  · exact (triadEffectiveParityOnsagerSystem triad hForce).dissipative_nonneg
      triad.entropy.bodyForce

/-- **`T3-AC-02` (Gap A + Gap C):** Projects evolving Hamiltonian gradients along
`peirceCartanLinearEquiv P` (`evenGrade P` in `ker(ad_P²)` + `oddGrade P` in `range ad_P`),
showing `cutDerivation P` annihilates the Peirce-even `𝔨` component while
`hasDerivAt_traceNormalizedSquarePotential_gibbsTrajectory` establishes trajectory-level
`HasDerivAt`, `deriv ≤ 0`, and `AntitoneOn` for `traceNormalizedSquarePotential`. -/
theorem gapAC_peirceCut_matrixKuboMori_secondLaw
    {n : ℕ} [Nonempty (Fin n)]
    (P : PeirceCut n) (H_eq σ : FiniteOperatorAlgebra n)
    (hH_eq : IsSelfAdjoint H_eq) (hσ : IsSelfAdjoint σ) (hcomm_σ : Commute σ H_eq)
    (H : ℝ → FiniteOperatorAlgebra n) {I : Set ℝ} (hI : Convex ℝ I)
    (hH : ∀ t ∈ I, IsSelfAdjoint (H t))
    (hflow : ∀ t (ht : t ∈ I),
      HasDerivAt H
        (gibbsUnitaryVectorField H_eq (H t) -
          ((faithfulGibbsDensity (H t) (hH t ht)
              (tracedExponential_re_pos_of_isSelfAdjoint (H t) (hH t ht))).rho - σ)) t) :
    (∀ t ∈ I,
      cutDerivation P ((peirceCartanLinearEquiv P (H t)).1 : FiniteOperatorAlgebra n) = 0 ∧
      cutDerivation P (cutDerivation P (H t)) =
        ((peirceCartanLinearEquiv P (H t)).2 : FiniteOperatorAlgebra n)) ∧
      (∀ t (ht : t ∈ I),
        HasDerivAt
          (fun s => traceNormalizedSquarePotential (matrixOfOp σ)
            (matrixOfOp (normalizedExponential (H s))))
          (MetriplecticDissipation.freeEnergyRate
            (evolvingGibbsMetriplecticSystem H_eq σ (H t) (hH t ht))) t ∧
        deriv
          (fun s => traceNormalizedSquarePotential (matrixOfOp σ)
            (matrixOfOp (normalizedExponential (H s)))) t ≤ 0) ∧
      AntitoneOn
        (fun s => traceNormalizedSquarePotential (matrixOfOp σ)
          (matrixOfOp (normalizedExponential (H s)))) I := by
  refine ⟨?_, ?_,
    antitoneOn_traceNormalizedSquarePotential_gibbsTrajectory
      H_eq σ hH_eq hσ hcomm_σ H hI hH hflow⟩
  · intro t _
    have hsplit := peirceCartanLinearEquiv_apply P (H t)
    refine ⟨?_, ?_⟩
    · rw [hsplit.1]
      exact cutDerivation_evenGrade_zero P (H t)
    · rw [hsplit.2]
      exact cutDerivation_square_eq_oddGrade P (H t)
  · intro t ht
    exact hasDerivAt_traceNormalizedSquarePotential_gibbsTrajectory
      H_eq σ hH_eq hσ hcomm_σ H (hH t ht) (hflow t ht)

end GapAC_CartanSchurPeirceTrajectory

/-! ## Section 8: Master Four-Pillar Synthesis & Non-Degenerate `n = 2` Witness -/

section FourPillarMasterSynthesisAndWitness

/-- Master four-pillar unification theorem connecting any
`LeibnizDerivationFrechetOnsagerSpine n` with `UnifiedDerivationOnsagerFormSpine (GibbsOperator n)`
across `Leibniz`, `Derivation`, `Fréchet`, and `Onsager`, together with trajectory-level
`AntitoneOn` monotonicity of `gibbsRelativePotential σ` along `gibbsMetriplecticFlow`. -/
theorem four_pillar_unified_capstone {n : ℕ} [Nonempty (Fin n)]
    (S : LeibnizDerivationFrechetOnsagerSpine n)
    (U : UnifiedDerivationOnsagerFormSpine (GibbsOperator n))
    (v : Fin 1 → U.lane.L) (ω η : DerivationOperatorForm U.lane 1)
    (D₁ D₂ : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hA₁ : IsSelfAdjoint (finiteCEOperatorForm n S.observable (finiteCEFrechetDirection D₁)))
    (H_eq σ : GibbsOperator n) (hσ : IsSelfAdjoint σ) (hcomm_σ : Commute σ H_eq)
    (H_curve : ℝ → GibbsOperator n) {I : Set ℝ} (hI : Convex ℝ I)
    (hH_curve : ∀ t ∈ I, IsSelfAdjoint (H_curve t))
    (hflow : ∀ t (ht : t ∈ I),
      HasDerivAt H_curve (gibbsMetriplecticFlow H_eq σ (H_curve t) (hH_curve t ht)) t) :
    (LinearMap.ker (peirceAdMap S.peirceCut ∘ₗ peirceAdMap S.peirceCut) =
        S.peirceCartan.drazinCore ∧
      LinearMap.range (peirceAdMap S.peirceCut) = S.peirceCartan.dissipativeRange) ∧
      ((secondFDerivLogPartitionReadout S.hamiltonian
          (finiteCEOperatorForm n S.observable (finiteCEFrechetDirection D₁))
          (finiteCEOperatorForm n S.observable (finiteCEFrechetDirection D₂))).re =
        S.ceParitySystem.dissipative
          (finiteCEFrechetDirection D₁) (finiteCEFrechetDirection D₂)) ∧
      (S.ceParitySystem.totalGenerator
          (S.ceParitySystem.T.op (finiteCEFrechetDirection D₁))
          (S.ceParitySystem.T.op (finiteCEFrechetDirection D₂)) =
        S.ceParitySystem.totalGenerator
          (finiteCEFrechetDirection D₂) (finiteCEFrechetDirection D₁)) ∧
      ((U.evalForm 1 v).totalGenerator ((U.evalForm 1 v).T.op ω) ((U.evalForm 1 v).T.op η) =
        (U.evalForm 1 v).totalGenerator η ω) ∧
      AntitoneOn (fun s => gibbsRelativePotential σ (H_curve s)) I :=
  ⟨S.peirce_split_compat,
    S.dissipative_eq_hessian D₁ D₂ hA₁,
    S.ce_reciprocity (finiteCEFrechetDirection D₁) (finiteCEFrechetDirection D₂),
    U.form_reciprocity 1 v ω η,
    antitoneOn_gibbsRelativePotential_metriplectic H_eq σ hσ hcomm_σ H_curve hI hH_curve hflow⟩

private theorem faithfulGibbsDensity_tiltOp2_ne_maximallyMixed
    (hZ : 0 < gibbsPartitionReal tiltOp2) :
    (faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ).rho ≠
      (1 / 2 : ℝ) • (1 : GibbsOperator 2) := by
  intro heq
  letI : NormedSpace ℝ (GibbsOperator 2) :=
    NormedSpace.restrictScalars ℝ ℂ (GibbsOperator 2)
  letI : NormedAlgebra ℝ (GibbsOperator 2) :=
    NormedAlgebra.restrictScalars ℝ ℂ (GibbsOperator 2)
  letI : StarModule ℝ (GibbsOperator 2) := ⟨by
    intro r x
    change star ((r : ℂ) • x) = r • star x
    rw [star_smul]
    simpa [Complex.star_def] using
      (real_smul_eq_complex_smul r (star x)).symm⟩
  let Z := gibbsPartitionReal tiltOp2
  let D := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ
  have hcfc : D.rho = cfc (normalizedScalarGibbsWeight Z) tiltOp2 :=
    faithfulGibbsDensity_rho_eq_normalizedGibbsCFC tiltOp2 tiltOp2_isSelfAdjoint hZ
  have hhalf : ((1 / 2 : ℝ) • (1 : GibbsOperator 2)) =
      cfc (fun _ : ℝ => (1 / 2 : ℝ)) tiltOp2 := by
    rw [cfc_const (fun _ : ℝ => (1 / 2 : ℝ)) tiltOp2]
    change (1 / 2 : ℝ) • (1 : GibbsOperator 2) = (algebraMap ℝ (GibbsOperator 2)) (1 / 2 : ℝ)
    rw [Algebra.algebraMap_eq_smul_one]
  have hsub_zero :
      cfc (fun x : ℝ => normalizedScalarGibbsWeight Z x - 1 / 2) tiltOp2 = 0 := by
    let f : ℝ → ℝ := normalizedScalarGibbsWeight Z
    let g : ℝ → ℝ := fun _ => (1 / 2 : ℝ)
    have hf : ContinuousOn f (spectrum ℝ tiltOp2) :=
      (continuous_const.mul Real.continuous_exp).continuousOn
    have hg : ContinuousOn g (spectrum ℝ tiltOp2) := continuousOn_const
    rw [cfc_sub f g tiltOp2 hf hg, ← hcfc, ← hhalf, heq, sub_self]
  have hspec_eq :
      ∀ x ∈ spectrum ℝ tiltOp2, normalizedScalarGibbsWeight Z x - 1 / 2 = 0 := by
    have hcont : ContinuousOn (fun x : ℝ => normalizedScalarGibbsWeight Z x - 1 / 2)
        (spectrum ℝ tiltOp2) :=
      ((continuous_const.mul Real.continuous_exp).sub continuous_const).continuousOn
    exact (cfc_eq_zero_iff (R := ℝ) tiltOp2 _ hcont).mp hsub_zero
  have h_one_ne : tiltOp2 - (1 : GibbsOperator 2) ≠ 0 := by
    intro h0
    have hm := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 1 1) h0
    rw [show matrixOfOp (tiltOp2 - (1 : GibbsOperator 2)) =
        matrixOfOp tiltOp2 - matrixOfOp (1 : GibbsOperator 2) from
      (LinearMap.toMatrix (ketBasis (Fin 2)) (ketBasis (Fin 2))).map_sub _ _,
      tiltOp2, matrixOfOp_matrixOp,
      show (1 : GibbsOperator 2) = ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2) from rfl,
      matrixOfOp_id, matrixOfOp_zero] at hm
    norm_num [tilt2] at hm
  have h_neg_one_ne : tiltOp2 + (1 : GibbsOperator 2) ≠ 0 := by
    intro h0
    have hm := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 0 0) h0
    rw [show matrixOfOp (tiltOp2 + (1 : GibbsOperator 2)) =
        matrixOfOp tiltOp2 + matrixOfOp (1 : GibbsOperator 2) from
      (LinearMap.toMatrix (ketBasis (Fin 2)) (ketBasis (Fin 2))).map_add _ _,
      tiltOp2, matrixOfOp_matrixOp,
      show (1 : GibbsOperator 2) = ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2) from rfl,
      matrixOfOp_id, matrixOfOp_zero] at hm
    norm_num [tilt2] at hm
  have h_prod1 : (tiltOp2 - 1) * (tiltOp2 + 1) = 0 := by
    calc
      (tiltOp2 - 1) * (tiltOp2 + 1) = tiltOp2 * tiltOp2 - 1 := by noncomm_ring
      _ = 0 := sub_eq_zero.mpr tiltOp2_sq
  have h_prod2 : (tiltOp2 + 1) * (tiltOp2 - 1) = 0 := by
    calc
      (tiltOp2 + 1) * (tiltOp2 - 1) = tiltOp2 * tiltOp2 - 1 := by noncomm_ring
      _ = 0 := sub_eq_zero.mpr tiltOp2_sq
  have h1_mem : (1 : ℝ) ∈ spectrum ℝ tiltOp2 := by
    rw [spectrum.mem_iff]
    intro hunit
    have halg : (algebraMap ℝ (GibbsOperator 2)) (1 : ℝ) - tiltOp2 = -(tiltOp2 - 1) := by
      rw [Algebra.algebraMap_eq_smul_one, one_smul]
      abel
    have hinv : (↑hunit.unit⁻¹ : GibbsOperator 2) * (-(tiltOp2 - 1)) = 1 := by
      rw [← halg]
      exact hunit.unit.inv_mul
    have hmul := congrArg (fun X : GibbsOperator 2 => X * (tiltOp2 + 1)) hinv
    rw [one_mul, mul_neg, neg_mul, ← mul_assoc, h_prod1, zero_mul, neg_zero] at hmul
    exact h_neg_one_ne hmul.symm
  have hm1_mem : (-1 : ℝ) ∈ spectrum ℝ tiltOp2 := by
    rw [spectrum.mem_iff]
    intro hunit
    have halg : (algebraMap ℝ (GibbsOperator 2)) (-1 : ℝ) - tiltOp2 = -(tiltOp2 + 1) := by
      rw [Algebra.algebraMap_eq_smul_one, neg_one_smul]
      abel
    have hinv : (↑hunit.unit⁻¹ : GibbsOperator 2) * (-(tiltOp2 + 1)) = 1 := by
      rw [← halg]
      exact hunit.unit.inv_mul
    have hmul := congrArg (fun X : GibbsOperator 2 => X * (tiltOp2 - 1)) hinv
    rw [one_mul, mul_neg, neg_mul, ← mul_assoc, h_prod2, zero_mul, neg_zero] at hmul
    exact h_one_ne hmul.symm
  have hv1 := sub_eq_zero.mp (hspec_eq 1 h1_mem)
  have hvm1 := sub_eq_zero.mp (hspec_eq (-1) hm1_mem)
  have hZne : Z⁻¹ ≠ 0 := inv_ne_zero hZ.ne'
  have hexp_eq : Real.exp 1 = Real.exp (-1) :=
    mul_left_cancel₀ hZne (hv1.trans hvm1.symm)
  exact (ne_of_gt (Real.exp_lt_exp.mpr (by norm_num : (-1 : ℝ) < 1))) hexp_eq.symm

/-- Non-degenerate concrete `n = 2` noncommutative witness on `capstoneQubitSpine`
simultaneously verifying:
1. `[switchOp2, tiltOp2] ≠ 0` (genuine noncommutativity),
2. `0 < S.ceParitySystem.dissipative x₁ x₁` and `0 < (secondFDerivLogPartitionReadout tiltOp2 A₁ A₂).re`,
3. `S.ceParitySystem.reversible x₁ x₂ ≠ 0` (`< 0`),
4. `frechetExtDeriv (logPartitionOneForm 2) tiltOp2 ![A₁, A₂] = 0`,
5. `S.ceParitySystem.totalGenerator (T x₁) (T x₂) = S.ceParitySystem.totalGenerator x₂ x₁`,
6. `deriv (fun s => gibbsRelativePotential σ_mix (H_curve s)) 0 < 0` via
   `deriv_gibbsRelativePotential_metriplectic_neg_of_ne`. -/
theorem capstone_qubit_nondegenerate_witness :
    let S := capstoneQubitSpine
    let D₁ := innerFrechetComplexDeriv (Complex.I • tiltOp2)
    let D₂ := innerFrechetComplexDeriv (Complex.I • tiltOp2 + tiltOp2 * switchOp2)
    let x₁ := finiteCEFrechetDirection D₁
    let x₂ := finiteCEFrechetDirection D₂
    let A₁ := finiteCEOperatorForm 2 switchOp2 x₁
    let A₂ := finiteCEOperatorForm 2 switchOp2 x₂
    let σ_mix : GibbsOperator 2 := (1 / 2 : ℝ) • (1 : GibbsOperator 2)
    let v_flow := gibbsMetriplecticFlow tiltOp2 σ_mix tiltOp2 tiltOp2_isSelfAdjoint
    let H_curve : ℝ → GibbsOperator 2 := fun s => tiltOp2 + s • v_flow
    (switchOp2 * tiltOp2 ≠ tiltOp2 * switchOp2) ∧
      (0 < S.ceParitySystem.dissipative x₁ x₁) ∧
      (0 < (secondFDerivLogPartitionReadout tiltOp2 A₁ A₂).re) ∧
      (S.ceParitySystem.reversible x₁ x₂ ≠ 0) ∧
      (frechetExtDeriv (logPartitionOneForm 2) tiltOp2 ![A₁, A₂] = 0) ∧
      (S.ceParitySystem.totalGenerator (S.ceParitySystem.T.op x₁) (S.ceParitySystem.T.op x₂) =
        S.ceParitySystem.totalGenerator x₂ x₁) ∧
      (deriv (fun s => gibbsRelativePotential σ_mix (H_curve s)) 0 < 0) := by
  intro S D₁ D₂ x₁ x₂ A₁ A₂ σ_mix v_flow H_curve
  have hnc : switchOp2 * tiltOp2 ≠ tiltOp2 * switchOp2 := by
    intro heq
    have hanti : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    have hsum : tiltOp2 * switchOp2 + tiltOp2 * switchOp2 = 0 := by
      calc
        tiltOp2 * switchOp2 + tiltOp2 * switchOp2 =
            tiltOp2 * switchOp2 + switchOp2 * tiltOp2 := by rw [heq]
        _ = tiltOp2 * switchOp2 + -(tiltOp2 * switchOp2) := by rw [hanti]
        _ = 0 := add_neg_cancel _
    have hmul : (2 : ℝ) • (tiltOp2 * switchOp2) = 0 := by
      rwa [two_smul ℝ (tiltOp2 * switchOp2)]
    have hprod0 : tiltOp2 * switchOp2 = 0 := by
      have hhalf := congrArg (fun Z : GibbsOperator 2 => ((2 : ℝ)⁻¹) • Z) hmul
      rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul, smul_zero] at hhalf
      exact hhalf
    have hsw0 : switchOp2 = 0 := by
      calc
        switchOp2 = (tiltOp2 * tiltOp2) * switchOp2 := by rw [tiltOp2_sq, one_mul]
        _ = tiltOp2 * (tiltOp2 * switchOp2) := by rw [mul_assoc]
        _ = 0 := by rw [hprod0, mul_zero]
    exact switchOp2_ne_zero hsw0
  have hw := logPartitionOneForm_finiteGibbs_aut_unification_nondegenerate_witness
  have hZ : 0 < gibbsPartitionReal tiltOp2 :=
    tracedExponential_re_pos_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint
  let D := faithfulGibbsDensity tiltOp2 tiltOp2_isSelfAdjoint hZ
  let hpow := continuous_faithfulGibbsDensity_rpow tiltOp2 tiltOp2_isSelfAdjoint hZ
  have hA₁_eq : A₁ = (2 * Complex.I) • (tiltOp2 * switchOp2) := by
    change (Complex.I • tiltOp2) * switchOp2 - switchOp2 * (Complex.I • tiltOp2) = _
    have hsw : switchOp2 * tiltOp2 = -(tiltOp2 * switchOp2) := by
      rw [tiltOp2_switchOp2_anticomm, neg_neg]
    rw [smul_mul_assoc, mul_smul_comm, hsw, smul_neg, sub_neg_eq_add,
      ← two_smul ℂ (Complex.I • (tiltOp2 * switchOp2)), smul_smul]
  have hdiss_pos : 0 < S.ceParitySystem.dissipative x₁ x₁ := by
    change 0 < centeredCEBKMForm D hpow switchOp2 x₁ x₁
    rw [centeredCEBKMForm_apply, centeredBKMRealCovariance_self, D.bkmRealBilinForm_apply]
    apply D.kuboMoriPairing_self_re_pos _ hpow
    intro hzero
    have hnot_gauge : A₁ ∉ BKMScalarGaugeQuotient.scalarGauge 2 := by
      rw [hA₁_eq]
      intro hmem
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
      have hm := congrArg (fun T : GibbsOperator 2 => matrixOfOp T 0 1) hr
      have hL : matrixOfOp (r • (1 : GibbsOperator 2)) 0 1 = 0 := by
        rw [matrixOfOp_real_smul]
        change (r : ℂ) * matrixOfOp (ContinuousLinearMap.id ℂ (FiniteHilbertSpace 2)) 0 1 = 0
        rw [matrixOfOp_id]
        simp
      have hR : matrixOfOp (((2 * Complex.I) • (tiltOp2 * switchOp2))) 0 1 = 2 * Complex.I := by
        rw [matrixOfOp_complex_smul]
        change (2 * Complex.I) * matrixOfOp (tiltOp2.comp switchOp2) 0 1 = 2 * Complex.I
        rw [matrixOfOp_comp, tiltOp2, switchOp2, matrixOfOp_matrixOp, matrixOfOp_matrixOp]
        have h01 : (tilt2 * switch2) 0 1 = 1 := by
          norm_num [tilt2, switch2, Matrix.mul_apply, Fin.sum_univ_two]
        rw [h01, mul_one]
      rw [hL, hR] at hm
      have him := congrArg Complex.im hm
      norm_num at him
    exact hnot_gauge ((centeredStatistic_eq_zero_iff D hpow A₁).mp hzero)
  have hSlit : tracedExponential tiltOp2 ∈ Complex.slitPlane :=
    tracedExponential_mem_slitPlane_of_isSelfAdjoint tiltOp2 tiltOp2_isSelfAdjoint
  have hExt : frechetExtDeriv (logPartitionOneForm 2) tiltOp2 ![A₁, A₂] = 0 := by
    rw [frechetExtDeriv_logPartitionOneForm_eq_zero tiltOp2 hSlit]
    rfl
  have hσ_sa : IsSelfAdjoint σ_mix := by
    rw [isSelfAdjoint_iff]
    change ContinuousLinearMap.adjoint ((1 / 2 : ℝ) • (1 : GibbsOperator 2)) = _
    rw [real_smul_eq_complex_smul, map_smul]
    change star ((1 / 2 : ℝ) : ℂ) • star (1 : GibbsOperator 2) = _
    simp [σ_mix, real_smul_eq_complex_smul]
  have hcomm_σ : Commute σ_mix tiltOp2 := by
    rw [Commute, SemiconjBy, real_smul_eq_complex_smul, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one]
  have hderiv_curve :
      HasDerivAt H_curve (gibbsMetriplecticFlow tiltOp2 σ_mix (H_curve 0) (by simpa [H_curve] using tiltOp2_isSelfAdjoint)) 0 := by
    have hsmul : HasDerivAt (fun s : ℝ => s • v_flow) v_flow 0 := by
      have hclm := ((ContinuousLinearMap.id ℝ ℝ).smulRight v_flow).hasFDerivAt.hasDerivAt
      simpa using hclm
    have hadd := (hasDerivAt_const (0 : ℝ) tiltOp2).add hsmul
    simpa [H_curve, v_flow] using hadd
  have hne :
      (faithfulGibbsDensity (H_curve 0) (by simpa [H_curve] using tiltOp2_isSelfAdjoint)
        (tracedExponential_re_pos_of_isSelfAdjoint (H_curve 0)
          (by simpa [H_curve] using tiltOp2_isSelfAdjoint))).rho ≠ σ_mix := by
    simpa [H_curve] using faithfulGibbsDensity_tiltOp2_ne_maximallyMixed hZ
  have hneg_deriv :
      deriv (fun s => gibbsRelativePotential σ_mix (H_curve s)) 0 < 0 :=
    deriv_gibbsRelativePotential_metriplectic_neg_of_ne
      tiltOp2 σ_mix hσ_sa hcomm_σ H_curve (t := 0)
      (by simpa [H_curve] using tiltOp2_isSelfAdjoint) hderiv_curve hne
  exact ⟨hnc, hdiss_pos, hw.1, ne_of_lt hw.2.1, hExt, hw.2.2, hneg_deriv⟩

end FourPillarMasterSynthesisAndWitness

end InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone
