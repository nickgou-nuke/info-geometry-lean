/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ErlangenOperator2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
import InfoGeometry.Thermo.OnsagerDifferentialFormsBridge
import InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily
import InfoGeometry.Canonical.OperatorFrechetForms
import InfoGeometry.OperatorAlgebra.KreinFrechetRiesz
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.DoubleRealKreinShearDefect

/-!
# Erlangen Operator 2.0 Bridge

Bridge from the existing coadjoint entropy symmetry interface to the abstract
`ErlangenOperatorDatum` synthesis layer.

This file is intentionally compositional: it does not construct concrete
response tensors, Onsager pairings, or Casimir involutions. Those are supplied
as owner data.
-/

namespace InfoGeometry
namespace Canonical

open InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
open InfoGeometry.Canonical.ErlangenOperator2
open InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum

/--
Pull back a coadjoint response tensor along the moment map.
-/
def responseMetricPullback
    {Sym G Gdual State : Type*}
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ) :
    State → Sym → Sym → ℝ :=
  fun s A B => responseMetric (C.data.moment s) A B

/--
Pull back a coadjoint Onsager pairing along the moment map.
-/
def onsagerPairingPullback
    {Sym G Gdual State : Type*}
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (onsagerPairing : Gdual → Sym → Sym → ℝ) :
    State → Sym → Sym → ℝ :=
  fun s A B => onsagerPairing (C.data.moment s) A B

/--
State-space invariance of the pullback response tensor follows from
coadjoint invariance plus moment equivariance.
-/
theorem responseMetricPullback_invariant
    {Sym G Gdual State : Type*}
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ)
    (hresp :
      ∀ X A B ξ,
        responseMetric (C.coadjointAction X ξ) A B =
          responseMetric ξ A B) :
    ∀ X A B s,
      responseMetricPullback C responseMetric (C.stateAction X s) A B =
        responseMetricPullback C responseMetric s A B := by
  intro X A B s
  unfold responseMetricPullback
  rw [C.moment_equivariant X s]
  exact hresp X A B (C.data.moment s)

/--
State-space `J`-reciprocity of the pullback Onsager pairing follows directly
from the coadjoint pairing reciprocity.
-/
theorem onsagerPairingPullback_reciprocity
    {Sym G Gdual State : Type*}
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (onsagerPairing : Gdual → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hons :
      ∀ A B ξ,
        onsagerPairing ξ A B =
          onsagerPairing ξ (casimirJ B) (casimirJ A)) :
    ∀ A B s,
      onsagerPairingPullback C onsagerPairing s A B =
        onsagerPairingPullback C onsagerPairing s (casimirJ B) (casimirJ A) := by
  intro A B s
  unfold onsagerPairingPullback
  exact hons A B (C.data.moment s)

/--
Build an Erlangen datum on the coadjoint carrier directly from a coadjoint
entropy symmetry context, with supplied response and Onsager/J channels.
-/
def coadjointErlangenDatum
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ)
    (onsagerPairing : Gdual → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ ξ : Gdual, C.coadjointAction 1 ξ = ξ)
    (hStateActMul :
      ∀ g h : Sym, ∀ ξ : Gdual,
        C.coadjointAction (g * h) ξ =
          C.coadjointAction g (C.coadjointAction h ξ))
    (hresp :
      ∀ X A B ξ,
        responseMetric (C.coadjointAction X ξ) A B =
          responseMetric ξ A B)
    (hons :
      ∀ A B ξ,
        onsagerPairing ξ A B =
          onsagerPairing ξ (casimirJ B) (casimirJ A)) :
    ErlangenOperatorDatum ℝ Sym Gdual Sym where
  entropy := C.entropy
  responseMetric := responseMetric
  onsagerPairing := onsagerPairing
  stateAct := C.coadjointAction
  obsAct := fun _ A => A
  casimirJ := casimirJ
  stateAct_one := hStateActOne
  stateAct_mul := hStateActMul
  obsAct_one := by
    intro A
    rfl
  obsAct_mul := by
    intro g h A
    rfl
  entropy_invariant := C.entropy_casimir_invariant
  response_invariant := by
    intro X A B s
    simpa using hresp X A B s
  onsager_reciprocity := hons

/--
Build an Erlangen datum on the underlying state carrier by pulling back entropy
through the context moment map, with supplied state-level response and Onsager/J
channels.
-/
def stateMomentErlangenDatum
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : State → Sym → Sym → ℝ)
    (onsagerPairing : State → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ s : State, C.stateAction 1 s = s)
    (hStateActMul :
      ∀ g h : Sym, ∀ s : State,
        C.stateAction (g * h) s = C.stateAction g (C.stateAction h s))
    (hresp :
      ∀ X A B s,
        responseMetric (C.stateAction X s) A B =
          responseMetric s A B)
    (hons :
      ∀ A B s,
        onsagerPairing s A B =
          onsagerPairing s (casimirJ B) (casimirJ A)) :
    ErlangenOperatorDatum ℝ Sym State Sym where
  entropy := fun s => C.entropy (C.data.moment s)
  responseMetric := responseMetric
  onsagerPairing := onsagerPairing
  stateAct := C.stateAction
  obsAct := fun _ A => A
  casimirJ := casimirJ
  stateAct_one := hStateActOne
  stateAct_mul := hStateActMul
  obsAct_one := by
    intro A
    rfl
  obsAct_mul := by
    intro g h A
    rfl
  entropy_invariant := by
    intro X s
    exact C.entropy_invariant_on_state_orbit X s
  response_invariant := by
    intro X A B s
    simpa using hresp X A B s
  onsager_reciprocity := hons

/--
Bridge closure theorem on the coadjoint carrier:
the bridge-assembled datum satisfies the Erlangen geometry synthesis theorem.
-/
theorem coadjoint_geometry_as_symmetry_invariants
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ)
    (onsagerPairing : Gdual → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ ξ : Gdual, C.coadjointAction 1 ξ = ξ)
    (hStateActMul :
      ∀ g h : Sym, ∀ ξ : Gdual,
        C.coadjointAction (g * h) ξ =
          C.coadjointAction g (C.coadjointAction h ξ))
    (hresp :
      ∀ X A B ξ,
        responseMetric (C.coadjointAction X ξ) A B =
          responseMetric ξ A B)
    (hons :
      ∀ A B ξ,
        onsagerPairing ξ A B =
          onsagerPairing ξ (casimirJ B) (casimirJ A)) :
    ErlangenOperatorGeometry
      (coadjointErlangenDatum C responseMetric onsagerPairing casimirJ
        hStateActOne hStateActMul hresp hons) :=
  geometry_as_symmetry_invariants
    (coadjointErlangenDatum C responseMetric onsagerPairing casimirJ
      hStateActOne hStateActMul hresp hons)

/--
Bridge closure theorem on the state carrier:
the moment-pullback bridge datum satisfies the Erlangen geometry synthesis
theorem.
-/
theorem state_geometry_as_symmetry_invariants
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : State → Sym → Sym → ℝ)
    (onsagerPairing : State → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ s : State, C.stateAction 1 s = s)
    (hStateActMul :
      ∀ g h : Sym, ∀ s : State,
        C.stateAction (g * h) s = C.stateAction g (C.stateAction h s))
    (hresp :
      ∀ X A B s,
        responseMetric (C.stateAction X s) A B =
          responseMetric s A B)
    (hons :
      ∀ A B s,
        onsagerPairing s A B =
          onsagerPairing s (casimirJ B) (casimirJ A)) :
    ErlangenOperatorGeometry
      (stateMomentErlangenDatum C responseMetric onsagerPairing casimirJ
        hStateActOne hStateActMul hresp hons) :=
  geometry_as_symmetry_invariants
    (stateMomentErlangenDatum C responseMetric onsagerPairing casimirJ
      hStateActOne hStateActMul hresp hons)

/--
Canonical pulled-back state datum from coadjoint response and Onsager channels.
-/
def stateMomentErlangenDatum_of_pullback
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ)
    (onsagerPairing : Gdual → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ s : State, C.stateAction 1 s = s)
    (hStateActMul :
      ∀ g h : Sym, ∀ s : State,
        C.stateAction (g * h) s = C.stateAction g (C.stateAction h s))
    (hresp :
      ∀ X A B ξ,
        responseMetric (C.coadjointAction X ξ) A B =
          responseMetric ξ A B)
    (hons :
      ∀ A B ξ,
        onsagerPairing ξ A B =
          onsagerPairing ξ (casimirJ B) (casimirJ A)) :
    ErlangenOperatorDatum ℝ Sym State Sym :=
  stateMomentErlangenDatum
    C
    (responseMetricPullback C responseMetric)
    (onsagerPairingPullback C onsagerPairing)
    casimirJ
    hStateActOne
    hStateActMul
    (responseMetricPullback_invariant C responseMetric hresp)
    (onsagerPairingPullback_reciprocity C onsagerPairing casimirJ hons)

/--
Closure theorem for the canonical pullback state datum.
-/
theorem state_pullback_geometry_as_symmetry_invariants
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ)
    (onsagerPairing : Gdual → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ s : State, C.stateAction 1 s = s)
    (hStateActMul :
      ∀ g h : Sym, ∀ s : State,
        C.stateAction (g * h) s = C.stateAction g (C.stateAction h s))
    (hresp :
      ∀ X A B ξ,
        responseMetric (C.coadjointAction X ξ) A B =
          responseMetric ξ A B)
    (hons :
      ∀ A B ξ,
        onsagerPairing ξ A B =
          onsagerPairing ξ (casimirJ B) (casimirJ A)) :
    ErlangenOperatorGeometry
      (stateMomentErlangenDatum_of_pullback C responseMetric onsagerPairing casimirJ
        hStateActOne hStateActMul hresp hons) :=
  geometry_as_symmetry_invariants
    (stateMomentErlangenDatum_of_pullback C responseMetric onsagerPairing casimirJ
      hStateActOne hStateActMul hresp hons)

/-! ## Onsager, Fréchet, & Krein–Riesz Reciprocity Bridges (F2.4 / M3.5) -/

section OnsagerFrechetKreinRieszBridge

open scoped InnerProductSpace
open _root_.InfoGeometry.Thermo.OnsagerClosure
open _root_.InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem
open _root_.InfoGeometry.Thermo.OnsagerFormsBridge
open _root_.InfoGeometry.Canonical.BKMScalarGaugeQuotient
open _root_.InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration
open _root_.InfoGeometry.Canonical.CEBKMOnsagerSystem
open _root_.InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily
open _root_.InfoGeometry.Canonical.CEOneFormNOperatorBridge
open _root_.InfoGeometry.Canonical.OperatorFrechetDerivationJet
open _root_.InfoGeometry.Canonical.OperatorFrechetForms
open _root_.InfoGeometry.Optics.OperatorDerivationForms
open _root_.InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open _root_.InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open _root_.InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open _root_.InfoGeometry.OperatorAlgebra
open _root_.InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open _root_.InfoGeometry.Krein
open _root_.InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
open _root_.InfoGeometry.Krein.DoubledSpaceRealKANBridge
open _root_.InfoGeometry.Krein.DoubleRealKreinShearDefect

/-- Every `ParityOnsagerSystem Obs` satisfies Erlangen `HasJReciprocity` with involution
`PS.T.op` (for any state type `State`). -/
theorem parityOnsager_hasJReciprocity
    {State Obs : Type*} [AddCommGroup Obs] [Module ℝ Obs]
    (PS : ParityOnsagerSystem Obs) :
    HasJReciprocity (fun (_ : State) A B => PS.totalGenerator A B) PS.T.op := by
  intro A B _s
  have h := PS.onsager_casimir_master_reciprocity (PS.T.op A) (PS.T.op B)
  rw [PS.T.involutive A, PS.T.involutive B] at h
  exact h

/-- Every `ParityOnsagerFormPairing V A n` (`V [⋀^Fin n]→ₗ[ℝ] A`, covering
`ActionOperatorForm`, `DerivationOperatorForm`, and `OpForm`) satisfies `HasJReciprocity`. -/
theorem parityOnsagerFormPairing_hasJReciprocity
    {State V A : Type*} {n : ℕ}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup A] [Module ℝ A]
    (PP : ParityOnsagerFormPairing V A n) :
    HasJReciprocity (fun (_ : State) ω η => PP.totalGenerator ω η) PP.T.op :=
  parityOnsager_hasJReciprocity PP.toParityOnsagerSystem

/-- Postcomposition of `Op1Form ℝ V A` by a `TimeReversal A` satisfies `HasJReciprocity`
for `totalGenerator1Form` at any test vector `u : V`. -/
theorem op1Form_hasJReciprocity
    {State V A : Type*} [AddCommGroup V] [Module ℝ V] [Ring A] [Algebra ℝ A]
    (PS : ParityOnsagerSystem A) (u : V) :
    HasJReciprocity
      (fun (_ : State) (α β : Op1Form ℝ V A) =>
        totalGenerator1Form PS.toOnsagerCasimirSystem α β u u)
      (fun α =>
        { toFun := fun v => PS.T.op (α v)
          map_add' := fun v₁ v₂ => by simp
          map_smul' := fun r v => by simp }) := by
  intro α β _s
  dsimp [totalGenerator1Form]
  have h := PS.onsager_casimir_master_reciprocity (PS.T.op (α u)) (PS.T.op (β u))
  rw [PS.T.involutive (α u), PS.T.involutive (β u)] at h
  exact h

/-- Convert `OperatorFrechetForms.ExchangeInvolution V` into a `TimeReversal V`. -/
def exchangeInvolutionToTimeReversal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : ExchangeInvolution V) : TimeReversal V where
  op := E.exchange.toLinearMap
  involutive := E.exchange_sq

/-- Construct an `ErlangenOperatorDatum ℝ G State Obs` from a group symmetry preserving
`entropy` and `responseMetric`, paired with a `ParityOnsagerSystem Obs` family sharing a
common time-reversal involution `casimirJ`. -/
def onsagerParityErlangenDatum
    {G State Obs : Type*} [Group G] [AddCommGroup Obs] [Module ℝ Obs]
    (entropy : State → ℝ)
    (responseMetric : State → Obs → Obs → ℝ)
    (stateAct : G → State → State)
    (obsAct : G → Obs → Obs)
    (PS : State → ParityOnsagerSystem Obs)
    (casimirJ : Obs → Obs)
    (hT : ∀ s, (PS s).T.op = casimirJ)
    (hStateOne : ∀ s, stateAct 1 s = s)
    (hStateMul : ∀ g h s, stateAct (g * h) s = stateAct g (stateAct h s))
    (hObsOne : ∀ A, obsAct 1 A = A)
    (hObsMul : ∀ g h A, obsAct (g * h) A = obsAct g (obsAct h A))
    (hEntropy : IsGeneralizedCasimir entropy stateAct)
    (hResp : IsGeometryInvariant responseMetric stateAct obsAct) :
    ErlangenOperatorDatum ℝ G State Obs where
  entropy := entropy
  responseMetric := responseMetric
  onsagerPairing := fun s A B => (PS s).totalGenerator A B
  stateAct := stateAct
  obsAct := obsAct
  casimirJ := casimirJ
  stateAct_one := hStateOne
  stateAct_mul := hStateMul
  obsAct_one := hObsOne
  obsAct_mul := hObsMul
  entropy_invariant := hEntropy
  response_invariant := hResp
  onsager_reciprocity := fun A B s => by
    rw [← hT s]
    exact parityOnsager_hasJReciprocity (PS s) A B s

theorem onsagerParityErlangenDatum_geometry
    {G State Obs : Type*} [Group G] [AddCommGroup Obs] [Module ℝ Obs]
    (entropy : State → ℝ)
    (responseMetric : State → Obs → Obs → ℝ)
    (stateAct : G → State → State)
    (obsAct : G → Obs → Obs)
    (PS : State → ParityOnsagerSystem Obs)
    (casimirJ : Obs → Obs)
    (hT : ∀ s, (PS s).T.op = casimirJ)
    (hStateOne : ∀ s, stateAct 1 s = s)
    (hStateMul : ∀ g h s, stateAct (g * h) s = stateAct g (stateAct h s))
    (hObsOne : ∀ A, obsAct 1 A = A)
    (hObsMul : ∀ g h A, obsAct (g * h) A = obsAct g (obsAct h A))
    (hEntropy : IsGeneralizedCasimir entropy stateAct)
    (hResp : IsGeometryInvariant responseMetric stateAct obsAct) :
    ErlangenOperatorGeometry
      (onsagerParityErlangenDatum entropy responseMetric stateAct obsAct PS casimirJ
        hT hStateOne hStateMul hObsOne hObsMul hEntropy hResp) :=
  geometry_as_symmetry_invariants _

/-- Bridge `CEBKMOnsagerGibbsNOperatorFamily` (`finiteGibbsCEFamilyNOperatorSystem`,
`secondFDerivLogPartitionReadout`) and `ExchangeInvolution` into `ErlangenOperatorDatum`,
proving both `HasJReciprocity` and Fréchet Hessian alignment. -/
noncomputable def gibbsNOperatorFamilyErlangenDatum
    {G : Type*} [Group G]
    {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ)
    (Q : GibbsOperator n)
    (E : ExchangeInvolution (FamilyCarrier m n))
    (hD_even : ∀ x y,
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative
          (E.exchange x) (E.exchange y) =
        (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative x y)
    (hR_odd : ∀ x y,
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).reversible
          (E.exchange x) (E.exchange y) =
        -(finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).reversible x y) :
    ErlangenOperatorDatum ℝ G Unit (FamilyCarrier m n) :=
  let PS : ParityOnsagerSystem (FamilyCarrier m n) :=
    { toOnsagerCasimirSystem := finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q
      T := exchangeInvolutionToTimeReversal E
      dissipative_T_even := hD_even
      reversible_T_odd := hR_odd }
  onsagerParityErlangenDatum
    (G := G)
    (State := Unit)
    (Obs := FamilyCarrier m n)
    (fun _ => gibbsPartitionReal H)
    (fun _ x y => PS.dissipative x y)
    (fun _ s => s)
    (fun _ x => x)
    (fun _ => PS)
    E.exchange
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)

theorem gibbsNOperatorFamilyErlangenDatum_reciprocity_and_hessian
    {G : Type*} [Group G]
    {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ)
    (Q : GibbsOperator n)
    (E : ExchangeInvolution (FamilyCarrier m n))
    (hD_even : ∀ x y,
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative
          (E.exchange x) (E.exchange y) =
        (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative x y)
    (hR_odd : ∀ x y,
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).reversible
          (E.exchange x) (E.exchange y) =
        -(finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).reversible x y)
    (D₁ D₂ : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hD₁ : IsSelfAdjoint
      (finiteGibbsCEFamilyNOperatorReadoutLinear a c
        (finiteCEFrechetFamilyDirection D₁))) :
    let datum := gibbsNOperatorFamilyErlangenDatum (G := G) H hH hZ a c Q E hD_even hR_odd
    HasJReciprocity datum.onsagerPairing E.exchange ∧
      datum.responseMetric ()
          (finiteCEFrechetFamilyDirection D₁)
          (finiteCEFrechetFamilyDirection D₂) =
        (secondFDerivLogPartitionReadout H
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c
            (finiteCEFrechetFamilyDirection D₁))
          (finiteGibbsCEFamilyNOperatorReadoutLinear a c
            (finiteCEFrechetFamilyDirection D₂))).re := by
  refine ⟨?_, ?_⟩
  · exact (gibbsNOperatorFamilyErlangenDatum (G := G) H hH hZ a c Q E hD_even hR_odd).onsager_reciprocity
  · have hpair :=
      finiteGibbsCEFamilyNOperatorSystem_pairwise_eq_dissipation_hessian
        H hH hZ a c Q D₁ D₂ hD₁
    exact hpair.1.symm.trans hpair.2

/-- Krein–Fréchet–Riesz pairing induced by `KreinFrechetRiesz.kreinToDual`:
`kreinDualPairing s x y = kreinToDual x y = kreinInner x y`. -/
noncomputable def kreinDualPairing
    {State H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H] :
    State → H → H → ℝ :=
  fun _ x y => kreinToDual x y

@[simp] theorem kreinDualPairing_eq_kreinInner
    {State H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H] (s : State) (x y : H) :
    kreinDualPairing s x y = KreinSpace.kreinInner x y :=
  rfl

/-- `HasJReciprocity` holds on `kreinDualPairing` for every `IsKreinIsometry U`
(and in particular for `KreinSpace.jCLM`). -/
theorem kreinDualPairing_hasJReciprocity_of_isKreinIsometry
    {State H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H]
    (U : H →L[ℝ] H) (hU : KreinSpace.IsKreinIsometry U) :
    HasJReciprocity (kreinDualPairing (State := State) (H := H)) U := by
  intro x y _s
  simp only [kreinDualPairing_eq_kreinInner]
  rw [hU y x]
  exact KreinSpace.kreinInner_symm x y

theorem kreinDualPairing_hasJReciprocity_jCLM
    {State H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H] :
    HasJReciprocity (kreinDualPairing (State := State) (H := H)) (KreinSpace.jCLM (H := H)) :=
  kreinDualPairing_hasJReciprocity_of_isKreinIsometry _ KreinSpace.IsKreinIsometry.J

/-- Concrete `ParityOnsagerSystem (DoubledSpace E)` with dissipative form `⟪u, v⟫_ℝ`,
reversible skew form `⟪complex_i u, v⟫_ℝ`, and time reversal `KreinSpace.jCLM`
(`= spectral_epsilon`). -/
noncomputable def doubledSpaceKreinOnsagerSystem
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    ParityOnsagerSystem (DoubledSpace E) where
  dissipative :=
    LinearMap.mk₂ ℝ (fun u v => ⟪u, v⟫_ℝ)
      (fun u₁ u₂ v => inner_add_left u₁ u₂ v)
      (fun c u v => real_inner_smul_left u v c)
      (fun u v₁ v₂ => inner_add_right u v₁ v₂)
      (fun c u v => real_inner_smul_right u v c)
  reversible :=
    LinearMap.mk₂ ℝ (fun u v => ⟪complex_i (E := E) u, v⟫_ℝ)
      (fun u₁ u₂ v => by simp [map_add, inner_add_left])
      (fun c u v => by simp [map_smul, real_inner_smul_left]; ring)
      (fun u v₁ v₂ => inner_add_right _ v₁ v₂)
      (fun c u v => real_inner_smul_right _ v c)
  dissipative_symm := fun u v => real_inner_comm v u
  reversible_skew := fun u v => by
    change ⟪complex_i (E := E) u, v⟫_ℝ = -⟪complex_i (E := E) v, u⟫_ℝ
    rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_complex_i (E := E),
      neg_apply, inner_neg_right, real_inner_comm]
  dissipative_nonneg := fun u => real_inner_self_nonneg (x := u)
  T :=
    { op := (KreinSpace.jCLM (H := DoubledSpace E)).toLinearMap
      involutive := fun u => by
        change (KreinSpace.jCLM (H := DoubledSpace E))
            ((KreinSpace.jCLM (H := DoubledSpace E)) u) = u
        rw [jCLM_eq_spectral_epsilon]
        apply DoubledSpace.ext <;> simp }
  dissipative_T_even := fun u v => by
    change ⟪KreinSpace.jCLM (H := DoubledSpace E) u,
        KreinSpace.jCLM (H := DoubledSpace E) v⟫_ℝ = ⟪u, v⟫_ℝ
    rw [jCLM_eq_spectral_epsilon]
    simp [spectral_epsilon, WithLp.prod_inner_apply]
  reversible_T_odd := fun u v => by
    change ⟪complex_i (E := E) (KreinSpace.jCLM (H := DoubledSpace E) u),
        KreinSpace.jCLM (H := DoubledSpace E) v⟫_ℝ =
      -⟪complex_i (E := E) u, v⟫_ℝ
    rw [jCLM_eq_spectral_epsilon]
    rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_spectral_epsilon]
    have hcomp : spectral_epsilon (E := E) ((complex_i (E := E)) (spectral_epsilon (E := E) u)) =
        -(complex_i (E := E) u) := by
      apply DoubledSpace.ext <;> simp [complex_i, modular_j_apply, spectral_epsilon]
    rw [hcomp, inner_neg_left]

/-- Concrete `ErlangenOperatorDatum` on `DoubledSpace E` whose `onsagerPairing` is the
Krein–Onsager generator of `doubledSpaceKreinOnsagerSystem E` and whose `casimirJ` is
`KreinSpace.jCLM (= spectral_epsilon)`. -/
noncomputable def doubledSpaceKreinErlangenDatum
    (G E : Type*) [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    ErlangenOperatorDatum ℝ G Unit (DoubledSpace E) :=
  onsagerParityErlangenDatum
    (G := G)
    (State := Unit)
    (Obs := DoubledSpace E)
    (fun _ => 0)
    (fun _ u v => (doubledSpaceKreinOnsagerSystem E).dissipative u v)
    (fun _ s => s)
    (fun _ u => u)
    (fun _ => doubledSpaceKreinOnsagerSystem E)
    (KreinSpace.jCLM (H := DoubledSpace E))
    (fun _ => funext fun _ => rfl)
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)

/-- Contrast 1 (`T3-02`): on any nontrivial `E`, `modular_j` FAILS `HasJReciprocity` on
`kreinDualPairing` (flipping the Krein sign via `kreinInner_modular_j`), whereas
`KreinSpace.jCLM (= spectral_epsilon)` satisfies it. -/
theorem kreinDualPairing_not_hasJReciprocity_modular_j
    {State E : Type*} [Nonempty State]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Nontrivial E] :
    ¬ HasJReciprocity (kreinDualPairing (State := State) (H := DoubledSpace E))
        (modular_j (E := E)) := by
  intro hRec
  obtain ⟨e₀, he₀⟩ := exists_ne (0 : E)
  obtain ⟨s₀⟩ := ‹Nonempty State›
  have h := hRec (to_doubled e₀ (0 : E)) (to_doubled e₀ (0 : E)) s₀
  simp only [kreinDualPairing_eq_kreinInner, kreinInner_modular_j] at h
  have hpos : 0 < KreinSpace.kreinInner (H := DoubledSpace E)
      (to_doubled e₀ (0 : E)) (to_doubled e₀ (0 : E)) := by
    rw [kreinInner_to_doubled]
    simp only [inner_zero_right, sub_zero]
    exact real_inner_self_pos.mpr he₀
  linarith

/-- Contrast 2 (`T2-F2.4-3`, `T3-02`): for any nonzero parabolic shear parameter `t ≠ 0` and
nonzero `ξ : E`, `ρclock (componentNReal t)` FAILS `HasJReciprocity` on `kreinDualPairing`
(matching `componentNReal_not_krein_isometry` and `kreinInner_componentNReal_secondSheet_defect`). -/
theorem kreinDualPairing_not_hasJReciprocity_componentNReal
    {State E : Type*} [Nonempty State]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (t : ℝ) (ht : t ≠ 0) (ξ : E) (hξ : ξ ≠ 0) :
    ¬ HasJReciprocity (kreinDualPairing (State := State) (H := DoubledSpace E))
        (ρclock (E := E) (componentNReal t)) := by
  intro hRec
  obtain ⟨s₀⟩ := ‹Nonempty State›
  have h := hRec (to_doubled (0 : E) ξ) (to_doubled (0 : E) ξ) s₀
  simp only [kreinDualPairing_eq_kreinInner] at h
  have hdefect := kreinInner_componentNReal_secondSheet_defect (E := E) t ξ
  rw [← h] at hdefect
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have hξ2 : 0 < inner ℝ ξ ξ := real_inner_self_pos.mpr hξ
  have hprod : 0 < t ^ 2 * inner ℝ ξ ξ := mul_pos ht2 hξ2
  linarith

end OnsagerFrechetKreinRieszBridge

end Canonical
end InfoGeometry
