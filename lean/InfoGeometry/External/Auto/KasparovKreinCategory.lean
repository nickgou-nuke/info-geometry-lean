import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import InfoGeometry.External.Auto.AnomalousKMSFlow
import InfoGeometry.External.Auto.ConnesSpectralAction
import InfoGeometry.External.Auto.CuntzKTheoryPairing

noncomputable section

namespace InfoGeometry.Canonical.KasparovKreinCategory

open Complex
open CategoryTheory

universe u v

/--
Object-indexed zero anchors for a KK-contractible boundary object in an
arbitrary category.

The indexing matters: a morphism `X ⟶ O₂` can only be compared to the zero
anchor with the same source `X`.
-/
structure CategoricalContractibleBoundary
    {KKCat : Type u} [Category.{v} KKCat] (O₂ : KKCat) where
  zeroIn : ∀ X : KKCat, X ⟶ O₂
  zeroOut : ∀ X : KKCat, O₂ ⟶ X
  incoming_eq : ∀ {X : KKCat} (f : X ⟶ O₂), f = zeroIn X
  outgoing_eq : ∀ {X : KKCat} (g : O₂ ⟶ X), g = zeroOut X

/--
Categorical Kasparov-product firewall:
if `O₂` is contractible in the categorical sense, every composable channel
`A ⟶ O₂ ⟶ C` is the anchored zero channel.
-/
theorem cuntz_kk_contractibility
    {KKCat : Type u} [Category.{v} KKCat]
    {O₂ A C : KKCat}
    (hO₂ : CategoricalContractibleBoundary O₂)
    (f : A ⟶ O₂) (g : O₂ ⟶ C) :
    f ≫ g = hO₂.zeroIn A ≫ hO₂.zeroOut C := by
  rw [hO₂.incoming_eq f, hO₂.outgoing_eq g]

/--
Abstract bivariant Kasparov–Krein interface.

`KK A B` is a formal carrier of bivariant classes from `A` to `B`.
-/
class KasparovKreinData where
  KK : Type → Type → Type
  comp : ∀ {A B C : Type}, KK A B → KK B C → KK A C

/-- KK-contractible boundary object: all classes to/from it are empty. -/
def KKContractibleBoundary (K₀ : Type) [KK : KasparovKreinData] : Prop :=
  (∀ A : Type, IsEmpty (KasparovKreinData.KK A K₀)) ∧
    (∀ B : Type, IsEmpty (KasparovKreinData.KK K₀ B))

namespace KKContractibleBoundary

/-- Compatibility projection for incoming KK classes. -/
theorem incoming
    {K₀ : Type} [KK : KasparovKreinData]
    (h : KKContractibleBoundary K₀) (A : Type) :
    IsEmpty (KasparovKreinData.KK A K₀) :=
  h.1 A

/-- Compatibility projection for outgoing KK classes. -/
theorem outgoing
    {K₀ : Type} [KK : KasparovKreinData]
    (h : KKContractibleBoundary K₀) (B : Type) :
    IsEmpty (KasparovKreinData.KK K₀ B) :=
  h.2 B

end KKContractibleBoundary

/--
O₂ boundary K₀ carrier aligned with the existing external compatibility symbol.

The carrier is an alias for the proof-trivial K₀ model from
`CuntzKTheoryPairing`; no categorical Cuntz algebra is constructed in this file.
-/
abbrev O2Boundary : Type := CuntzKTheoryPairing.O2_K0

/-- Symbolic KK-transfer through O₂. -/
def kkBoundaryPairing
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    {K1 : Type*} [AddCommGroup K1]
    {A B : Type}
    [KK : KasparovKreinData]
    (_xA : KasparovKreinData.KK A O2Boundary) (_xB : KasparovKreinData.KK O2Boundary B)
    (_k : CuntzKTheoryPairing.O2_K0) (_ξ : K1) : ℂ :=
  0

/-- Any KK-factorized O₂ boundary pairing is zero in this abstract model. -/
theorem kkBoundaryPairing_zero
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    {K1 : Type*} [AddCommGroup K1]
    {A B : Type}
    [KK : KasparovKreinData]
    (xA : KasparovKreinData.KK A O2Boundary) (xB : KasparovKreinData.KK O2Boundary B)
    (k : CuntzKTheoryPairing.O2_K0) (ξ : K1) :
    kkBoundaryPairing H xA xB k ξ = 0 := by
  simp [kkBoundaryPairing]

/-- O₂ contractibility blocks all KK transport through it. -/
theorem kasparovKrein_killed_by_o2
    (K₀ : Type) [KK : KasparovKreinData]
    (hK : KKContractibleBoundary K₀) :
    ∀ A : Type, IsEmpty (KasparovKreinData.KK A K₀) ∧ IsEmpty (KasparovKreinData.KK K₀ A) := by
  intro A
  exact ⟨hK.1 A, hK.2 A⟩

/--
A typed Kasparov-factorization chain through the O₂ boundary:
`A -(xA)-> O₂ -(xB)-> C`.
-/
structure KKProductChain
    {A C : Type} [KK : KasparovKreinData] where
  left : KasparovKreinData.KK A O2Boundary
  right : KasparovKreinData.KK O2Boundary C
  composite : KasparovKreinData.KK A C
  isComposed : composite = KK.comp left right

/--
If an anomaly index is identified with the KK-factorized O₂ boundary channel,
Connes–Chern contractibility gives the full collapse and spectral minimization
via the existing bridge theorems.
-/
theorem kasparov_krein_product_chain_collapses_via_connes_bridge
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : AnomalousKMSFlow.ModularAnomalyContext H)
    (hFaith : AnomalousKMSFlow.TraceFaithful H C.tr)
    (S0 c : ℝ) (hc : 0 < c)
    {K1 : Type*} [AddCommGroup K1]
    {A Ctxt : Type}
    [KasparovKreinData]
    (k : CuntzKTheoryPairing.O2_K0) (ξ : K1)
    (chain : KKProductChain (A := A) (C := Ctxt))
    (hPair :
      AnomalousKMSFlow.anomalousIndex H C =
        kkBoundaryPairing H chain.left chain.right k ξ) :
    C.δK = 0 ∧
      (ConnesSpectralAction.connesSpectralAction (H := H) C C.δK S0 c = S0) ∧
      (∀ δ : Module.End ℂ H,
        ConnesSpectralAction.connesSpectralAction (H := H) C δ S0 c =
          ConnesSpectralAction.connesSpectralAction (H := H) C C.δK S0 c ↔ δ = C.δK) ∧
      (∀ s, AnomalousKMSFlow.anomalousLineLeak (AnomalousKMSFlow.anomalousIndexLeakProfile H C) s = 0) := by
  have hPair' :
      AnomalousKMSFlow.anomalousIndex H C =
        (inferInstance : CuntzKTheoryPairing.ConnesChernPairing
          CuntzKTheoryPairing.O2_K0 K1).pair k ξ := by
    simpa [kkBoundaryPairing] using hPair
  exact CuntzKTheoryPairing.connes_chern_holographic_minimization_summary
    (H := H) C hFaith S0 c hc k ξ hPair'

/--
Typed Kasparov-chain firewall principle: a contractible O₂ boundary has no
incoming/outgoing non-empty KK data, so any such chain is impossible.
-/
theorem kasparov_krein_product_chain_contractibility_forbids
    {A Ctxt : Type}
    [KK : KasparovKreinData]
    (hK : KKContractibleBoundary O2Boundary)
    (chain : KKProductChain (A := A) (C := Ctxt)) :
    False := by
  have hIn : IsEmpty (KasparovKreinData.KK A O2Boundary) := hK.1 A
  exact hIn.elim chain.left

/--
If a conjectural anomaly hypothesis is forced through a contractible KK
boundary, the correct constructive conclusion is non-existence of that
incoming/outgoing chain.  We do not manufacture anomaly-collapse theorems from
inconsistent chain data.
-/
theorem kasparov_krein_contractibility_forbids_anomaly_chain
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : AnomalousKMSFlow.ModularAnomalyContext H)
    {K1 : Type*} [AddCommGroup K1]
    [KK : KasparovKreinData]
    {A B : Type}
    (k : CuntzKTheoryPairing.O2_K0) (ξ : K1)
    (hKK : KKContractibleBoundary O2Boundary)
    (xA : KasparovKreinData.KK A O2Boundary) (_xB : KasparovKreinData.KK O2Boundary B)
    (_hPair :
      AnomalousKMSFlow.anomalousIndex H C =
        kkBoundaryPairing H xA _xB k ξ) :
    False := by
  have hIm : IsEmpty (KasparovKreinData.KK A O2Boundary) := hKK.1 A
  exact hIm.elim xA

/-- Static consequence on the existing Connes–Chern interface. -/
theorem kasparov_krein_contractibility_reduces_o2_pairing
    {K1 : Type*} [AddCommGroup K1]
    (k : CuntzKTheoryPairing.O2_K0) (ξ : K1) :
    (inferInstance : CuntzKTheoryPairing.ConnesChernPairing
      CuntzKTheoryPairing.O2_K0 K1).pair k ξ = 0 :=
  CuntzKTheoryPairing.connesChernPairing_zero_on_O2 (K1 := K1) k ξ

/-- Compact exported slogan. -/
theorem kasparov_krein_contractibility_slogan
    (K₀ : Type) [KK : KasparovKreinData] (hK : KKContractibleBoundary K₀) :
    ∀ A : Type, IsEmpty (KasparovKreinData.KK A K₀) := by
  intro A
  exact hK.1 A

end InfoGeometry.Canonical.KasparovKreinCategory
