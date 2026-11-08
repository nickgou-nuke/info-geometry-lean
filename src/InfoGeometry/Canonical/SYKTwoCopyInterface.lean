/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.KitaevChain
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RNDeterminantConnesChainBridge
import InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SYKTwoCopyInterface

## i. Overview
Strict interface separating:
- current owner theorem surfaces compiled in this repository (including the
  algebraic two-copy shockwave sheet-transfer theorem in
  `InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset`),
- formalizable next-owner targets for coupled two-copy SYK protocols,
- external spacetime/traversability interpretation claims.

## ii. Key results
- `traversableWindowOpen_iff_not_closed` & `traversableWindow_side_split`
- `topologicalIndexZ2_append_owner_claim_holds`
- `connesCocycle_state_chain_owner_claim_holds`
- `two_copy_syk_shockwave_transfer_owner_claim_holds`

## iii. Table of contents
- Claim-status tier classification (`ClaimTier`, `TaggedClaim`)
- Finite two-copy coupled-system window dichotomy
- Compiled repo-theorem owner anchors (`KitaevChain`, `ConnesCocycle`, `KitaevSYKHolographyScramblonPoset`)

## iv. References
- Alexei Kitaev, *"A simple model of quantum holography (part 1)"* (2015)
- Ping Gao, Daniel Louis Jafferis, and Aron C. Wall, *Traversable Wormholes via a Double Trace Deformation* (2017)

### Three-Bucket Audit Map (`audit-proof` Policy)

#### BUCKET 1 — Proved Kernel Content
- `TaggedClaim.formalizableNextOwnerTarget_not_repoTheorem`,
  `TaggedClaim.externalInterpretation_not_repoTheorem`,
  `traversableWindowOpen_iff_not_closed`, `traversableWindowOpen_not_closed`,
  `traversableWindow_side_split`, `traversableProtocolTargetClaim_not_repo`,
  `erEprInterpretationClaim_not_repo`, `traversableProtocolRepoClaim_is_repo`,
  `traversableProtocolRepoClaim_holds`, `topologicalIndexZ2_append_owner_claim_is_repo`,
  `topologicalIndexZ2_append_owner_claim_holds`,
  `connesCocycle_state_chain_owner_claim_is_repo`,
  `connesCocycle_state_chain_owner_claim_holds`,
  `two_copy_syk_shockwave_transfer_owner_claim_is_repo`,
  `two_copy_syk_shockwave_transfer_owner_claim_holds`.

#### BUCKET 2 — Conditional / Interface Boundaries
- Coupling sign window `μ < 0` vs. `0 ≤ μ` over `ℝ` and algebraic idempotent `P * P = P` over `[Ring B]`.

#### BUCKET 3 — Open / Unformalized
- External bulk semi-classical spacetime ER=EPR geometry beyond the finite algebraic and operator models.
-/

namespace InfoGeometry.Canonical.SYKTwoCopyInterface

open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Canonical.RNDeterminantConnesChainBridge
open InfoGeometry.Volume.ConnesCocycle

section ClaimTier

/-- Claim-status bands for scope-safe protocol language. -/
@[rep_depth transport]
inductive ClaimTier where
  | repoTheorem
  | formalizableNextOwnerTarget
  | externalInterpretation
  deriving DecidableEq, Repr

/--
A proposition indexed by claim-status band.

The proposition is a type parameter rather than an opaque structure field, so
claim classification cannot erase the theorem being classified.
-/
@[rep_depth transport]
def TaggedClaim (_statement : Prop) := ClaimTier

namespace TaggedClaim

/-- Underlying `ClaimTier` value of a `TaggedClaim`. -/
def tier {P : Prop} (C : TaggedClaim P) : ClaimTier := C

/-- Formalizable-next-owner claims are not repo-theorem claims. -/
@[rep_depth transport]
theorem formalizableNextOwnerTarget_not_repoTheorem
    {P : Prop}
    (C : TaggedClaim P)
    (hTarget : C.tier = ClaimTier.formalizableNextOwnerTarget) :
    C.tier ≠ ClaimTier.repoTheorem := by
  intro hRepo
  rw [hTarget] at hRepo
  cases hRepo

/-- External-interpretation claims are not repo-theorem claims. -/
@[rep_depth transport]
theorem externalInterpretation_not_repoTheorem
    {P : Prop}
    (C : TaggedClaim P)
    (hExt : C.tier = ClaimTier.externalInterpretation) :
    C.tier ≠ ClaimTier.repoTheorem := by
  intro hRepo
  rw [hExt] at hRepo
  cases hRepo

end TaggedClaim

end ClaimTier

section TwoCopyFinite

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "EndH" => H →L[ℝ] H

/-- Effective cross-coupling operator `μ • couplingLR`. -/
@[rep_depth operator]
def effectiveCrossCoupling (couplingLR : EndH) (μ : ℝ) : EndH :=
  μ • couplingLR

/-- Open window (`μ < 0`) iff the closed-window inequality (`0 ≤ μ`) is false. -/
@[rep_depth transport]
theorem traversableWindowOpen_iff_not_closed (μ : ℝ) :
    μ < 0 ↔ ¬ (0 ≤ μ) := by
  constructor
  · intro hOpen hClosed
    have hlt := not_le_of_gt hOpen
    exact hlt hClosed
  · intro hNotClosed
    by_cases hClosed : 0 ≤ μ
    · exact False.elim (hNotClosed hClosed)
    · exact lt_of_not_ge hClosed

/-- Open (`μ < 0`) and closed (`0 ≤ μ`) windows are mutually exclusive. -/
@[rep_depth transport]
theorem traversableWindowOpen_not_closed
    (μ : ℝ) (hOpen : μ < 0) (hClosed : 0 ≤ μ) :
    False := by
  have hiff := (traversableWindowOpen_iff_not_closed μ).mp hOpen
  exact hiff hClosed

/-- Every scalar coupling `μ : ℝ` lies in either the open (`μ < 0`) or closed (`0 ≤ μ`) window. -/
@[rep_depth transport]
theorem traversableWindow_side_split (μ : ℝ) :
    μ < 0 ∨ 0 ≤ μ := by
  by_cases h : 0 ≤ μ
  · exact Or.inr h
  · exact Or.inl (lt_of_not_ge h)

/-- Formalizable-next-target protocol claim constructor. -/
@[rep_depth transport]
def traversableProtocolTargetClaim (μ : ℝ) : TaggedClaim (μ < 0) :=
  ClaimTier.formalizableNextOwnerTarget

/-- The formalizable target claim is explicitly non-repo by tier tag. -/
@[rep_depth transport]
theorem traversableProtocolTargetClaim_not_repo (μ : ℝ) :
    (traversableProtocolTargetClaim μ).tier ≠ ClaimTier.repoTheorem := by
  dsimp [traversableProtocolTargetClaim, TaggedClaim.tier]
  intro h
  cases h

/-- External ER=EPR interpretation claim constructor (kept non-owner by type tag). -/
@[rep_depth transport]
def erEprInterpretationClaim (μ : ℝ) : TaggedClaim (μ < 0) :=
  ClaimTier.externalInterpretation

/-- The ER=EPR interpretation constructor is never tagged as repo theorem. -/
@[rep_depth transport]
theorem erEprInterpretationClaim_not_repo (μ : ℝ) :
    (erEprInterpretationClaim μ).tier ≠ ClaimTier.repoTheorem := by
  dsimp [erEprInterpretationClaim, TaggedClaim.tier]
  intro h
  cases h

/-- Repo-tier claim materialized from a normalized preparation `‖psi‖ = 1` and an open-window hypothesis `μ < 0`. -/
@[rep_depth transport]
def traversableProtocolRepoClaim
    (psi : H) (_hNorm : ‖psi‖ = 1) (μ : ℝ) (_hOpen : μ < 0) :
    TaggedClaim (‖psi‖ = 1 ∧ μ < 0) :=
  ClaimTier.repoTheorem

/-- Protocol repo claim is tagged in the repo theorem band. -/
@[rep_depth transport]
theorem traversableProtocolRepoClaim_is_repo
    (psi : H) (hNorm : ‖psi‖ = 1) (μ : ℝ) (hOpen : μ < 0) :
    (traversableProtocolRepoClaim psi hNorm μ hOpen).tier = ClaimTier.repoTheorem := by
  unfold traversableProtocolRepoClaim TaggedClaim.tier
  rfl

/-- Protocol repo claim carries the explicit proof of the normalized open-window statement. -/
@[rep_depth transport]
theorem traversableProtocolRepoClaim_holds
    (psi : H) (hNorm : ‖psi‖ = 1) (μ : ℝ) (hOpen : μ < 0) :
    ‖psi‖ = 1 ∧ μ < 0 := by
  constructor
  · exact hNorm
  · exact hOpen

end TwoCopyFinite

section OwnerAnchorTheorems

/-- Tagged repo-tier claim for the finite `ℤ₂` append owner theorem. -/
@[rep_depth transport]
def topologicalIndexZ2_append_owner_claim :
    TaggedClaim
      (∀ (chain₁ chain₂ : List InfoGeometry.Quantum.KitaevChain.KitaevCell),
        macroscopicVolume chain₁ ≠ 0 →
        macroscopicVolume chain₂ ≠ 0 →
        topologicalIndexZ2 (chain₁ ++ chain₂)
          = topologicalIndexZ2 chain₁ + topologicalIndexZ2 chain₂) :=
  ClaimTier.repoTheorem

/-- The finite `ℤ₂` append owner claim is tagged as repo theorem. -/
@[rep_depth transport]
theorem topologicalIndexZ2_append_owner_claim_is_repo :
    topologicalIndexZ2_append_owner_claim.tier = ClaimTier.repoTheorem := by
  unfold topologicalIndexZ2_append_owner_claim TaggedClaim.tier
  rfl

/-- The finite `ℤ₂` append owner claim is constructively inhabited. -/
@[rep_depth transport]
theorem topologicalIndexZ2_append_owner_claim_holds
    (chain₁ chain₂ : List KitaevCell)
    (h₁ : macroscopicVolume chain₁ ≠ 0)
    (h₂ : macroscopicVolume chain₂ ≠ 0) :
    topologicalIndexZ2 (chain₁ ++ chain₂)
      = topologicalIndexZ2 chain₁ + topologicalIndexZ2 chain₂ := by
  have h := topologicalIndexZ2_append_of_macroscopicVolume_ne_zero chain₁ chain₂ h₁ h₂
  exact h

section Connes

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Tagged repo-tier claim for the Connes cocycle owner chain law. -/
@[rep_depth transport]
def connesCocycle_state_chain_owner_claim :
    TaggedClaim
      (∀ (σ : AdditiveModularFlow (H := E))
        (u : ℝ → AlgebraEnd E),
        IsConnesCocycle σ u →
        ∀ (s t : ℝ),
        u (s + t) = u s * σ s (u t)) :=
  ClaimTier.repoTheorem

/-- The Connes cocycle owner claim is tagged as repo theorem. -/
@[rep_depth transport]
theorem connesCocycle_state_chain_owner_claim_is_repo :
    (connesCocycle_state_chain_owner_claim (E := E)).tier = ClaimTier.repoTheorem := by
  unfold connesCocycle_state_chain_owner_claim TaggedClaim.tier
  rfl

/-- The Connes cocycle owner claim is constructively inhabited. -/
@[rep_depth transport]
theorem connesCocycle_state_chain_owner_claim_holds
    (σ : AdditiveModularFlow (H := E))
    (u : ℝ → AlgebraEnd E)
    (hCocycle : IsConnesCocycle σ u)
    (s t : ℝ) :
    u (s + t) = u s * σ s (u t) := by
  have h := connesCocycle_state_chain (σ := σ) (u := u) hCocycle s t
  exact h

end Connes

section AlgebraicTwoCopyShockwaveTransfer

variable {B : Type*} [Ring B]

/-- Tagged repo-tier claim for the algebraic two-copy SYK shockwave sheet-transfer
and unitary round-trip reconstruction theorem. -/
@[rep_depth transport]
def two_copy_syk_shockwave_transfer_owner_claim :
    TaggedClaim
      (∀ (P X Y Z : B), P * P = P →
        let x := P * Z * P
        let np := InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P X
        let nm := InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P Y
        let qp := np * nm
        (1 - P) *
          InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation P X Y x *
          (1 - P) = nm * x * np ∧
        np *
          ((1 - P) *
            InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation P X Y x *
            (1 - P)) *
          nm = qp * x * qp ∧
        (qp = P →
          np *
            ((1 - P) *
              InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation P X Y x *
              (1 - P)) *
            nm = x)) :=
  ClaimTier.repoTheorem

/-- The algebraic two-copy shockwave transfer claim is tagged as a repo theorem. -/
@[rep_depth transport]
theorem two_copy_syk_shockwave_transfer_owner_claim_is_repo :
    (two_copy_syk_shockwave_transfer_owner_claim (B := B)).tier = ClaimTier.repoTheorem := by
  unfold TaggedClaim.tier two_copy_syk_shockwave_transfer_owner_claim
  rfl

/-- The algebraic two-copy shockwave transfer claim is constructively inhabited by
`two_corner_shockwave_sheet_transfer_round_trip`. -/
@[rep_depth transport]
theorem two_copy_syk_shockwave_transfer_owner_claim_holds
    (P X Y Z : B) (hP : P * P = P) :
    let x := P * Z * P
    let np := InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P X
    let nm := InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P Y
    let qp := np * nm
    (1 - P) *
      InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation P X Y x *
      (1 - P) = nm * x * np ∧
    np *
      ((1 - P) *
        InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation P X Y x *
        (1 - P)) *
      nm = qp * x * qp ∧
    (qp = P →
      np *
        ((1 - P) *
          InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation P X Y x *
          (1 - P)) *
        nm = x) := by
  have h :=
    InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.two_corner_shockwave_sheet_transfer_round_trip
      P X Y Z hP
  exact h

end AlgebraicTwoCopyShockwaveTransfer

end OwnerAnchorTheorems

end InfoGeometry.Canonical.SYKTwoCopyInterface
