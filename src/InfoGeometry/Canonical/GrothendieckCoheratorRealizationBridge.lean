/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import OAI.CategoryTheory.Globular.Main
import HomotopyHypothesis.Blueprint.Main
import HomotopyHypothesis.Bridge.Statement.Main

/-!
# Grothendieck Coherator Transport and Single-Coherator Topological Realization Bridge (Rank 2)

## i. Overview
Closes Rank 2 of `docs/CROSS_LANE_CLOSURE_SEQUENCE.md` by connecting the coherator `C` used in
`OAI.Grothendieck.elementary_expansion` to topological realization in two complementary ways:
1. **Direct single-coherator realization (`elementary_expansion_with_same_coherator_oai_realization`):**
   Using `HomotopyHypothesis.Blueprint.oaiStatement C hC`, the exact same coherator
   `C : OAI.Grothendieck.GlobularTheory.{v}` and `hC : C.IsCoherator` of the elementary pushout
   `i : X ⟶ Y` admits an `OAIRealization C` whose fundamental `∞`-groupoid functor `R.Pi` maps
   weak homotopy equivalences in `TopCat.{v}` into `HomotopyHypothesis.Blueprint.W hC`
   (`= OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hC`) and exhibits
   `R.Pi ⋙ (W hC).Q` as the localization of `TopCat.{v}` at `weakHomotopyEquivalences`.
2. **Explicit `theoryToOAI` coherator transport (`coherator_transport_theoryToOAI_and_realization_bridge`):**
   For any `C_top : HomotopyHypothesis.Grothendieck.GlobularTheory.{u}` with `hC_top : C_top.IsCoherator`,
   the explicit transport map `HomotopyHypothesis.Bridge.Statement.theoryToOAI C_top` produces an
   OAI coherator `C = theoryToOAI C_top` (`isCoherator_theoryToOAI hC_top`), transports realizations
   via `realizationToOAI` and `realizationOfOAI`, preserves and reflects model weak equivalences
   across `modelToOAI C_top` (`weakEquivalence_modelToOAI_iff`), and transports the localization
   functor (`localization_modelToOAI`).

## ii. Key results
- `elementary_expansion_with_same_coherator_oai_realization`
- `coherator_transport_theoryToOAI_and_realization_bridge`

## iii. Table of contents
- Single-coherator elementary expansion and `OAIRealization C` localization
- Explicit `theoryToOAI` / `modelToOAI` coherator and realization transport

## iv. References
- Alexander Grothendieck, *Pursuing Stacks* (1983)
- Simon Henry, *Algebraic models of homotopy types and the homotopy hypothesis* (arXiv:1609.04622)

### Three-Bucket Audit Map
* **BUCKET 1 (Keep / Proved Kernel Content):**
  `elementary_expansion_with_same_coherator_oai_realization`,
  `coherator_transport_theoryToOAI_and_realization_bridge`.
* **BUCKET 2 (Delete / Rejected Surrogates):**
  None; directly connects `OAI.Grothendieck` and `HomotopyHypothesis.Blueprint` / `Bridge.Statement`.
* **BUCKET 3 (Conditional / Open Context):**
  Conditional on `hC : C.IsCoherator`, `hX : X.IsCellular`, `square`, and `hC_top : C_top.IsCoherator`.
-/

namespace InfoGeometry.Canonical.GrothendieckCoheratorRealizationBridge

universe u v

open CategoryTheory

/-- **Single-Coherator Elementary Expansion and Topological Realization (Rank 2a).**
For a single coherator `C : OAI.Grothendieck.GlobularTheory.{v}` (`hC : C.IsCoherator`), cellular
`C`-model `X`, and elementary expansion pushout `square`:
1. `i : X ⟶ Y` satisfies `OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hC i`
   (which is definitionally `HomotopyHypothesis.Blueprint.W hC i`),
2. That exact same coherator `C` admits a topological realization
   `Nonempty (HomotopyHypothesis.Blueprint.OAIRealization C)`,
3. For every `R : HomotopyHypothesis.Blueprint.OAIRealization C`, `R.Pi` sends weak homotopy
   equivalences in `TopCat.{v}` to `WeakEquivalence hC` in `C.Model` and exhibits
   `R.Pi ⋙ (HomotopyHypothesis.Blueprint.W hC).Q` as the localization of `TopCat.{v}` at
   `HomotopyHypothesis.weakHomotopyEquivalences`. -/
theorem elementary_expansion_with_same_coherator_oai_realization
    (C : OAI.Grothendieck.GlobularTheory.{v}) (hC : C.IsCoherator)
    (X : C.Model) (hX : X.IsCellular) (n : ℕ)
    (a : OAI.Grothendieck.GlobularTheory.Model.disk C n ⟶ X)
    (Y : C.Model) (i : X ⟶ Y)
    (b : OAI.Grothendieck.GlobularTheory.Model.disk C (n + 1) ⟶ Y)
    (square : CategoryTheory.IsPushout a (OAI.Grothendieck.GlobularTheory.Model.J C n) i b) :
    OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hC i ∧
    HomotopyHypothesis.Blueprint.W hC i ∧
    Nonempty (HomotopyHypothesis.Blueprint.OAIRealization C) ∧
    (∀ R : HomotopyHypothesis.Blueprint.OAIRealization C,
      HomotopyHypothesis.weakHomotopyEquivalences ≤
        (HomotopyHypothesis.Blueprint.W hC).inverseImage R.Pi ∧
      (R.Pi ⋙ (HomotopyHypothesis.Blueprint.W hC).Q).IsLocalization
        HomotopyHypothesis.weakHomotopyEquivalences) := by
  have hWE : OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hC i :=
    OAI.Grothendieck.elementary_expansion C hC X hX n a Y i b square
  have hOAI := HomotopyHypothesis.Blueprint.oaiStatement C hC
  exact ⟨hWE, hWE, hOAI.1, hOAI.2⟩

/-- **Explicit Coherator and Realization Transport across `theoryToOAI` (Rank 2b).**
For any `C_top : HomotopyHypothesis.Grothendieck.GlobularTheory.{u}` (`hC_top : C_top.IsCoherator`):
1. `C := HomotopyHypothesis.Bridge.Statement.theoryToOAI C_top` is an OAI coherator
   (`isCoherator_theoryToOAI hC_top`),
2. `realizationToOAI` and `realizationOfOAI` transport realizations between `C_top` and
   `theoryToOAI C_top`, so both `Nonempty (HomotopyHypothesis.Blueprint.OAIRealization (theoryToOAI C_top))`
   and `Nonempty (HomotopyHypothesis.TopRealization C_top)` hold simultaneously,
3. `modelToOAI C_top : C_top.Model ⥤ (theoryToOAI C_top).Model` preserves and reflects model weak
   equivalences (`weakEquivalence_modelToOAI_iff`),
4. `modelToOAI C_top ⋙ (HomotopyHypothesis.Blueprint.W (isCoherator_theoryToOAI hC_top)).Q` is a
   localization of `C_top.Model` at `HomotopyHypothesis.modelWeakEquivalences hC_top`. -/
theorem coherator_transport_theoryToOAI_and_realization_bridge
    (C_top : HomotopyHypothesis.Grothendieck.GlobularTheory.{u})
    (hC_top : C_top.IsCoherator)
    {M₁ M₂ : C_top.Model} (f : M₁ ⟶ M₂) :
    (HomotopyHypothesis.Bridge.Statement.theoryToOAI C_top).IsCoherator ∧
    Nonempty (HomotopyHypothesis.Blueprint.OAIRealization
      (HomotopyHypothesis.Bridge.Statement.theoryToOAI C_top)) ∧
    Nonempty (HomotopyHypothesis.TopRealization C_top) ∧
    (HomotopyHypothesis.Grothendieck.GlobularTheory.Model.WeakEquivalence hC_top f ↔
      OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence
        (HomotopyHypothesis.Bridge.Statement.isCoherator_theoryToOAI hC_top)
        ((HomotopyHypothesis.Bridge.Statement.modelToOAI C_top).map f)) ∧
    (HomotopyHypothesis.Bridge.Statement.modelToOAI C_top ⋙
      (HomotopyHypothesis.Blueprint.W
        (HomotopyHypothesis.Bridge.Statement.isCoherator_theoryToOAI hC_top)).Q).IsLocalization
      (HomotopyHypothesis.modelWeakEquivalences hC_top) := by
  have hC : (HomotopyHypothesis.Bridge.Statement.theoryToOAI C_top).IsCoherator :=
    HomotopyHypothesis.Bridge.Statement.isCoherator_theoryToOAI hC_top
  obtain ⟨⟨R_oai⟩, _⟩ := HomotopyHypothesis.Blueprint.oaiStatement
    (HomotopyHypothesis.Bridge.Statement.theoryToOAI C_top) hC
  refine ⟨hC, ⟨R_oai⟩, ⟨HomotopyHypothesis.Bridge.Statement.realizationOfOAI R_oai⟩,
    (HomotopyHypothesis.Bridge.Statement.weakEquivalence_modelToOAI_iff hC_top hC f).symm,
    HomotopyHypothesis.Bridge.Statement.localization_modelToOAI hC_top hC⟩

end InfoGeometry.Canonical.GrothendieckCoheratorRealizationBridge
