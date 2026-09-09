import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Lie.RealSplitOctonionG2Classification
import InfoGeometry.Lie.BaezG2SplitOctonion
import InfoGeometry.Lie.RealSplitOctonionDerivation
import InfoGeometry.Lie.RealSplitOctonionDerivationData
import InfoGeometry.Lie.CanonicalZornG2UnificationBridge
import InfoGeometry.Lie.SplitG2RealFormCapstone
import InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationExponential
import InfoGeometry.Lie.CanonicalZornRootSystemComparison
import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import Mathlib.Tactic

/-!
# Native classification of `G₂(2)` and `G_{2(2)}` (real split form)

This module ties the repo's existing theorem-checked surfaces into a single
native classification layer for both forms of the exceptional `G₂`:

* **`G₂(2)`** — the finite Chevalley group of type `G₂` over `𝔽₂`.
  `G₂(2) = Aut(O_s(𝔽₂))`.  The carrier type and `Group` structure live in
  `InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem` as `SplitOctF2Aut`.

* **`G_{2(2)}`** — the real split form of `G₂`.
  `G_{2(2)} = Aut(O_s(ℝ))`.  The carrier type is `RealSplitOctonionAut`
  (the real split-octonion automorphism subgroup) in
  `InfoGeometry.Canonical.SplitOctonionAutomorphism`.  Its derivation Lie
  algebra is the canonical 14-dimensional split-`𝔤₂`, whose
  finite-dimension theorem is owned by
  `InfoGeometry.Lie.RealSplitOctonionG2Classification`
  and unified in `InfoGeometry.Lie.CanonicalZornG2UnificationBridge`.

Both carrier types and their algebraic structure are **native Lean**: the
group laws, the 14-dimensional derivation bound, the 12-root system, and
the exact order arithmetic are all kernel-checked theorems here — no axiom,
no `sorry`, no external enumeration is invoked inside this file itself.

### Open closure debt
The exact enumeration count `|G₂(2)| = 12096` is *read back* through the
conditional theorem `aut_splitOctF2_card_eq_g2twoOrder_from_enumeration`,
whose enumeration premise is produced by the external companion verifier
(`tools/sympy/g2_2_automorphism_theorem.py`).  Performing the full 12096-element
enumeration inside the Lean kernel is not done here.
-/

noncomputable section

namespace InfoGeometry.Lie.G2TwoRealSplitClassification

open InfoGeometry.Canonical
open InfoGeometry.Lie.RealSplitOctonionG2Classification
open InfoGeometry.Lie.BaezG2SplitOctonion
open InfoGeometry.Lie.RealSplitOctonionDerivationData
open InfoGeometry.Lie.CanonicalZornG2UnificationBridge
open InfoGeometry.Lie.SplitG2RealFormCapstone
open InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationExponential
open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

------------------------------------------------------------------
/-! ## Shorthands for the G2Two owner identifiers -/
------------------------------------------------------------------

abbrev G2Two :=
  InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut

abbrev g2twoOrder : Nat :=
  InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.g2twoOrder

abbrev g2twoDerivedOrder : Nat :=
  InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.psu33Order

------------------------------------------------------------------
/-! ## `G₂(2)` — finite Chevalley group -/
------------------------------------------------------------------

/-- `G₂(2)` inherits the exact group structure of `SplitOctF2Aut`. -/
instance : Group G2Two := by
  change Group (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut)
  infer_instance

/-- The exact arithmetic factorization `|G₂(2)| = 2⁶ · (2⁶−1) · (2²−1)`. -/
theorem g2two_order_formula :
    g2twoOrder = 2 ^ 6 * (2 ^ 6 - 1) * (2 ^ 2 - 1) := by
  show g2twoOrder = 2 ^ 6 * (2 ^ 6 - 1) * (2 ^ 2 - 1)
  exact
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.g2two_order_formula

/-- The arithmetic value of the order-ledger constant is `12096`.

This is not a theorem about `Fintype.card G2Two`; that carrier cardinality
requires the separate enumeration premise below. -/
theorem g2two_order_ledger_value : g2twoOrder = 12096 := by
  exact g2two_order_formula.trans (by norm_num)

/-- `|G₂(2)| = 2 · |G₂(2)'|`, i.e. the derived subgroup `G₂(2)' ≅ PSU₃(3)`
has index 2. -/
theorem g2two_derived_half : g2twoOrder / 2 = g2twoDerivedOrder := by
  exact
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.g2two_derived_order

/-- `G₂(2)` and `PGL₃(3)` have different orders, ruling out misidentification. -/
theorem g2two_neq_pgl33 :
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.pgl33Order ≠
    g2twoOrder :=
  InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.pgl33_order_ne_g2two_order

/-- Read-back the enumeration theorem from the owner surface.

The premise `h_enum` is the enumeration count produced by the companion
verifier.  Given it, the group order equals `12096`. -/
theorem g2two_card_from_enumeration
    (h_enum : Fintype.card G2Two = 12096) :
    Fintype.card G2Two = g2twoOrder :=
  InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.aut_splitOctF2_card_eq_g2twoOrder_from_enumeration h_enum

------------------------------------------------------------------
/-! ## `G_{2(2)}` — real split form -/
------------------------------------------------------------------

/-- The real split form `G_{2(2)} = Aut(O_s(ℝ))`. -/
abbrev G2RealSplit := RealSplitOctonionAut

/-- The derivation Lie algebra of the real split form, owned by the
`CanonicalZornDerivation` module. -/
abbrev G2RealSplitDerivation := canonicalZornDerivations

/-- The real split `G₂` derivation space has finite dimension `14` over `ℝ`. -/
theorem g2_real_split_derivation_finrank :
    Module.finrank ℝ G2RealSplitDerivation = 14 :=
  canonical_split_octonion_derivation_finrank

/-- The `0-1` rotation derivation is a real-split-`G₂` derivation. -/
theorem rot01Linear_is_g2_real_split_derivation :
    IsNonAssocDerivation (R := ℝ)
      (A := InfoGeometry.Lie.RealSplitOctonionDerivation.SplitCayley) rot01Linear :=
  InfoGeometry.Lie.BaezG2SplitOctonion.rot01Linear_is_derivation

/-- The `0-1` rotation derivation is nonzero on `up0`. -/
theorem rot01Linear_nonzero_on_up0 :
    ∃ X : InfoGeometry.Lie.RealSplitOctonionDerivation.SplitCayley,
      rot01Linear X ≠ 0 :=
  ⟨up0, rot01Real_nonzero_on_up0⟩

------------------------------------------------------------------
/-! ## Bridge: real split form → real derivation Lie algebra -/
------------------------------------------------------------------

/-- The real-split-`G₂` root system has exactly 12 roots. -/
theorem g2_real_split_root_count : Fintype.card RootIndex = 12 :=
  rootIndex_card

/-- The real-split-`G₂` Cartan subalgebra is abelian of dimension 2. -/
theorem g2_real_split_cartan :
    Module.finrank ℝ axialCartanLieSubalgebra = 2 :=
  axialCartanLieSubalgebra_finrank

/-- Every canonical derivation exponential integrates to the native real
automorphism group `G_{2(2)} = Aut(O_s(ℝ))`. -/
theorem split_g2_derivation_exponential_integrates_to_realAut
    (D : canonicalZornDerivations) (t : ℝ) :
    ∃ F : G2RealSplit,
      (F : SplitOctonionAutCandidate ℝ) = zornFlowLinearEquiv D.1 t :=
  ⟨zornFlowRealAut D t, zornFlowRealAut_coe D t⟩

/-- The native real automorphism flow is a one-parameter subgroup of `G_{2(2)}`. -/
theorem split_g2_real_aut_is_one_parameter_subgroup
    (D : canonicalZornDerivations) (s t : ℝ) :
    zornFlowRealAut D (s + t) =
      zornFlowRealAut D s * zornFlowRealAut D t :=
  zornFlowRealAut_add D s t

/-- Complete real-form capstone: 14-dimensional derivation Lie algebra with
12-root system and one-parameter automorphism flow in `G_{2(2)}`. -/
theorem g2_real_split_capstone :
    Module.finrank ℝ G2RealSplitDerivation = 14 ∧
      Fintype.card RootIndex = 12 ∧
        (∀ (D : canonicalZornDerivations) (s t : ℝ),
          zornFlowRealAut D (s + t) =
            zornFlowRealAut D s * zornFlowRealAut D t) := by
  refine ⟨canonical_split_octonion_derivation_finrank, rootIndex_card, ?_⟩
  exact fun D s t => zornFlowRealAut_add D s t

end InfoGeometry.Lie.G2TwoRealSplitClassification
