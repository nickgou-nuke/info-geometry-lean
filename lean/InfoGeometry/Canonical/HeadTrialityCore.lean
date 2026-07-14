import InfoGeometry.Canonical.Triality
import InfoGeometry.Canonical.HyperbolicRotor
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.HeadTrialityCore

Interface owner for blocked triality hypotheses on head structure.

This file does **not** assert literal triality on an arbitrary head dimension.
It packages the safe ansatz:

- represent each head as blocks of 8-dimensional cells,
- interpret `Q/K/V` as a blockwise triadic object,
- expose a structured-trinity predicate to be studied/proved downstream.
-/

namespace HeadTrialityCore

open InfoGeometry.Canonical.Triality

section BlockedCore

/-- A `cellDim`-dimensional head cell over `ℝ`. -/
abbrev CellVector (cellDim : Nat) := Fin cellDim → ℝ

/-- A blocked head representation with `blocks` many cells of dimension `cellDim`. -/
abbrev BlockedHead (blocks cellDim : Nat) := Fin blocks → CellVector cellDim

/-- Blockwise `Q/K/V` triple. -/
structure BlockedQKV (blocks cellDim : Nat) where
  Q : BlockedHead blocks cellDim
  K : BlockedHead blocks cellDim
  V : BlockedHead blocks cellDim

/--
Blocked triality ansatz:
all blocks share a common cell-level metric triadic core.
-/
structure BlockedTrialityDatum (blocks cellDim : Nat) where
  qkv : BlockedQKV blocks cellDim
  cellCore : MetricTriadicCore (CellVector cellDim) (CellVector cellDim) (CellVector cellDim)

/-- Cellwise routed output induced from `Q` and `K`. -/
noncomputable def routedCell {blocks cellDim : Nat}
    (T : BlockedTrialityDatum blocks cellDim) (b : Fin blocks) : CellVector cellDim :=
  T.cellCore.route (T.qkv.Q b) (T.qkv.K b)

/--
Structured-trinity predicate:
`V` is exactly the cellwise triadic route of `Q` and `K`.
-/
def IsStructuredTrinity {blocks cellDim : Nat}
    (T : BlockedTrialityDatum blocks cellDim) : Prop :=
  ∀ b : Fin blocks, routedCell T b = T.qkv.V b

/-- Residual cell error of the triadic route against `V`. -/
noncomputable def cellResidual {blocks cellDim : Nat}
    (T : BlockedTrialityDatum blocks cellDim) (b : Fin blocks) : CellVector cellDim :=
  T.qkv.V b - routedCell T b

/-- Equivalent zero-residual characterization of structured trinity. -/
theorem isStructuredTrinity_iff_cellResidual_eq_zero
    {blocks cellDim : Nat} (T : BlockedTrialityDatum blocks cellDim) :
    IsStructuredTrinity T ↔ ∀ b : Fin blocks, cellResidual T b = 0 := by
  constructor
  · intro h b
    have hb := h b
    unfold routedCell at hb
    unfold cellResidual routedCell
    rw [hb]
    simp
  · intro h b
    have h0 := h b
    unfold cellResidual routedCell at h0
    exact (sub_eq_zero.mp h0).symm

/-- Certified blocked triality package. -/
structure CertifiedBlockedTrialityDatum (blocks cellDim : Nat)
    extends BlockedTrialityDatum blocks cellDim where
  structured : IsStructuredTrinity toBlockedTrialityDatum

/-- In a certified package, each blockwise route equals its `V`-cell. -/
theorem routedCell_eq_value_of_structured
    {blocks cellDim : Nat}
    (T : CertifiedBlockedTrialityDatum blocks cellDim) (b : Fin blocks) :
    routedCell T.toBlockedTrialityDatum b = T.qkv.V b :=
  T.structured b

end BlockedCore

section SplitDoubledLane

/-- Real 64-dimensional Majorana half-head lane. -/
abbrev MajoranaHalf64 := Fin 64 → ℝ

/-- Real 64-dimensional Weyl half-head lane. -/
abbrev WeylHalf64 := Fin 64 → ℝ

/--
Split-doubled head package for the `128 = 2 × 64` presentation.

This lane is intentionally real/split and does not use a complex-scalar
primitive.
-/
structure SplitDoubledHead128 where
  majorana : MajoranaHalf64
  weyl : WeylHalf64

/--
Mass-like coupling interface from Majorana to Weyl lanes.
-/
structure MajoranaWeylCoupling where
  massMap : MajoranaHalf64 →ₗ[ℝ] WeylHalf64

/-- Coupled Weyl lane after applying the mass-like Majorana→Weyl map. -/
noncomputable def coupledWeylLane
    (H : SplitDoubledHead128) (C : MajoranaWeylCoupling) : WeylHalf64 :=
  C.massMap H.majorana + H.weyl

/-- Coupled split-doubled head package. -/
noncomputable def coupledSplitDoubledHead128
    (H : SplitDoubledHead128) (C : MajoranaWeylCoupling) : SplitDoubledHead128 :=
  { majorana := H.majorana
    weyl := coupledWeylLane H C }

/-- Dimension sanity check for the split-doubled head lane. -/
theorem splitDoubled128_dimension :
    (2 : Nat) * (64 : Nat) = 128 := by
  decide

end SplitDoubledLane

section HyperbolicBoostLane

open InfoGeometry.Canonical.HyperbolicRotor
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/--
Head-lane hyperbolic boost rotor hook.

This reuses the canonical split `Cl(1,1)` head rotor and keeps the triality
interface in the Hestenes/hyperbolic-boost register.
-/
@[rep_depth transport]
noncomputable def headHyperbolicBoostRotor (n : ℕ) (θ : ℝ) :
    SplitClNNTensorStep n :=
  hyperbolicRotor n θ

@[rep_depth transport, simp]
theorem headHyperbolicBoostRotor_zero (n : ℕ) :
    headHyperbolicBoostRotor n 0 = (1 : SplitClNNTensorStep n) := by
  simp [headHyperbolicBoostRotor]

end HyperbolicBoostLane

section Head128

/-- Canonical blocked presentation for a 128-dimensional head: `16 × 8`. -/
abbrev BlockedHead128 := BlockedHead 16 8

/-- Canonical blocked `Q/K/V` triple for 128-dimensional heads. -/
abbrev BlockedQKV128 := BlockedQKV 16 8

/-- Canonical blocked-triality datum for 128-dimensional heads. -/
abbrev BlockedTriality128 := BlockedTrialityDatum 16 8

/-- Canonical certified blocked-triality datum for 128-dimensional heads. -/
abbrev CertifiedBlockedTriality128 := CertifiedBlockedTrialityDatum 16 8

/-- Dimension sanity check for the blocked ansatz. -/
theorem blocked128_dimension :
    (16 : Nat) * (8 : Nat) = 128 := by
  decide

/--
Interface proposition for the "blocked triality ansatz" at head dimension 128.
-/
def IsBlockedTriality128 (T : BlockedTriality128) : Prop :=
  IsStructuredTrinity T

/-- Certified 128-head packages satisfy the blocked triality proposition. -/
theorem isBlockedTriality128_of_structured (T : CertifiedBlockedTriality128) :
    IsBlockedTriality128 T.toBlockedTrialityDatum := by
  exact T.structured

end Head128

end HeadTrialityCore
