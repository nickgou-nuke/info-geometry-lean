import InfoGeometry.LLM.TransformerArchitecture
import InfoGeometry.LLM.PinCPTBridge
import InfoGeometry.Canonical.SpinConnection
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace TensorProduct

namespace InfoGeometry.LLM

open InfoGeometry.Canonical
open InfoGeometry.LLM.PinCPTBridge
open InfoGeometry.Canonical.SplitCliffordTensorBridge

section SpinPinLayer

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "N" => InfoGeometry.Krein.NeutralSpace E
local notation "EndN" => N →L[ℝ] N

/--
Transformer decoder layer over endomorphisms, equipped with
- a spin transport on the doubled-real/Krein carrier,
- a Pin-style involutive conjugation for CPT parity checks.
-/
structure SpinPinTransformerLayer where
  layer : DecoderLayer EndN
  spin : SpinConnection E
  pin : PinAction (A := EndN)

namespace SpinPinTransformerLayer

/-- Endomorphism transport induced by the layer's spin connection. -/
noncomputable def transport (B : SpinPinTransformerLayer (E := E)) (t : ℝ) (X : EndN) : EndN :=
  transportEnd B.spin t X

@[simp] theorem transport_add
    (B : SpinPinTransformerLayer (E := E)) (t : ℝ) (X Y : EndN) :
    B.transport t (X + Y) = B.transport t X + B.transport t Y := by
  unfold transport
  exact transportEnd_add B.spin t X Y

@[simp] theorem transport_zero
    (B : SpinPinTransformerLayer (E := E)) (t : ℝ) :
    B.transport t (0 : EndN) = 0 := by
  unfold transport
  exact transportEnd_zero B.spin t

@[simp] theorem transport_smul
    (B : SpinPinTransformerLayer (E := E)) (t : ℝ) (a : ℝ) (X : EndN) :
    B.transport t (a • X) = a • B.transport t X := by
  unfold transport
  exact transportEnd_smul B.spin t a X

/-- Layer update gap `run X - X`. -/
noncomputable def gap (B : SpinPinTransformerLayer (E := E)) (X : EndN) : EndN :=
  B.layer.run X - X

/-- Expanded two-stage residual form for transported input. -/
@[rep_depth transport]
theorem run_transport_expansion
    (B : SpinPinTransformerLayer (E := E)) (t : ℝ) (X : EndN) :
    B.layer.run (B.transport t X) =
      let h := B.transport t X + B.layer.attention (B.layer.preAttentionNorm (B.transport t X))
      h + B.layer.feedForward (B.layer.preFFNNorm h) := by
  simpa [transport] using
    (DecoderLayer.run_eq_two_stage_residual (B := B.layer) (x := B.transport t X))

/-- Equivariance assumptions for the decoder submaps against spin transport. -/
structure IsSpinEquivariant (B : SpinPinTransformerLayer (E := E)) : Prop where
  preAttentionNorm : ∀ t X, B.layer.preAttentionNorm (B.transport t X) = B.transport t (B.layer.preAttentionNorm X)
  attention : ∀ t X, B.layer.attention (B.transport t X) = B.transport t (B.layer.attention X)
  preFFNNorm : ∀ t X, B.layer.preFFNNorm (B.transport t X) = B.transport t (B.layer.preFFNNorm X)
  feedForward : ∀ t X, B.layer.feedForward (B.transport t X) = B.transport t (B.layer.feedForward X)

/-- First residual stage commutes with spin transport under equivariance assumptions. -/
@[rep_depth transport]
theorem afterAttention_transport_commute
    (B : SpinPinTransformerLayer (E := E))
    (hEq : IsSpinEquivariant (B := B))
    (t : ℝ) (X : EndN) :
    B.layer.afterAttention (B.transport t X) = B.transport t (B.layer.afterAttention X) := by
  unfold DecoderLayer.afterAttention
  rw [hEq.preAttentionNorm t X]
  rw [hEq.attention t (B.layer.preAttentionNorm X)]
  unfold transport
  exact (transportEnd_add B.spin t X (B.layer.attention (B.layer.preAttentionNorm X))).symm

/-- Second residual stage commutes with spin transport under equivariance assumptions. -/
@[rep_depth transport]
theorem afterFeedForward_transport_commute
    (B : SpinPinTransformerLayer (E := E))
    (hEq : IsSpinEquivariant (B := B))
    (t : ℝ) (X : EndN) :
    B.layer.afterFeedForward (B.transport t X) = B.transport t (B.layer.afterFeedForward X) := by
  unfold DecoderLayer.afterFeedForward
  set hX : EndN := B.layer.afterAttention X
  have hAh : B.layer.afterAttention (B.transport t X) = B.transport t hX := by
    simpa [hX] using afterAttention_transport_commute (B := B) hEq t X
  calc
    B.layer.afterAttention (B.transport t X) +
        B.layer.feedForward (B.layer.preFFNNorm (B.layer.afterAttention (B.transport t X)))
        = B.transport t hX + B.layer.feedForward (B.layer.preFFNNorm (B.transport t hX)) := by
            simp [hAh]
    _ = B.transport t hX + B.layer.feedForward (B.transport t (B.layer.preFFNNorm hX)) := by
          rw [hEq.preFFNNorm t hX]
    _ = B.transport t hX + B.transport t (B.layer.feedForward (B.layer.preFFNNorm hX)) := by
          rw [hEq.feedForward t (B.layer.preFFNNorm hX)]
    _ = B.transport t (hX + B.layer.feedForward (B.layer.preFFNNorm hX)) := by
          unfold transport
          exact
            (transportEnd_add B.spin t hX (B.layer.feedForward (B.layer.preFFNNorm hX))).symm
    _ = B.transport t (B.layer.afterFeedForward X) := by
          simp [hX, DecoderLayer.afterFeedForward]

/-- Full decoder run commutes with spin transport under equivariance assumptions. -/
@[rep_depth transport]
theorem run_transport_commute
    (B : SpinPinTransformerLayer (E := E))
    (hEq : IsSpinEquivariant (B := B))
    (t : ℝ) (X : EndN) :
    B.layer.run (B.transport t X) = B.transport t (B.layer.run X) := by
  unfold DecoderLayer.run
  exact afterFeedForward_transport_commute (B := B) hEq t X

/-- The layer gap is transport-equivariant whenever the layer run is transport-equivariant. -/
@[rep_depth transport]
theorem gap_transport_commute
    (B : SpinPinTransformerLayer (E := E))
    (hEq : IsSpinEquivariant (B := B))
    (t : ℝ) (X : EndN) :
    B.gap (B.transport t X) = B.transport t (B.gap X) := by
  unfold gap
  rw [run_transport_commute (B := B) hEq t X]
  unfold transport
  have hneg : transportEnd B.spin t (-X) = -transportEnd B.spin t X := by
    unfold transportEnd
    exact InfoGeometry.Krein.conjugateCLM_neg (U := (B.spin.U t : N ≃L[ℝ] N)) X
  calc
    transportEnd B.spin t (B.layer.run X) - transportEnd B.spin t X
        = transportEnd B.spin t (B.layer.run X) + transportEnd B.spin t (-X) := by
            rw [sub_eq_add_neg, hneg.symm]
    _ = transportEnd B.spin t (B.layer.run X + (-X)) := by
          exact (transportEnd_add B.spin t (B.layer.run X) (-X)).symm
    _ = transportEnd B.spin t (B.layer.run X - X) := by
          simp [sub_eq_add_neg]

/-- Pin-oddness of the layer gap implies Pin-evenness of its square. -/
@[rep_depth transport]
theorem pin_odd_gap_square_even
    (B : SpinPinTransformerLayer (E := E)) (X : EndN)
    (hOdd : B.pin.IsOdd (B.gap X)) :
    B.pin.IsEven (B.gap X * B.gap X) :=
  B.pin.odd_implies_even_square hOdd

/-- If the layer gap is Pin-odd, conjugation flips its sign. -/
@[rep_depth transport]
theorem pin_conjugate_odd_gap_eq_neg
    (B : SpinPinTransformerLayer (E := E)) (X : EndN)
    (hOdd : B.pin.IsOdd (B.gap X)) :
    B.pin.conjugate (B.gap X) = -B.gap X :=
  B.pin.conjugate_odd_eq_neg hOdd

/-- If the layer gap is Pin-odd, its square is invariant under Pin conjugation. -/
@[rep_depth transport]
theorem pin_conjugate_gap_square_eq_self
    (B : SpinPinTransformerLayer (E := E)) (X : EndN)
    (hOdd : B.pin.IsOdd (B.gap X)) :
    B.pin.conjugate (B.gap X * B.gap X) = B.gap X * B.gap X :=
  B.pin.conjugate_even_square_eq_self hOdd

/-- Pin conjugation on any layer gap is involutive. -/
@[rep_depth transport]
theorem pin_conjugate_gap_involutive
    (B : SpinPinTransformerLayer (E := E)) (X : EndN) :
    B.pin.conjugate (B.pin.conjugate (B.gap X)) = B.gap X :=
  B.pin.conjugate_involutive (B.gap X)

end SpinPinTransformerLayer

/--
`Cl(4,4)` head-factor witness used as the `Pin(4,4)` geometric anchor
for LLM-side spin/transport layers.
-/
@[rep_depth krein]
theorem pin44_headFactor_sorry
    (x : ℝ × ℝ) :
    splitCl44_headFactorEquiv
        (CliffordAlgebra.ι SplitCl44Quad (InfoGeometry.Clifford.ClNN.headPair 3 x))
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 x)
          ᵍ⊗ₜ (1 : CliffordAlgebra (InfoGeometry.CliffordTower.Qsplit 3)) := by
  simpa using splitCl44_headFactor x

end SpinPinLayer

end InfoGeometry.LLM
