import InfoGeometry.LLM.TransformerArchitecture
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LLM.TrialityMoE
import InfoGeometry.LLM.SpinPinTransformerLayer
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM

open InfoGeometry.LLM.TrialityMoE
open SpinPinTransformerLayer

section Spec

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]

local notation "N" => InfoGeometry.Krein.NeutralSpace S
local notation "EndN" => N →L[ℝ] N

variable {Pos Expert : Type*} [Fintype Expert] [DecidableEq Expert]

/--
Llama4-style operatorial block specification on the doubled-real carrier:
- iRoPE positional blend,
- two-stage residual update,
- shared+routed MoE output,
- spin-transport + Pin/CPT checker.
-/
structure Llama4BlockSpec where
  irope : IropeBlend Pos EndN
  residual : TwoStageResidualBlock (H := EndN)
  moe : SharedRoutedMoEBlock (X := EndN) (V := EndN) (E := Expert)
  spinPin : SpinPinTransformerLayer (E := S)

namespace Llama4BlockSpec

/-- Position-aware query lane. -/
noncomputable def positionedQuery (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (p : Pos) (x : EndN) : EndN :=
  B.irope.query p x

/-- Position-aware key lane. -/
noncomputable def positionedKey (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (p : Pos) (x : EndN) : EndN :=
  B.irope.key p x

/-- Residual two-stage update lane. -/
noncomputable def residualUpdate (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (x : EndN) : EndN :=
  B.residual.run x

/-- Shared+routed MoE update lane. -/
noncomputable def routedUpdate (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (x : EndN) : EndN :=
  B.moe.output x

/-- Core block update before the spin/pin checker lane. -/
noncomputable def coreUpdate (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (x : EndN) : EndN :=
  B.residualUpdate x + B.routedUpdate x

/-- Full spin/pin-checked block update. -/
noncomputable def run (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (x : EndN) : EndN :=
  B.spinPin.layer.run (B.coreUpdate x)

section OmitDecidableEqRoutingLemmas

omit [DecidableEq Expert]

@[simp] theorem routedUpdate_split
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert)) (x : EndN) :
    B.routedUpdate x =
      (B.moe.shared x + B.moe.routed.activeOutput x) + B.moe.routed.defectOutput x := by
  unfold routedUpdate
  simpa [add_assoc] using (B.moe.output_split_active_defect x)

/--
Assumptions asserting that each routed split component commutes with spin transport.
-/
def IsSplitTransportEquivariant
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert)) : Prop :=
  (∀ t x,
    B.moe.shared (B.spinPin.transport t x) = B.spinPin.transport t (B.moe.shared x)) ∧
  (∀ t x,
    B.moe.routed.activeOutput (B.spinPin.transport t x) =
      B.spinPin.transport t (B.moe.routed.activeOutput x)) ∧
  (∀ t x,
    B.moe.routed.defectOutput (B.spinPin.transport t x) =
      B.spinPin.transport t (B.moe.routed.defectOutput x))

/--
Split-component transport equivariance implies transport equivariance of total routed output.
-/
@[rep_depth transport]
theorem routedUpdate_transport_commute_of_split
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (hEq : IsSplitTransportEquivariant (B := B))
    (t : ℝ) (x : EndN) :
    B.routedUpdate (B.spinPin.transport t x) =
      B.spinPin.transport t (B.routedUpdate x) := by
  unfold routedUpdate
  have hL : B.moe.output (B.spinPin.transport t x) =
      B.moe.shared (B.spinPin.transport t x) + B.moe.routed.activeOutput (B.spinPin.transport t x) := by
    simpa using B.moe.output_eq_shared_plus_active (B.spinPin.transport t x)
  have hR : B.moe.output x = B.moe.shared x + B.moe.routed.activeOutput x := by
    simpa using B.moe.output_eq_shared_plus_active x
  calc
    B.moe.output (B.spinPin.transport t x)
        = B.moe.shared (B.spinPin.transport t x) + B.moe.routed.activeOutput (B.spinPin.transport t x) := hL
    _ = B.spinPin.transport t (B.moe.shared x) + B.spinPin.transport t (B.moe.routed.activeOutput x) := by
          rw [hEq.1 t x, hEq.2.1 t x]
    _ = B.spinPin.transport t (B.moe.shared x + B.moe.routed.activeOutput x) := by
          symm
          exact SpinPinTransformerLayer.transport_add (B := B.spinPin) (t := t)
            (X := B.moe.shared x) (Y := B.moe.routed.activeOutput x)
    _ = B.spinPin.transport t (B.moe.output x) := by rw [hR]

/--
End-to-end split law under transport:
if routed output commutes with transport, the `(shared + active + defect)`
shape is preserved by transport.
-/
@[rep_depth transport]
theorem transport_preserves_routed_split
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (hOut : ∀ t x,
      B.routedUpdate (B.spinPin.transport t x) =
        B.spinPin.transport t (B.routedUpdate x))
    (t : ℝ) (x : EndN) :
    B.routedUpdate (B.spinPin.transport t x) =
      B.spinPin.transport t (B.moe.shared x + B.moe.routed.activeOutput x) +
      B.spinPin.transport t (B.moe.routed.defectOutput x) := by
  have hDef : B.moe.routed.defectOutput x = 0 := B.moe.routed.defectOutput_eq_zero x
  rw [hOut t x]
  have hMain :
      B.spinPin.transport t (B.routedUpdate x) =
        B.spinPin.transport t (B.moe.shared x + B.moe.routed.activeOutput x) := by
    unfold routedUpdate
    rw [B.moe.output_eq_shared_plus_active x]
  calc
    B.spinPin.transport t (B.routedUpdate x)
        = B.spinPin.transport t (B.moe.shared x + B.moe.routed.activeOutput x) := hMain
    _ = B.spinPin.transport t (B.moe.shared x + B.moe.routed.activeOutput x) +
          B.spinPin.transport t (B.moe.routed.defectOutput x) := by
            rw [hDef, SpinPinTransformerLayer.transport_zero (B := B.spinPin) (t := t)]
            simp

/--
Transport-preserved routed split via split-component equivariance assumptions.
-/
@[rep_depth transport]
theorem transport_preserves_routed_split_of_split
    (B : Llama4BlockSpec (S := S) (Pos := Pos) (Expert := Expert))
    (hEq : IsSplitTransportEquivariant (B := B))
    (t : ℝ) (x : EndN) :
    B.routedUpdate (B.spinPin.transport t x) =
      B.spinPin.transport t (B.moe.shared x + B.moe.routed.activeOutput x) +
      B.spinPin.transport t (B.moe.routed.defectOutput x) := by
  exact transport_preserves_routed_split (B := B)
    (hOut := routedUpdate_transport_commute_of_split (B := B) hEq) t x

end OmitDecidableEqRoutingLemmas

end Llama4BlockSpec

end Spec

end InfoGeometry.LLM
