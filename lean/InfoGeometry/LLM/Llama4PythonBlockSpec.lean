import InfoGeometry.LLM.TrialityMoE
import InfoGeometry.LLM.TransformerArchitecture
import InfoGeometry.Meta.Architecture

open scoped BigOperators

namespace InfoGeometry.LLM
namespace Llama4PythonBlockSpec

section Router

variable {X Expert : Type*} [Fintype Expert] [DecidableEq Expert]

/-- Scalar gate used by the routed MoE path (`torch.sigmoid` in vendor code). -/
noncomputable def sigmoid (z : ℝ) : ℝ :=
  (1 + Real.exp (-z))⁻¹

/--
Top-k sparse router surface extracted from `models/llama4/moe.py`:
- raw scores per token/expert,
- top-k selection mask,
- routed weights are `sigmoid(score)` on selected experts and `0` otherwise.
-/
structure TopKRouter where
  rawScore : X → Expert → ℝ
  selected : X → Expert → Bool
  topK : Nat
  selected_card_le : ∀ x, (Finset.univ.filter (fun e => selected x e)).card ≤ topK

namespace TopKRouter

noncomputable def weight (R : TopKRouter (X := X) (Expert := Expert)) (x : X) (e : Expert) : ℝ :=
  if R.selected x e then sigmoid (R.rawScore x e) else 0

section OmitDecidableEqRouterLemmas

omit [DecidableEq Expert]

@[simp]
theorem weight_of_selected
    (R : TopKRouter (X := X) (Expert := Expert)) (x : X) (e : Expert)
    (h : R.selected x e = true) :
    R.weight x e = sigmoid (R.rawScore x e) := by
  simp [weight, h]

@[simp]
theorem weight_of_not_selected
    (R : TopKRouter (X := X) (Expert := Expert)) (x : X) (e : Expert)
    (h : R.selected x e = false) :
    R.weight x e = 0 := by
  simp [weight, h]

end OmitDecidableEqRouterLemmas

/-- Adapter into the shared sparse-router owner surface. -/
noncomputable def toSparseRouter (R : TopKRouter (X := X) (Expert := Expert)) :
    TrialityMoE.SparseRouter (X := X) (E := Expert) where
  weight := R.weight
  gate := R.selected
  inactive_weight_eq_zero := by
    intro x e h
    simp [weight, h]

end TopKRouter

end Router

section SharedTopKMoE

variable {X V Expert : Type*} [Fintype Expert] [DecidableEq Expert]
variable [AddCommMonoid V] [Module ℝ V]

/--
Llama4 routed FFN lane with one always-on shared expert plus top-k routed experts.
This mirrors `out = shared_expert(x) + routed_experts(x)` from `models/llama4/moe.py`.
-/
structure SharedTopKMoE where
  sharedExpert : X → V
  routedExpert : Expert → X → V
  router : TopKRouter (X := X) (Expert := Expert)

namespace SharedTopKMoE

noncomputable def routedBlock (B : SharedTopKMoE (X := X) (V := V) (Expert := Expert)) :
    TrialityMoE.TrialityMoEBlock (X := X) (V := V) (E := Expert) where
  router := B.router.toSparseRouter
  expert := B.routedExpert

noncomputable def asSharedRouted (B : SharedTopKMoE (X := X) (V := V) (Expert := Expert)) :
    TrialityMoE.SharedRoutedMoEBlock (X := X) (V := V) (E := Expert) where
  shared := B.sharedExpert
  routed := B.routedBlock

noncomputable def output (B : SharedTopKMoE (X := X) (V := V) (Expert := Expert)) (x : X) : V :=
  B.asSharedRouted.output x

section OmitDecidableEqSharedTopK

omit [DecidableEq Expert]

@[simp]
theorem output_eq_shared_plus_total
    (B : SharedTopKMoE (X := X) (V := V) (Expert := Expert)) (x : X) :
    B.output x = B.sharedExpert x + B.routedBlock.totalOutput x := by
  rfl

/--
Canonical Llama4 MoE law: output equals shared path + active routed path.
The shared expert is always present in the final output.
-/
@[rep_depth transport]
theorem output_eq_shared_plus_active
    (B : SharedTopKMoE (X := X) (V := V) (Expert := Expert)) (x : X) :
    B.output x = B.sharedExpert x + B.routedBlock.activeOutput x := by
  unfold output asSharedRouted routedBlock
  simpa using
    (TrialityMoE.SharedRoutedMoEBlock.output_eq_shared_plus_active
      (B := {
        shared := B.sharedExpert
        routed := {
          router := B.router.toSparseRouter
          expert := B.routedExpert
        }
      }) x)

end OmitDecidableEqSharedTopK

end SharedTopKMoE

end SharedTopKMoE

section TransformerBlock

variable {S Mask : Type*}

/--
Minimal block-level surface matching `models/llama4/model.py`:
- NoPE toggle controls RoPE and qk-norm usage,
- global-vs-local mask selection,
- pre-norm attention residual, then pre-norm FFN/MoE residual.
-/
structure TransformerBlock where
  isNopeLayer : Bool
  baseUseQkNorm : Bool
  useRope : Bool
  useQkNorm : Bool
  globalMask : Mask
  localMask : Option Mask
  attentionNorm : S → S
  ffnNorm : S → S
  attention : S → S
  feedForward : S → S
  useRope_eq_not_isNope : useRope = !isNopeLayer
  useQkNorm_eq_base_and_not_isNope : useQkNorm = (baseUseQkNorm && !isNopeLayer)

namespace TransformerBlock

def selectedMask (B : TransformerBlock (S := S) (Mask := Mask)) : Mask :=
  if B.isNopeLayer then B.globalMask
  else
    match B.localMask with
    | some m => m
    | none => B.globalMask

@[simp] theorem selectedMask_of_nope
    (B : TransformerBlock (S := S) (Mask := Mask))
    (h : B.isNopeLayer = true) :
    B.selectedMask = B.globalMask := by
  simp [selectedMask, h]

@[simp] theorem selectedMask_of_local
    (B : TransformerBlock (S := S) (Mask := Mask))
    {m : Mask}
    (hNope : B.isNopeLayer = false)
    (hLocal : B.localMask = some m) :
    B.selectedMask = m := by
  simp [selectedMask, hNope, hLocal]

@[simp] theorem selectedMask_of_missing_local
    (B : TransformerBlock (S := S) (Mask := Mask))
    (hNope : B.isNopeLayer = false)
    (hLocal : B.localMask = none) :
    B.selectedMask = B.globalMask := by
  simp [selectedMask, hNope, hLocal]

@[simp] theorem useRope_eq_not_nope
    (B : TransformerBlock (S := S) (Mask := Mask)) :
    B.useRope = !B.isNopeLayer := B.useRope_eq_not_isNope

@[simp] theorem useQkNorm_eq_base_and_not_nope
    (B : TransformerBlock (S := S) (Mask := Mask)) :
    B.useQkNorm = (B.baseUseQkNorm && !B.isNopeLayer) :=
  B.useQkNorm_eq_base_and_not_isNope

def afterAttention [AddCommMonoid S]
    (B : TransformerBlock (S := S) (Mask := Mask)) (x : S) : S :=
  x + B.attention (B.attentionNorm x)

def run [AddCommMonoid S]
    (B : TransformerBlock (S := S) (Mask := Mask)) (x : S) : S :=
  let h := B.afterAttention x
  h + B.feedForward (B.ffnNorm h)

/-- Exact residual update law from the extracted Python block. -/
@[rep_depth transport]
theorem run_eq_python_block_update
    [AddCommMonoid S]
    (B : TransformerBlock (S := S) (Mask := Mask)) (x : S) :
    B.run x =
      let h := x + B.attention (B.attentionNorm x)
      h + B.feedForward (B.ffnNorm h) := by
  rfl

end TransformerBlock

end TransformerBlock

end Llama4PythonBlockSpec
end InfoGeometry.LLM
