import InfoGeometry.LLM.AllTopThermodynamicRouter
import InfoGeometry.LLM.TransformerArchitecture
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM.AllTopThermodynamicTransformer

open InfoGeometry.Canonical.MoE
open InfoGeometry.LLM.AllTopThermodynamicRouter
open InfoGeometry.LLM.ThermodynamicSwitching

/--
All-top thermodynamic layer that reuses a base decoder layer and adds a routed MoE branch.
-/
structure ReusedAllTopLayer (V : Type*) [AddCommMonoid V] (n : Nat) where
  base : DecoderLayer V
  routedMoE : MoELayer n V

namespace ReusedAllTopLayer

section Core

variable {Tok V : Type*}
variable [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

/-- Routed all-top thermodynamic contribution on token `i`. -/
noncomputable def routedAllTop
    (L : ReusedAllTopLayer V n)
    (β : ℝ) (x : Tok → V) (i : Tok) : V :=
  allTopMixture (n := n) L.routedMoE β x i

/-- One-token update: reused base update plus all-top routed correction. -/
noncomputable def runToken
    (L : ReusedAllTopLayer V n)
    (β : ℝ) (x : Tok → V) (i : Tok) : V :=
  L.base.run (x i) + L.routedAllTop β x i

/-- Tokenwise state update for this layer. -/
noncomputable def runState
    (L : ReusedAllTopLayer V n)
    (β : ℝ) (x : Tok → V) : Tok → V :=
  fun i => L.runToken β x i

@[simp, rep_depth transport]
theorem runToken_eq_base_plus_routed
    (L : ReusedAllTopLayer V n)
    (β : ℝ) (x : Tok → V) (i : Tok) :
    L.runToken β x i = L.base.run (x i) + L.routedAllTop β x i := rfl

@[rep_depth transport]
theorem routedAllTop_eq_normalizedMixture
    (L : ReusedAllTopLayer V n)
    (β : ℝ) (x : Tok → V) (i : Tok) :
    L.routedAllTop β x i = normalizedMixture L.routedMoE β x i := by
  simpa [routedAllTop] using
    allTopMixture_eq_normalizedMixture
      (n := n) (layer := L.routedMoE) (β := β) (x := x) (i := i)

@[rep_depth transport]
theorem runToken_eq_base_plus_normalizedMixture
    (L : ReusedAllTopLayer V n)
    (β : ℝ) (x : Tok → V) (i : Tok) :
    L.runToken β x i = L.base.run (x i) + normalizedMixture L.routedMoE β x i := by
  rw [runToken_eq_base_plus_routed, routedAllTop_eq_normalizedMixture]

end Core

end ReusedAllTopLayer

section Stack

variable {Tok V : Type*}
variable [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

/-- Tokenwise stack execution for all-top thermodynamic layers. -/
noncomputable def runLayerStack
    (layers : List (ReusedAllTopLayer V n))
    (β : ℝ) (x : Tok → V) : Tok → V :=
  layers.foldl (fun state layer => layer.runState β state) x

@[simp] theorem runLayerStack_nil (β : ℝ) (x : Tok → V) :
    runLayerStack (Tok := Tok) (V := V) (n := n) [] β x = x := by
  rfl

@[simp] theorem runLayerStack_cons
    (L : ReusedAllTopLayer V n)
    (Ls : List (ReusedAllTopLayer V n))
    (β : ℝ) (x : Tok → V) :
    runLayerStack (Tok := Tok) (V := V) (n := n) (L :: Ls) β x
      = runLayerStack (Tok := Tok) (V := V) (n := n) Ls β (L.runState β x) := by
  rfl

/-- Pointwise execution of the standard decoder stack. -/
noncomputable def runDecoderStackPointwise
    (layers : List (DecoderLayer V)) (x : Tok → V) : Tok → V :=
  fun i => runDecoderStack layers (x i)

end Stack

namespace WeightReuse

section Core

variable {Tok V : Type*}
variable [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

/-- Zero expert used to prove exact-reuse fallback behavior. -/
def zeroExpert : Expert V where
  apply := fun _ => 0

/-- Zero routed MoE layer (all experts are zero maps). -/
def zeroMoE : MoELayer n V where
  experts := fun _ => zeroExpert (V := V)

@[simp] theorem allTopMixture_zeroMoE
    (β : ℝ) (x : Tok → V) (i : Tok) :
    allTopMixture (n := n) (zeroMoE (V := V) (n := n)) β x i = 0 := by
  unfold allTopMixture maskedNormalizedMixture zeroMoE zeroExpert
  simp

/-- Attach a zero routed branch to a base decoder layer. -/
def withZeroMoE (B : DecoderLayer V) : ReusedAllTopLayer V n where
  base := B
  routedMoE := zeroMoE (V := V) (n := n)

@[rep_depth transport]
theorem runToken_withZeroMoE_eq_base
    (B : DecoderLayer V) (β : ℝ) (x : Tok → V) (i : Tok) :
    (withZeroMoE (V := V) (n := n) B).runToken β x i = B.run (x i) := by
  unfold ReusedAllTopLayer.runToken ReusedAllTopLayer.routedAllTop withZeroMoE
  rw [allTopMixture_zeroMoE (V := V) (n := n) (β := β) (x := x) (i := i)]
  simp

@[rep_depth transport]
theorem runState_withZeroMoE_eq_pointwise
    (B : DecoderLayer V) (β : ℝ) (x : Tok → V) :
    (withZeroMoE (V := V) (n := n) B).runState β x
      = fun i => B.run (x i) := by
  funext i
  simpa [ReusedAllTopLayer.runState] using
    runToken_withZeroMoE_eq_base (V := V) (n := n) B β x i

/--
Stack-level exact reuse theorem:
if routed branches are all zero, thermodynamic stack execution collapses
to pointwise execution of the base decoder stack.
-/
@[rep_depth transport]
theorem runLayerStack_map_withZeroMoE_eq_pointwise
    (layers : List (DecoderLayer V)) (β : ℝ) (x : Tok → V) :
    runLayerStack (Tok := Tok) (V := V) (n := n)
      (layers.map (withZeroMoE (V := V) (n := n))) β x
      =
    runDecoderStackPointwise (Tok := Tok) (V := V) layers x := by
  induction layers generalizing x with
  | nil =>
      rfl
  | cons L Ls ih =>
      funext i
      have hih := congrArg (fun f : Tok → V => f i)
        (ih ((withZeroMoE (V := V) (n := n) L).runState β x))
      simpa [runLayerStack, runDecoderStackPointwise,
        runState_withZeroMoE_eq_pointwise (Tok := Tok) (V := V) (n := n)]
        using hih

end Core

end WeightReuse

section Model

variable {Tok V Logits : Type*}
variable [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

/-- Full all-top thermodynamic backbone. -/
structure AllTopThermodynamicBackbone [AddCommMonoid V] where
  tokenEmbedding : Tok → V
  layers : List (ReusedAllTopLayer V n)
  finalNorm : V → V

namespace AllTopThermodynamicBackbone

noncomputable def hiddenState
    (B : AllTopThermodynamicBackbone (Tok := Tok) (V := V) (n := n))
    (β : ℝ) (tok : Tok) : V :=
  runLayerStack (Tok := Tok) (V := V) (n := n) B.layers β B.tokenEmbedding tok

noncomputable def normalizedState
    (B : AllTopThermodynamicBackbone (Tok := Tok) (V := V) (n := n))
    (β : ℝ) (tok : Tok) : V :=
  B.finalNorm (B.hiddenState β tok)

end AllTopThermodynamicBackbone

/-- Full all-top thermodynamic language model surface. -/
structure AllTopThermodynamicLanguageModel [AddCommMonoid V] where
  backbone : AllTopThermodynamicBackbone (Tok := Tok) (V := V) (n := n)
  lmHead : V → Logits

namespace AllTopThermodynamicLanguageModel

noncomputable def tokenLogits
    (M : AllTopThermodynamicLanguageModel (Tok := Tok) (V := V) (Logits := Logits) (n := n))
    (β : ℝ) (tok : Tok) : Logits :=
  M.lmHead (M.backbone.normalizedState β tok)

noncomputable def logits
    (M : AllTopThermodynamicLanguageModel (Tok := Tok) (V := V) (Logits := Logits) (n := n))
    (β : ℝ) : Tok → Logits :=
  fun tok => M.tokenLogits β tok

/--
Lift a base decoder LM by reusing token embedding, decoder layers, final norm,
and LM head exactly, while attaching a routed thermodynamic branch per layer.
-/
noncomputable def liftBaseWithRoute
    (base : DecoderLanguageModel Tok V Logits)
    (routeOf : DecoderLayer V → MoELayer n V) :
    AllTopThermodynamicLanguageModel (Tok := Tok) (V := V) (Logits := Logits) (n := n) where
  backbone :=
    { tokenEmbedding := base.backbone.tokenEmbedding
      layers := base.backbone.layers.map (fun L =>
        { base := L
          routedMoE := routeOf L })
      finalNorm := base.backbone.finalNorm }
  lmHead := base.lmHead

@[simp] theorem liftBaseWithRoute_tokenEmbedding
    (base : DecoderLanguageModel Tok V Logits)
    (routeOf : DecoderLayer V → MoELayer n V) :
    (liftBaseWithRoute (Tok := Tok) (V := V) (Logits := Logits) (n := n) base routeOf).backbone.tokenEmbedding
      = base.backbone.tokenEmbedding := rfl

@[simp] theorem liftBaseWithRoute_finalNorm
    (base : DecoderLanguageModel Tok V Logits)
    (routeOf : DecoderLayer V → MoELayer n V) :
    (liftBaseWithRoute (Tok := Tok) (V := V) (Logits := Logits) (n := n) base routeOf).backbone.finalNorm
      = base.backbone.finalNorm := rfl

@[simp] theorem liftBaseWithRoute_lmHead
    (base : DecoderLanguageModel Tok V Logits)
    (routeOf : DecoderLayer V → MoELayer n V) :
    (liftBaseWithRoute (Tok := Tok) (V := V) (Logits := Logits) (n := n) base routeOf).lmHead
      = base.lmHead := rfl

/-- Zero-routed lift: exact reuse mode with thermodynamic branch disabled. -/
noncomputable def liftBaseWithZeroMoE
    (base : DecoderLanguageModel Tok V Logits) :
    AllTopThermodynamicLanguageModel (Tok := Tok) (V := V) (Logits := Logits) (n := n) :=
  liftBaseWithRoute (Tok := Tok) (V := V) (Logits := Logits) (n := n) base
    (fun _ => WeightReuse.zeroMoE (V := V) (n := n))

@[rep_depth transport]
theorem tokenLogits_liftBaseWithZeroMoE_eq_base
    (base : DecoderLanguageModel Tok V Logits)
    (β : ℝ) (tok : Tok) :
    (liftBaseWithZeroMoE (Tok := Tok) (V := V) (Logits := Logits) (n := n) base).tokenLogits β tok
      = base.logits tok := by
  unfold tokenLogits liftBaseWithZeroMoE liftBaseWithRoute
  simp [AllTopThermodynamicBackbone.normalizedState,
    AllTopThermodynamicBackbone.hiddenState]
  change
    base.lmHead
      (base.backbone.finalNorm
        (runLayerStack (Tok := Tok) (V := V) (n := n)
          (base.backbone.layers.map (WeightReuse.withZeroMoE (V := V) (n := n)))
          β base.backbone.tokenEmbedding tok))
      =
    base.logits tok
  have hstack := WeightReuse.runLayerStack_map_withZeroMoE_eq_pointwise
      (Tok := Tok) (V := V) (n := n)
      (layers := base.backbone.layers) (β := β) (x := base.backbone.tokenEmbedding)
  have htok : runLayerStack (Tok := Tok) (V := V) (n := n)
        (base.backbone.layers.map (WeightReuse.withZeroMoE (V := V) (n := n)))
        β base.backbone.tokenEmbedding tok
      =
      runDecoderStackPointwise (Tok := Tok) (V := V) base.backbone.layers base.backbone.tokenEmbedding tok := by
    exact congrArg (fun f : Tok → V => f tok) hstack
  have hlog := congrArg (fun v => base.lmHead (base.backbone.finalNorm v)) htok
  simpa [DecoderLanguageModel.logits, runDecoderStackPointwise] using hlog

@[rep_depth transport]
theorem logits_liftBaseWithZeroMoE_eq_base
    (base : DecoderLanguageModel Tok V Logits) (β : ℝ) :
    (liftBaseWithZeroMoE (Tok := Tok) (V := V) (Logits := Logits) (n := n) base).logits β
      = base.logits := by
  funext tok
  exact tokenLogits_liftBaseWithZeroMoE_eq_base
    (Tok := Tok) (V := V) (Logits := Logits) (n := n) base β tok

end AllTopThermodynamicLanguageModel

end Model

end InfoGeometry.LLM.AllTopThermodynamicTransformer
