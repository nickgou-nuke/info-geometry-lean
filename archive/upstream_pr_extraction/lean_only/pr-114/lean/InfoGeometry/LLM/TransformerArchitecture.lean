import InfoGeometry.LLM.TransformerBlock
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM

/--
RoPE-style positional interface that rotates query/key lanes at a position `p`.
-/
structure RotaryPositionalLayer (Pos V : Type*) where
  rotateQ : Pos → V → V
  rotateK : Pos → V → V

namespace RotaryPositionalLayer

variable {Pos V : Type*}

/-- Apply positional rotation to a query/key pair. -/
def rotatePair (R : RotaryPositionalLayer Pos V) (p : Pos) (q k : V) : V × V :=
  (R.rotateQ p q, R.rotateK p k)

@[simp] theorem rotatePair_fst (R : RotaryPositionalLayer Pos V) (p : Pos) (q k : V) :
    (R.rotatePair p q k).1 = R.rotateQ p q := rfl

@[simp] theorem rotatePair_snd (R : RotaryPositionalLayer Pos V) (p : Pos) (q k : V) :
    (R.rotatePair p q k).2 = R.rotateK p k := rfl

end RotaryPositionalLayer

/--
Kramers-pair structure on a latent space:
an involutive partner map identifies conjugate lanes.
-/
structure KramersPairing (V : Type*) where
  partner : V → V
  involutive_partner : Function.Involutive partner

namespace KramersPairing

variable {V : Type*}

@[simp] theorem partner_partner (K : KramersPairing V) (x : V) :
    K.partner (K.partner x) = x :=
  K.involutive_partner x

end KramersPairing

/--
iRoPE-style blend of elliptic (rotary) and hyperbolic positional actions.
`mixQ` / `mixK` choose how the two lanes are fused.
-/
structure IropeBlend (Pos V : Type*) where
  rotary : RotaryPositionalLayer Pos V
  hyperbolic : RotaryPositionalLayer Pos V
  mixQ : V → V → V
  mixK : V → V → V

namespace IropeBlend

variable {Pos V : Type*}

def query (B : IropeBlend Pos V) (p : Pos) (q : V) : V :=
  B.mixQ (B.rotary.rotateQ p q) (B.hyperbolic.rotateQ p q)

def key (B : IropeBlend Pos V) (p : Pos) (k : V) : V :=
  B.mixK (B.rotary.rotateK p k) (B.hyperbolic.rotateK p k)

@[simp] theorem query_def (B : IropeBlend Pos V) (p : Pos) (q : V) :
    B.query p q = B.mixQ (B.rotary.rotateQ p q) (B.hyperbolic.rotateQ p q) := rfl

@[simp] theorem key_def (B : IropeBlend Pos V) (p : Pos) (k : V) :
    B.key p k = B.mixK (B.rotary.rotateK p k) (B.hyperbolic.rotateK p k) := rfl

end IropeBlend

/--
Bogoliubov-style linear mixing between two conjugate latent lanes.
`particle` and `hole` are the two linear channels.
-/
structure BogoliubovTransform (V : Type*) [AddCommGroup V] [Module ℝ V] where
  particle : V →ₗ[ℝ] V
  hole : V →ₗ[ℝ] V

namespace BogoliubovTransform

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def forwardPair (B : BogoliubovTransform V) (x y : V) : V × V :=
  (B.particle x + B.hole y, B.particle y + B.hole x)

@[simp] theorem forwardPair_fst (B : BogoliubovTransform V) (x y : V) :
    (B.forwardPair x y).1 = B.particle x + B.hole y := rfl

@[simp] theorem forwardPair_snd (B : BogoliubovTransform V) (x y : V) :
    (B.forwardPair x y).2 = B.particle y + B.hole x := rfl

end BogoliubovTransform

/--
Minimal KV-cache interface.

`keyAt`/`valueAt` expose the cached key-value pair at each position.
-/
structure KVCache (Pos K V : Type*) where
  keyAt : Pos → Option K
  valueAt : Pos → Option V

namespace KVCache

variable {Pos K V : Type*} [DecidableEq Pos]

/-- Cache write at one position. -/
def write (C : KVCache Pos K V) (p : Pos) (k : K) (v : V) : KVCache Pos K V where
  keyAt := fun i => if i = p then some k else C.keyAt i
  valueAt := fun i => if i = p then some v else C.valueAt i

@[simp] theorem keyAt_write_same (C : KVCache Pos K V) (p : Pos) (k : K) (v : V) :
    (C.write p k v).keyAt p = some k := by
  simp [write]

@[simp] theorem valueAt_write_same (C : KVCache Pos K V) (p : Pos) (k : K) (v : V) :
    (C.write p k v).valueAt p = some v := by
  simp [write]

@[simp] theorem keyAt_write_ne (C : KVCache Pos K V) (p i : Pos) (k : K) (v : V)
    (h : i ≠ p) :
    (C.write p k v).keyAt i = C.keyAt i := by
  simp [write, h]

@[simp] theorem valueAt_write_ne (C : KVCache Pos K V) (p i : Pos) (k : K) (v : V)
    (h : i ≠ p) :
    (C.write p k v).valueAt i = C.valueAt i := by
  simp [write, h]

end KVCache

/--
SwiGLU-style feed-forward abstraction:
- gate branch
- up branch
- activation and combination
- down projection
-/
structure GatedFeedForward (V : Type*) [AddCommGroup V] [Module ℝ V] where
  gateProj : V →ₗ[ℝ] V
  upProj : V →ₗ[ℝ] V
  activate : V → V
  combine : V → V → V
  downProj : V →ₗ[ℝ] V

namespace GatedFeedForward

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Pre-down state: combine activated gate branch with up branch. -/
def preDown (B : GatedFeedForward V) (x : V) : V :=
  B.combine (B.activate (B.gateProj x)) (B.upProj x)

/-- Full FFN output. -/
def run (B : GatedFeedForward V) (x : V) : V :=
  B.downProj (B.preDown x)

@[simp] theorem run_def (B : GatedFeedForward V) (x : V) :
    B.run x = B.downProj (B.combine (B.activate (B.gateProj x)) (B.upProj x)) := rfl

end GatedFeedForward

/--
Decoder-layer interface with pre-norm attention and pre-norm feed-forward updates.
-/
structure DecoderLayer (V : Type*) [AddCommMonoid V] where
  preAttentionNorm : V → V
  attention : V → V
  preFFNNorm : V → V
  feedForward : V → V

namespace DecoderLayer

variable {V : Type*} [AddCommMonoid V]

/-- `h = x + attention(preAttentionNorm x)` -/
def afterAttention (B : DecoderLayer V) (x : V) : V :=
  x + B.attention (B.preAttentionNorm x)

/-- `out = h + feedForward(preFFNNorm h)` -/
def afterFeedForward (B : DecoderLayer V) (x : V) : V :=
  let h := B.afterAttention x
  h + B.feedForward (B.preFFNNorm h)

/-- Full decoder-layer update. -/
def run (B : DecoderLayer V) (x : V) : V :=
  B.afterFeedForward x

/--
Canonical two-residual decoder law.
-/
@[rep_depth transport]
theorem run_eq_two_stage_residual (B : DecoderLayer V) (x : V) :
    B.run x =
      let h := x + B.attention (B.preAttentionNorm x)
      h + B.feedForward (B.preFFNNorm h) := by
  rfl

end DecoderLayer

/-- Left-to-right layer-stack execution for decoder layers. -/
def runDecoderStack {V : Type*} [AddCommMonoid V] (layers : List (DecoderLayer V)) (x : V) : V :=
  layers.foldl (fun state layer => layer.run state) x

section StackLemmas

variable {V : Type*} [AddCommMonoid V]

@[simp] theorem runDecoderStack_nil (x : V) :
    runDecoderStack ([] : List (DecoderLayer V)) x = x := by
  rfl

@[simp] theorem runDecoderStack_cons (L : DecoderLayer V) (Ls : List (DecoderLayer V)) (x : V) :
    runDecoderStack (L :: Ls) x = runDecoderStack Ls (L.run x) := by
  rfl

/-- Stack composition law: running `L₁ ++ L₂` equals `L₁` then `L₂`. -/
@[rep_depth transport]
  theorem runDecoderStack_append (L₁ L₂ : List (DecoderLayer V)) (x : V) :
    runDecoderStack (L₁ ++ L₂) x = runDecoderStack L₂ (runDecoderStack L₁ x) := by
  induction L₁ generalizing x with
  | nil =>
      simp [runDecoderStack]
  | cons L Ls ih =>
      simp [runDecoderStack]

end StackLemmas

/-- Backbone surface: token embedding + decoder stack + final normalization. -/
structure TransformerBackbone (Tok V : Type*) [AddCommMonoid V] where
  tokenEmbedding : Tok → V
  layers : List (DecoderLayer V)
  finalNorm : V → V

namespace TransformerBackbone

variable {Tok V : Type*} [AddCommMonoid V]

def hiddenState (B : TransformerBackbone Tok V) (tok : Tok) : V :=
  runDecoderStack B.layers (B.tokenEmbedding tok)

def normalizedState (B : TransformerBackbone Tok V) (tok : Tok) : V :=
  B.finalNorm (B.hiddenState tok)

@[simp] theorem hiddenState_def (B : TransformerBackbone Tok V) (tok : Tok) :
    B.hiddenState tok = runDecoderStack B.layers (B.tokenEmbedding tok) := rfl

@[simp] theorem normalizedState_def (B : TransformerBackbone Tok V) (tok : Tok) :
    B.normalizedState tok = B.finalNorm (B.hiddenState tok) := rfl

end TransformerBackbone

/-- Full decoder model with LM-head projection. -/
structure DecoderLanguageModel (Tok V Logits : Type*) [AddCommMonoid V] where
  backbone : TransformerBackbone Tok V
  lmHead : V → Logits

namespace DecoderLanguageModel

variable {Tok V Logits : Type*} [AddCommMonoid V]

def logits (M : DecoderLanguageModel Tok V Logits) (tok : Tok) : Logits :=
  M.lmHead (M.backbone.normalizedState tok)

@[simp] theorem logits_def (M : DecoderLanguageModel Tok V Logits) (tok : Tok) :
    M.logits tok = M.lmHead (M.backbone.finalNorm (runDecoderStack M.backbone.layers (M.backbone.tokenEmbedding tok))) := rfl

end DecoderLanguageModel

end InfoGeometry.LLM
