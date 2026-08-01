import Mathlib.Data.Nat.Basic

/-!
# De Bruijn tensor-port controller

This file is a small Mathlib-rooted kernel for the tensor-overlay doctrine.  It
models Arango-style edge payloads as local port/scope coordinates while keeping
certification as direct Lean predicates/readbacks on the lower module itself.

There is deliberately no extra carrier layer here: candidate graph payloads
remain plain data, and conductivity is obtained by proving the local predicates
exposed by this module.
-/

namespace InfoGeometry
namespace Tensor

/-- A local port coordinate on a tensor-like object.

`arity` is the number of exposed slots/ports and `index` is the selected slot.
The proof field is direct Lean evidence that the payload coordinate is in
bounds. -/
abbrev TensorPort : Type :=
  {p : ℕ × ℕ // p.2 < p.1}

namespace TensorPort

@[simp] def arity (p : TensorPort) : ℕ :=
  p.1.1

@[simp] def index (p : TensorPort) : ℕ :=
  p.1.2

@[simp] def inBounds (p : TensorPort) : p.index < p.arity :=
  p.2

@[simp] theorem index_lt_arity (p : TensorPort) : p.index < p.arity :=
  p.inBounds

/-- The raw natural number used by an external graph edge payload. -/
def rawIndex (p : TensorPort) : ℕ :=
  p.index

@[simp] theorem rawIndex_eq (p : TensorPort) : p.rawIndex = p.index :=
  rfl

end TensorPort

/-- Candidate De Bruijn-style payload carried by a graph edge.

The fields are intentionally plain natural numbers so they can mirror JSON
payloads such as `port_source`, `port_target`, `binder_depth`, and
`scope_delta`.  The lower module itself exposes the predicates that make a
payload conduct: no separate carrier is introduced as proof authority. -/
structure DeBruijnEdge where
  sourceArity : ℕ
  targetArity : ℕ
  sourcePort : ℕ
  targetPort : ℕ
  binderDepth : ℕ
  scopeDepth : ℕ
  sourceBondDim : ℕ
  targetBondDim : ℕ
  deriving Repr, DecidableEq

namespace DeBruijnEdge

/-- The source port payload is inside the source arity, the target port payload
is inside the target arity, and the De Bruijn depth is inside the current
scope. -/
def InScope (e : DeBruijnEdge) : Prop :=
  e.sourcePort < e.sourceArity ∧ e.targetPort < e.targetArity ∧ e.binderDepth ≤ e.scopeDepth

/-- Minimal local type-compatibility proxy for a contraction edge: the two bond
dimensions agree.  A future tensor/operator theory can replace or refine this
with richer typed fibres. -/
def PortCompatible (e : DeBruijnEdge) : Prop :=
  e.sourceBondDim = e.targetBondDim

/-- A candidate edge is contraction-sound exactly when its coordinates are in
scope and its local bond dimensions are compatible. -/
def ContractionSound (e : DeBruijnEdge) : Prop :=
  e.InScope ∧ e.PortCompatible

/-- Direct constructor for a candidate edge from already-bounded tensor ports.

This is data construction, not an added certification layer.  Soundness is read
back by the theorems below from the lower module predicates. -/
def ofPorts (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    DeBruijnEdge where
  sourceArity := source.arity
  targetArity := target.arity
  sourcePort := source.index
  targetPort := target.index
  binderDepth := binderDepth
  scopeDepth := scopeDepth
  sourceBondDim := sourceBondDim
  targetBondDim := targetBondDim

@[simp] theorem ofPorts_sourceArity
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).sourceArity =
      source.arity :=
  rfl

@[simp] theorem ofPorts_targetArity
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).targetArity =
      target.arity :=
  rfl

@[simp] theorem ofPorts_sourcePort
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).sourcePort =
      source.index :=
  rfl

@[simp] theorem ofPorts_targetPort
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).targetPort =
      target.index :=
  rfl

/-- Read back the source-port bound from direct `InScope` evidence. -/
theorem source_port_lt {e : DeBruijnEdge} (h : e.InScope) : e.sourcePort < e.sourceArity :=
  h.1

/-- Read back the target-port bound from direct `InScope` evidence. -/
theorem target_port_lt {e : DeBruijnEdge} (h : e.InScope) : e.targetPort < e.targetArity :=
  h.2.1

/-- Read back the De Bruijn binder/scope bound from direct `InScope` evidence. -/
theorem scope_sound {e : DeBruijnEdge} (h : e.InScope) : e.binderDepth ≤ e.scopeDepth :=
  h.2.2

/-- Read back local bond-dimension compatibility from direct compatibility evidence. -/
theorem compatible_of_sound {e : DeBruijnEdge} (h : e.ContractionSound) :
    e.sourceBondDim = e.targetBondDim :=
  h.2

/-- Direct promotion theorem: a payload with lower-module predicate evidence is
contraction-sound, without wrapping it in an added object. -/
theorem sound_of_inScope_compatible {e : DeBruijnEdge}
    (hscope : e.InScope) (hcompat : e.PortCompatible) : e.ContractionSound :=
  ⟨hscope, hcompat⟩

/-- Port-bounded construction is in scope exactly when the De Bruijn binder depth
is inside the ambient scope. -/
theorem ofPorts_inScope_iff
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).InScope ↔
      binderDepth ≤ scopeDepth := by
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨source.inBounds, target.inBounds, h⟩

/-- Port-bounded construction is compatible exactly when the endpoint bond dimensions agree. -/
theorem ofPorts_portCompatible_iff
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).PortCompatible ↔
      sourceBondDim = targetBondDim := by
  rfl

/-- Lift an edge payload through `delta` additional binders/scopes.

The endpoints and port coordinates are unchanged; only the local De Bruijn depth
and the ambient scope depth are lifted together. -/
def lift (delta : ℕ) (e : DeBruijnEdge) : DeBruijnEdge :=
  { e with
    binderDepth := e.binderDepth + delta
    scopeDepth := e.scopeDepth + delta }

/-- A proposed rewrite is shift/lift-sound when it is exactly the structural
lift of the original payload. -/
def ShiftSound (delta : ℕ) (before after : DeBruijnEdge) : Prop :=
  after = before.lift delta

@[simp] theorem lift_sourceArity (delta : ℕ) (e : DeBruijnEdge) :
    (e.lift delta).sourceArity = e.sourceArity :=
  rfl

@[simp] theorem lift_targetArity (delta : ℕ) (e : DeBruijnEdge) :
    (e.lift delta).targetArity = e.targetArity :=
  rfl

@[simp] theorem lift_sourcePort (delta : ℕ) (e : DeBruijnEdge) :
    (e.lift delta).sourcePort = e.sourcePort :=
  rfl

@[simp] theorem lift_targetPort (delta : ℕ) (e : DeBruijnEdge) :
    (e.lift delta).targetPort = e.targetPort :=
  rfl

@[simp] theorem lift_binderDepth (delta : ℕ) (e : DeBruijnEdge) :
    (e.lift delta).binderDepth = e.binderDepth + delta :=
  rfl

@[simp] theorem lift_scopeDepth (delta : ℕ) (e : DeBruijnEdge) :
    (e.lift delta).scopeDepth = e.scopeDepth + delta :=
  rfl

@[simp] theorem lift_sourceBondDim (delta : ℕ) (e : DeBruijnEdge) :
    (e.lift delta).sourceBondDim = e.sourceBondDim :=
  rfl

@[simp] theorem lift_targetBondDim (delta : ℕ) (e : DeBruijnEdge) :
    (e.lift delta).targetBondDim = e.targetBondDim :=
  rfl

/-- Lifting preserves source/target port bounds and binder scope bounds. -/
theorem lift_inScope {delta : ℕ} {e : DeBruijnEdge} (h : e.InScope) :
    (e.lift delta).InScope := by
  rcases h with ⟨hs, ht, hb⟩
  exact ⟨hs, ht, Nat.add_le_add_right hb delta⟩

/-- Lifting preserves the local bond-dimension compatibility predicate. -/
theorem lift_portCompatible {delta : ℕ} {e : DeBruijnEdge} (h : e.PortCompatible) :
    (e.lift delta).PortCompatible := by
  simpa [PortCompatible, lift] using h

/-- Lifting preserves contraction soundness. -/
theorem lift_contractionSound {delta : ℕ} {e : DeBruijnEdge}
    (h : e.ContractionSound) : (e.lift delta).ContractionSound :=
  ⟨lift_inScope h.1, lift_portCompatible h.2⟩

/-- The canonical lift proposal is shift-sound by reflexivity. -/
theorem lift_shiftSound (delta : ℕ) (e : DeBruijnEdge) :
    ShiftSound delta e (e.lift delta) :=
  rfl

end DeBruijnEdge

end Tensor
end InfoGeometry
