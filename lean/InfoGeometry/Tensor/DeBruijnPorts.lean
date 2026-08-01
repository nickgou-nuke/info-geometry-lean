import InfoGeometry.Tensor.DeBruijnLift

namespace InfoGeometry
namespace Tensor

/-!
# De Bruijn port readbacks

This module connects bounded `TensorPort` inputs to endpoint-free
`DeBruijnPayload` values.  It is a direct theorem layer over the lower Lean
modules: bounded source/target ports supply the port inequalities, while the
remaining conductivity conditions are the lower-module scope and compatibility
predicates.
-/

namespace DeBruijnPayload

/-- Build an endpoint-free payload from already-bounded source and target ports. -/
def ofPorts (source target : TensorPort)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) : DeBruijnPayload where
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

@[simp] theorem ofPorts_binderDepth
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).binderDepth =
      binderDepth :=
  rfl

@[simp] theorem ofPorts_scopeDepth
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).scopeDepth =
      scopeDepth :=
  rfl

@[simp] theorem ofPorts_sourceBondDim
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).sourceBondDim =
      sourceBondDim :=
  rfl

@[simp] theorem ofPorts_targetBondDim
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).targetBondDim =
      targetBondDim :=
  rfl

/-- Payload construction from ports reads back definitionally to lower-edge port construction. -/
@[simp] theorem toEdge_ofPorts
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).toEdge =
      DeBruijnEdge.ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim :=
  rfl

/-- For bounded ports, payload scope reduces to the binder/scope inequality. -/
theorem ofPorts_inScope_iff
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).InScope ↔
      binderDepth ≤ scopeDepth := by
  simpa [InScope] using
    DeBruijnEdge.ofPorts_inScope_iff source target binderDepth scopeDepth sourceBondDim
      targetBondDim

/-- For bounded ports, payload compatibility reduces to bond-dimension equality. -/
theorem ofPorts_portCompatible_iff
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).PortCompatible ↔
      sourceBondDim = targetBondDim := by
  rfl

/-- For bounded ports, payload conductivity is exactly binder/scope boundedness
and local bond-dimension equality. -/
theorem ofPorts_conductive_iff
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).Conductive ↔
      binderDepth ≤ scopeDepth ∧ sourceBondDim = targetBondDim := by
  constructor
  · intro h
    exact ⟨(ofPorts_inScope_iff source target binderDepth scopeDepth sourceBondDim
      targetBondDim).1 h.1, h.2⟩
  · intro h
    exact ⟨(ofPorts_inScope_iff source target binderDepth scopeDepth sourceBondDim
      targetBondDim).2 h.1, h.2⟩

/-- Direct conductivity constructor for payloads built from bounded ports. -/
theorem ofPorts_conductive
    (source target : TensorPort) {binderDepth scopeDepth sourceBondDim targetBondDim : ℕ}
    (hscope : binderDepth ≤ scopeDepth) (hcompat : sourceBondDim = targetBondDim) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).Conductive :=
  (ofPorts_conductive_iff source target binderDepth scopeDepth sourceBondDim targetBondDim).2
    ⟨hscope, hcompat⟩

/-- Source-port boundedness is inherited from the source `TensorPort`. -/
theorem ofPorts_source_port_lt
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).sourcePort <
      (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).sourceArity :=
  source.inBounds

/-- Target-port boundedness is inherited from the target `TensorPort`. -/
theorem ofPorts_target_port_lt
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).targetPort <
      (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).targetArity :=
  target.inBounds

/-- Lifting a port-built payload equals rebuilding from the same ports with lifted depths. -/
theorem lift_ofPorts (delta : ℕ)
    (source target : TensorPort) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).lift delta =
      ofPorts source target (binderDepth + delta) (scopeDepth + delta) sourceBondDim
        targetBondDim :=
  rfl

/-- A lifted port-built payload conducts when the original depth/bond conditions hold. -/
theorem lift_ofPorts_conductive (delta : ℕ)
    (source target : TensorPort) {binderDepth scopeDepth sourceBondDim targetBondDim : ℕ}
    (hscope : binderDepth ≤ scopeDepth) (hcompat : sourceBondDim = targetBondDim) :
    ((ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).lift delta).Conductive :=
  lift_conductive (delta := delta) (ofPorts_conductive source target hscope hcompat)

end DeBruijnPayload

namespace CandidateContractionRecord

/-- Build a candidate record from graph endpoints and already-bounded tensor ports. -/
def ofPorts (endpoints : GraphEndpoints) (source target : TensorPort)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) : CandidateContractionRecord :=
  (endpoints, DeBruijnPayload.ofPorts source target binderDepth scopeDepth sourceBondDim
    targetBondDim)

@[simp] theorem ofPorts_endpoints (endpoints : GraphEndpoints) (source target : TensorPort)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts endpoints source target binderDepth scopeDepth sourceBondDim targetBondDim).endpoints =
      endpoints :=
  rfl

@[simp] theorem ofPorts_payload (endpoints : GraphEndpoints) (source target : TensorPort)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts endpoints source target binderDepth scopeDepth sourceBondDim targetBondDim).payload =
      DeBruijnPayload.ofPorts source target binderDepth scopeDepth sourceBondDim targetBondDim :=
  rfl

/-- Candidate records built from bounded ports conduct exactly when the remaining
scope and compatibility conditions hold. -/
theorem ofPorts_conductive_iff (endpoints : GraphEndpoints) (source target : TensorPort)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts endpoints source target binderDepth scopeDepth sourceBondDim targetBondDim).Conductive ↔
      binderDepth ≤ scopeDepth ∧ sourceBondDim = targetBondDim :=
  DeBruijnPayload.ofPorts_conductive_iff source target binderDepth scopeDepth sourceBondDim
    targetBondDim

/-- Direct conductivity constructor for candidate records built from bounded ports. -/
theorem ofPorts_conductive (endpoints : GraphEndpoints) (source target : TensorPort)
    {binderDepth scopeDepth sourceBondDim targetBondDim : ℕ}
    (hscope : binderDepth ≤ scopeDepth) (hcompat : sourceBondDim = targetBondDim) :
    (ofPorts endpoints source target binderDepth scopeDepth sourceBondDim targetBondDim).Conductive :=
  (ofPorts_conductive_iff endpoints source target binderDepth scopeDepth sourceBondDim
    targetBondDim).2 ⟨hscope, hcompat⟩

/-- Lifting a port-built candidate record preserves endpoints and rebuilds its
payload from the same ports with lifted depths. -/
theorem lift_ofPorts (delta : ℕ) (endpoints : GraphEndpoints) (source target : TensorPort)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofPorts endpoints source target binderDepth scopeDepth sourceBondDim targetBondDim).lift delta =
      ofPorts endpoints source target (binderDepth + delta) (scopeDepth + delta)
        sourceBondDim targetBondDim :=
  rfl

end CandidateContractionRecord

end Tensor
end InfoGeometry
