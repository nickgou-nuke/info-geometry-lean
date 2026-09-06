import InfoGeometry.Tensor.DeBruijn

namespace InfoGeometry
namespace Tensor

/-!
# De Bruijn payload readbacks

This module models the shape of an external graph edge record without granting
authority to the graph store and without adding a proof-carrier layer above
`InfoGeometry.Tensor.DeBruijn`.

Graph endpoints and role strings are ordinary navigation payload.  A record
conducts only when its payload reads back to the lower `DeBruijnEdge` predicates.
-/

/-- Physical graph endpoints for an external graph record.

These endpoints model storage/navigation identity such as Arango `_from` and
`_to`.  They are not De Bruijn coordinates and carry no proof authority. -/
structure GraphEndpoints where
  source : String
  target : String
  deriving Repr, DecidableEq

namespace GraphEndpoints

end GraphEndpoints

/-- External edge-payload coordinates that can be read back to a Lean
`DeBruijnEdge`.

The field order keeps endpoint-free local coordinates separate from graph
storage endpoints.  The fields mirror a conservative JSON-like payload, but this
structure itself is only Lean data. -/
structure DeBruijnPayload where
  sourceArity : ℕ
  targetArity : ℕ
  sourcePort : ℕ
  targetPort : ℕ
  binderDepth : ℕ
  scopeDepth : ℕ
  sourceBondDim : ℕ
  targetBondDim : ℕ
  deriving Repr, DecidableEq

namespace DeBruijnPayload

/-- Read a payload back into the lower Lean edge kernel. -/
def toEdge (p : DeBruijnPayload) : DeBruijnEdge where
  sourceArity := p.sourceArity
  targetArity := p.targetArity
  sourcePort := p.sourcePort
  targetPort := p.targetPort
  binderDepth := p.binderDepth
  scopeDepth := p.scopeDepth
  sourceBondDim := p.sourceBondDim
  targetBondDim := p.targetBondDim

@[simp] theorem toEdge_sourceArity (p : DeBruijnPayload) :
    p.toEdge.sourceArity = p.sourceArity :=
  rfl

@[simp] theorem toEdge_targetArity (p : DeBruijnPayload) :
    p.toEdge.targetArity = p.targetArity :=
  rfl

@[simp] theorem toEdge_sourcePort (p : DeBruijnPayload) :
    p.toEdge.sourcePort = p.sourcePort :=
  rfl

@[simp] theorem toEdge_targetPort (p : DeBruijnPayload) :
    p.toEdge.targetPort = p.targetPort :=
  rfl

@[simp] theorem toEdge_binderDepth (p : DeBruijnPayload) :
    p.toEdge.binderDepth = p.binderDepth :=
  rfl

@[simp] theorem toEdge_scopeDepth (p : DeBruijnPayload) :
    p.toEdge.scopeDepth = p.scopeDepth :=
  rfl

@[simp] theorem toEdge_sourceBondDim (p : DeBruijnPayload) :
    p.toEdge.sourceBondDim = p.sourceBondDim :=
  rfl

@[simp] theorem toEdge_targetBondDim (p : DeBruijnPayload) :
    p.toEdge.targetBondDim = p.targetBondDim :=
  rfl

/-- Payload-level in-scope condition, defined by lower-kernel readback. -/
def InScope (p : DeBruijnPayload) : Prop :=
  p.toEdge.InScope

/-- Payload-level port-compatibility condition, defined by lower-kernel readback. -/
def PortCompatible (p : DeBruijnPayload) : Prop :=
  p.toEdge.PortCompatible

/-- Payload-level conductivity condition: direct lower-kernel contraction soundness. -/
def Conductive (p : DeBruijnPayload) : Prop :=
  p.toEdge.ContractionSound

/-- Payload conductivity is exactly the conjunction required by the lower kernel. -/
theorem conductive_iff (p : DeBruijnPayload) :
    p.Conductive ↔ p.InScope ∧ p.PortCompatible :=
  Iff.rfl

/-- Backwards-compatible spelling for candidate selection. -/
theorem promotable_iff (p : DeBruijnPayload) :
    p.Conductive ↔ p.InScope ∧ p.PortCompatible :=
  p.conductive_iff

/-- Read back the source-port bound from a payload-level scope proof. -/
theorem source_port_lt {p : DeBruijnPayload} (h : p.InScope) :
    p.sourcePort < p.sourceArity :=
  DeBruijnEdge.source_port_lt h

/-- Read back the target-port bound from a payload-level scope proof. -/
theorem target_port_lt {p : DeBruijnPayload} (h : p.InScope) :
    p.targetPort < p.targetArity :=
  DeBruijnEdge.target_port_lt h

/-- Read back the binder/scope bound from a payload-level scope proof. -/
theorem scope_sound {p : DeBruijnPayload} (h : p.InScope) :
    p.binderDepth ≤ p.scopeDepth :=
  DeBruijnEdge.scope_sound h

/-- Direct lower-kernel soundness from payload evidence, without packaging. -/
theorem conductive_of_inScope_compatible {p : DeBruijnPayload}
    (hscope : p.InScope) (hcompat : p.PortCompatible) : p.Conductive :=
  DeBruijnEdge.sound_of_inScope_compatible hscope hcompat

/-- Read back local compatibility from direct conductivity evidence. -/
theorem compatible_of_conductive {p : DeBruijnPayload} (h : p.Conductive) :
    p.sourceBondDim = p.targetBondDim :=
  DeBruijnEdge.compatible_of_sound h

end DeBruijnPayload

/-- Candidate graph record for a De Bruijn contraction.

The candidate role is data only.  It does not certify the payload. -/
structure CandidateContractionRecord where
  endpoints : GraphEndpoints
  payload : DeBruijnPayload
  deriving Repr, DecidableEq

namespace CandidateContractionRecord

/-- The conventional external role string for candidate records. -/
def role (_ : CandidateContractionRecord) : String :=
  "candidate_contraction"

@[simp] theorem role_eq (r : CandidateContractionRecord) :
    r.role = "candidate_contraction" :=
  rfl

/-- A candidate record conducts exactly when its payload conducts through the lower kernel. -/
def Conductive (r : CandidateContractionRecord) : Prop :=
  r.payload.Conductive

/-- Candidate-record conductivity is Lean kernel contraction soundness after
payload readback. -/
theorem conductive_iff (r : CandidateContractionRecord) :
    r.Conductive ↔ r.payload.toEdge.ContractionSound :=
  Iff.rfl

/-- Backwards-compatible spelling for candidate selection. -/
theorem promotable_iff (r : CandidateContractionRecord) :
    r.Conductive ↔ r.payload.toEdge.ContractionSound :=
  r.conductive_iff

/-- Read back source-port boundedness from direct lower-kernel conductivity. -/
theorem source_port_lt {r : CandidateContractionRecord} (h : r.Conductive) :
    r.payload.sourcePort < r.payload.sourceArity :=
  DeBruijnPayload.source_port_lt h.1

/-- Read back target-port boundedness from direct lower-kernel conductivity. -/
theorem target_port_lt {r : CandidateContractionRecord} (h : r.Conductive) :
    r.payload.targetPort < r.payload.targetArity :=
  DeBruijnPayload.target_port_lt h.1

/-- Read back binder/scope boundedness from direct lower-kernel conductivity. -/
theorem scope_sound {r : CandidateContractionRecord} (h : r.Conductive) :
    r.payload.binderDepth ≤ r.payload.scopeDepth :=
  DeBruijnPayload.scope_sound h.1

/-- Read back local bond-dimension compatibility from direct lower-kernel conductivity. -/
theorem compatible_of_conductive {r : CandidateContractionRecord} (h : r.Conductive) :
    r.payload.sourceBondDim = r.payload.targetBondDim :=
  DeBruijnPayload.compatible_of_conductive h

end CandidateContractionRecord

end Tensor
end InfoGeometry
