import InfoGeometry.Tensor.DeBruijnPayload

namespace InfoGeometry
namespace Tensor

/-!
# De Bruijn payload lift readbacks

This module is a direct theorem layer over the lower De Bruijn modules.  It adds
no carrier object around the proof.  A lifted payload conducts only by reading
back to `DeBruijnEdge.lift` and reusing the lower-module readback lemmas.
-/

namespace DeBruijnPayload

/-- Lift a payload through `delta` additional binders/scopes.

Endpoint-free payload coordinates for ports and bond dimensions are preserved;
only the local De Bruijn depth and ambient scope depth are lifted together. -/
def lift (delta : ℕ) (p : DeBruijnPayload) : DeBruijnPayload where
  sourceArity := p.sourceArity
  targetArity := p.targetArity
  sourcePort := p.sourcePort
  targetPort := p.targetPort
  binderDepth := p.binderDepth + delta
  scopeDepth := p.scopeDepth + delta
  sourceBondDim := p.sourceBondDim
  targetBondDim := p.targetBondDim

@[simp] theorem lift_sourceArity (delta : ℕ) (p : DeBruijnPayload) :
    (p.lift delta).sourceArity = p.sourceArity :=
  rfl

@[simp] theorem lift_targetArity (delta : ℕ) (p : DeBruijnPayload) :
    (p.lift delta).targetArity = p.targetArity :=
  rfl

@[simp] theorem lift_sourcePort (delta : ℕ) (p : DeBruijnPayload) :
    (p.lift delta).sourcePort = p.sourcePort :=
  rfl

@[simp] theorem lift_targetPort (delta : ℕ) (p : DeBruijnPayload) :
    (p.lift delta).targetPort = p.targetPort :=
  rfl

@[simp] theorem lift_binderDepth (delta : ℕ) (p : DeBruijnPayload) :
    (p.lift delta).binderDepth = p.binderDepth + delta :=
  rfl

@[simp] theorem lift_scopeDepth (delta : ℕ) (p : DeBruijnPayload) :
    (p.lift delta).scopeDepth = p.scopeDepth + delta :=
  rfl

@[simp] theorem lift_sourceBondDim (delta : ℕ) (p : DeBruijnPayload) :
    (p.lift delta).sourceBondDim = p.sourceBondDim :=
  rfl

@[simp] theorem lift_targetBondDim (delta : ℕ) (p : DeBruijnPayload) :
    (p.lift delta).targetBondDim = p.targetBondDim :=
  rfl

/-- Payload lift reads back definitionally to lower-edge lift. -/
@[simp] theorem toEdge_lift (delta : ℕ) (p : DeBruijnPayload) :
    (p.lift delta).toEdge = p.toEdge.lift delta :=
  rfl

/-- Payload lift preserves in-scope evidence by lower-module readback. -/
theorem lift_inScope {delta : ℕ} {p : DeBruijnPayload} (h : p.InScope) :
    (p.lift delta).InScope := by
  simpa [InScope] using DeBruijnEdge.lift_inScope (delta := delta) (e := p.toEdge) h

/-- Payload lift preserves local port compatibility by lower-module readback. -/
theorem lift_portCompatible {delta : ℕ} {p : DeBruijnPayload} (h : p.PortCompatible) :
    (p.lift delta).PortCompatible := by
  simpa [PortCompatible] using
    DeBruijnEdge.lift_portCompatible (delta := delta) (e := p.toEdge) h

/-- Payload lift preserves direct conductivity by lower-module readback. -/
theorem lift_conductive {delta : ℕ} {p : DeBruijnPayload} (h : p.Conductive) :
    (p.lift delta).Conductive := by
  simpa [Conductive] using
    DeBruijnEdge.lift_contractionSound (delta := delta) (e := p.toEdge) h

/-- The canonical payload lift is shift-sound because it reads back to the lower
edge lift. -/
theorem lift_shiftSound (delta : ℕ) (p : DeBruijnPayload) :
    DeBruijnEdge.ShiftSound delta p.toEdge (p.lift delta).toEdge := by
  simp [DeBruijnEdge.ShiftSound]

/-- Source-port boundedness survives payload lift when the original payload conducts. -/
theorem lift_source_port_lt {delta : ℕ} {p : DeBruijnPayload} (h : p.Conductive) :
    (p.lift delta).sourcePort < (p.lift delta).sourceArity :=
  source_port_lt (lift_conductive (delta := delta) h).1

/-- Target-port boundedness survives payload lift when the original payload conducts. -/
theorem lift_target_port_lt {delta : ℕ} {p : DeBruijnPayload} (h : p.Conductive) :
    (p.lift delta).targetPort < (p.lift delta).targetArity :=
  target_port_lt (lift_conductive (delta := delta) h).1

/-- Binder/scope boundedness survives payload lift when the original payload conducts. -/
theorem lift_scope_sound {delta : ℕ} {p : DeBruijnPayload} (h : p.Conductive) :
    (p.lift delta).binderDepth ≤ (p.lift delta).scopeDepth :=
  scope_sound (lift_conductive (delta := delta) h).1

/-- Local bond-dimension compatibility survives payload lift when the original
payload conducts. -/
theorem lift_compatible_of_conductive {delta : ℕ} {p : DeBruijnPayload}
    (h : p.Conductive) :
    (p.lift delta).sourceBondDim = (p.lift delta).targetBondDim :=
  compatible_of_conductive (lift_conductive (delta := delta) h)

end DeBruijnPayload

namespace CandidateContractionRecord

/-- Lift the payload of a candidate graph record while preserving graph endpoints. -/
def lift (delta : ℕ) (r : CandidateContractionRecord) : CandidateContractionRecord :=
  (r.endpoints, r.payload.lift delta)

@[simp] theorem lift_endpoints (delta : ℕ) (r : CandidateContractionRecord) :
    (r.lift delta).endpoints = r.endpoints :=
  rfl

@[simp] theorem lift_payload (delta : ℕ) (r : CandidateContractionRecord) :
    (r.lift delta).payload = r.payload.lift delta :=
  rfl

/-- Candidate-record lift preserves direct conductivity by payload readback. -/
theorem lift_conductive {delta : ℕ} {r : CandidateContractionRecord} (h : r.Conductive) :
    (r.lift delta).Conductive :=
  DeBruijnPayload.lift_conductive (delta := delta) h

/-- Candidate-record lift is shift-sound after payload readback. -/
theorem lift_shiftSound (delta : ℕ) (r : CandidateContractionRecord) :
    DeBruijnEdge.ShiftSound delta r.payload.toEdge (r.lift delta).payload.toEdge :=
  DeBruijnPayload.lift_shiftSound delta r.payload

/-- Source-port boundedness survives candidate-record lift when the original
record conducts. -/
theorem lift_source_port_lt {delta : ℕ} {r : CandidateContractionRecord} (h : r.Conductive) :
    (r.lift delta).payload.sourcePort < (r.lift delta).payload.sourceArity :=
  source_port_lt (lift_conductive (delta := delta) h)

/-- Target-port boundedness survives candidate-record lift when the original
record conducts. -/
theorem lift_target_port_lt {delta : ℕ} {r : CandidateContractionRecord} (h : r.Conductive) :
    (r.lift delta).payload.targetPort < (r.lift delta).payload.targetArity :=
  target_port_lt (lift_conductive (delta := delta) h)

/-- Binder/scope boundedness survives candidate-record lift when the original
record conducts. -/
theorem lift_scope_sound {delta : ℕ} {r : CandidateContractionRecord} (h : r.Conductive) :
    (r.lift delta).payload.binderDepth ≤ (r.lift delta).payload.scopeDepth :=
  scope_sound (lift_conductive (delta := delta) h)

/-- Local bond-dimension compatibility survives candidate-record lift when the
original record conducts. -/
theorem lift_compatible_of_conductive {delta : ℕ} {r : CandidateContractionRecord}
    (h : r.Conductive) :
    (r.lift delta).payload.sourceBondDim = (r.lift delta).payload.targetBondDim :=
  compatible_of_conductive (lift_conductive (delta := delta) h)

end CandidateContractionRecord

end Tensor
end InfoGeometry
