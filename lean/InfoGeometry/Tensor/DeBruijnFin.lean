import InfoGeometry.Tensor.DeBruijnPorts
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry
namespace Tensor

/-!
# De Bruijn finite-index readbacks

This module roots local tensor-port coordinates in Mathlib's `Fin`.  The existing
`TensorPort` wrapper is read back to `Fin p.arity`, and `Fin n` values build
bounded ports without introducing a new proof authority layer.
-/

namespace TensorPort

/-- Read a bounded tensor port as the corresponding Mathlib finite index. -/
def toFin (p : TensorPort) : Fin p.arity :=
  ⟨p.index, p.inBounds⟩

/-- Build a tensor port directly from a Mathlib finite index. -/
def ofFin {arity : ℕ} (i : Fin arity) : TensorPort where
  arity := arity
  index := i.val
  inBounds := i.isLt

@[simp] theorem toFin_val (p : TensorPort) : p.toFin.val = p.index :=
  rfl

@[simp] theorem toFin_isLt (p : TensorPort) : p.toFin.isLt = p.inBounds :=
  rfl

@[simp] theorem ofFin_arity {arity : ℕ} (i : Fin arity) : (ofFin i).arity = arity :=
  rfl

@[simp] theorem ofFin_index {arity : ℕ} (i : Fin arity) : (ofFin i).index = i.val :=
  rfl

@[simp] theorem ofFin_inBounds {arity : ℕ} (i : Fin arity) : (ofFin i).inBounds = i.isLt :=
  rfl

@[simp] theorem toFin_ofFin {arity : ℕ} (i : Fin arity) : (ofFin i).toFin = i := by
  cases i
  rfl

/-- Round-trip from `TensorPort` to `Fin` and back preserves all data fields. -/
@[simp] theorem ofFin_toFin (p : TensorPort) : ofFin p.toFin = p := by
  cases p
  rfl

@[simp] theorem rawIndex_eq_toFin_val (p : TensorPort) : p.rawIndex = p.toFin.val :=
  rfl

end TensorPort

namespace DeBruijnEdge

/-- Build an edge from Mathlib finite source and target ports. -/
def ofFinPorts {sourceArity targetArity : ℕ} (source : Fin sourceArity)
    (target : Fin targetArity) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    DeBruijnEdge :=
  ofPorts (TensorPort.ofFin source) (TensorPort.ofFin target) binderDepth scopeDepth
    sourceBondDim targetBondDim

@[simp] theorem ofFinPorts_sourceArity {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).sourceArity =
      sourceArity :=
  rfl

@[simp] theorem ofFinPorts_targetArity {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).targetArity =
      targetArity :=
  rfl

@[simp] theorem ofFinPorts_sourcePort {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).sourcePort =
      source.val :=
  rfl

@[simp] theorem ofFinPorts_targetPort {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).targetPort =
      target.val :=
  rfl

/-- Fin-built edge scope reduces to the binder/scope inequality. -/
theorem ofFinPorts_inScope_iff {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).InScope ↔
      binderDepth ≤ scopeDepth := by
  simpa [ofFinPorts] using
    ofPorts_inScope_iff (TensorPort.ofFin source) (TensorPort.ofFin target) binderDepth
      scopeDepth sourceBondDim targetBondDim

/-- Fin-built edge compatibility reduces to bond-dimension equality. -/
theorem ofFinPorts_portCompatible_iff {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).PortCompatible ↔
      sourceBondDim = targetBondDim := by
  rfl

/-- Fin-built edge soundness is exactly binder/scope boundedness and local bond compatibility. -/
theorem ofFinPorts_contractionSound_iff {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).ContractionSound ↔
      binderDepth ≤ scopeDepth ∧ sourceBondDim = targetBondDim := by
  simpa [ContractionSound] using
    and_congr (ofFinPorts_inScope_iff source target binderDepth scopeDepth sourceBondDim
      targetBondDim) (ofFinPorts_portCompatible_iff source target binderDepth scopeDepth
      sourceBondDim targetBondDim)

/-- Direct constructor for soundness of an edge built from Mathlib finite ports. -/
theorem ofFinPorts_contractionSound {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    {binderDepth scopeDepth sourceBondDim targetBondDim : ℕ}
    (hscope : binderDepth ≤ scopeDepth) (hcompat : sourceBondDim = targetBondDim) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).ContractionSound :=
  (ofFinPorts_contractionSound_iff source target binderDepth scopeDepth sourceBondDim
    targetBondDim).2 ⟨hscope, hcompat⟩

end DeBruijnEdge

namespace DeBruijnPayload

/-- Build an endpoint-free payload from Mathlib finite source and target ports. -/
def ofFinPorts {sourceArity targetArity : ℕ} (source : Fin sourceArity)
    (target : Fin targetArity) (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    DeBruijnPayload :=
  ofPorts (TensorPort.ofFin source) (TensorPort.ofFin target) binderDepth scopeDepth
    sourceBondDim targetBondDim

@[simp] theorem ofFinPorts_sourceArity {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).sourceArity =
      sourceArity :=
  rfl

@[simp] theorem ofFinPorts_targetArity {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).targetArity =
      targetArity :=
  rfl

@[simp] theorem ofFinPorts_sourcePort {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).sourcePort =
      source.val :=
  rfl

@[simp] theorem ofFinPorts_targetPort {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).targetPort =
      target.val :=
  rfl

/-- Payload construction from finite ports reads back to the lower edge construction. -/
@[simp] theorem toEdge_ofFinPorts {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).toEdge =
      DeBruijnEdge.ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim :=
  rfl

/-- Fin-built payload scope reduces to the binder/scope inequality. -/
theorem ofFinPorts_inScope_iff {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).InScope ↔
      binderDepth ≤ scopeDepth := by
  simpa [ofFinPorts] using
    ofPorts_inScope_iff (TensorPort.ofFin source) (TensorPort.ofFin target) binderDepth
      scopeDepth sourceBondDim targetBondDim

/-- Fin-built payload compatibility reduces to bond-dimension equality. -/
theorem ofFinPorts_portCompatible_iff {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).PortCompatible ↔
      sourceBondDim = targetBondDim := by
  rfl

/-- Fin-built payload conductivity is exactly binder/scope boundedness and bond compatibility. -/
theorem ofFinPorts_conductive_iff {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).Conductive ↔
      binderDepth ≤ scopeDepth ∧ sourceBondDim = targetBondDim := by
  simpa [Conductive] using
    DeBruijnEdge.ofFinPorts_contractionSound_iff source target binderDepth scopeDepth
      sourceBondDim targetBondDim

/-- Direct conductivity constructor for payloads built from Mathlib finite ports. -/
theorem ofFinPorts_conductive {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    {binderDepth scopeDepth sourceBondDim targetBondDim : ℕ}
    (hscope : binderDepth ≤ scopeDepth) (hcompat : sourceBondDim = targetBondDim) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).Conductive :=
  (ofFinPorts_conductive_iff source target binderDepth scopeDepth sourceBondDim
    targetBondDim).2 ⟨hscope, hcompat⟩

/-- Lifting a Fin-built payload equals rebuilding from the same finite ports with lifted depths. -/
theorem lift_ofFinPorts (delta : ℕ) {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts source target binderDepth scopeDepth sourceBondDim targetBondDim).lift delta =
      ofFinPorts source target (binderDepth + delta) (scopeDepth + delta) sourceBondDim
        targetBondDim :=
  rfl

end DeBruijnPayload

namespace CandidateContractionRecord

/-- Build a candidate record from graph endpoints and Mathlib finite source/target ports. -/
def ofFinPorts (endpoints : GraphEndpoints) {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) : CandidateContractionRecord :=
  ofPorts endpoints (TensorPort.ofFin source) (TensorPort.ofFin target) binderDepth scopeDepth
    sourceBondDim targetBondDim

@[simp] theorem ofFinPorts_endpoints (endpoints : GraphEndpoints) {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts endpoints source target binderDepth scopeDepth sourceBondDim targetBondDim).endpoints =
      endpoints :=
  rfl

@[simp] theorem ofFinPorts_payload (endpoints : GraphEndpoints) {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts endpoints source target binderDepth scopeDepth sourceBondDim targetBondDim).payload =
      DeBruijnPayload.ofFinPorts source target binderDepth scopeDepth sourceBondDim
        targetBondDim :=
  rfl

/-- Candidate records built from finite ports conduct exactly when the remaining
scope and compatibility conditions hold. -/
theorem ofFinPorts_conductive_iff (endpoints : GraphEndpoints) {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts endpoints source target binderDepth scopeDepth sourceBondDim targetBondDim).Conductive ↔
      binderDepth ≤ scopeDepth ∧ sourceBondDim = targetBondDim :=
  DeBruijnPayload.ofFinPorts_conductive_iff source target binderDepth scopeDepth sourceBondDim
    targetBondDim

/-- Direct conductivity constructor for candidate records built from finite ports. -/
theorem ofFinPorts_conductive (endpoints : GraphEndpoints) {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    {binderDepth scopeDepth sourceBondDim targetBondDim : ℕ}
    (hscope : binderDepth ≤ scopeDepth) (hcompat : sourceBondDim = targetBondDim) :
    (ofFinPorts endpoints source target binderDepth scopeDepth sourceBondDim targetBondDim).Conductive :=
  (ofFinPorts_conductive_iff endpoints source target binderDepth scopeDepth sourceBondDim
    targetBondDim).2 ⟨hscope, hcompat⟩

/-- Lifting a Fin-built candidate record preserves endpoints and rebuilds its payload
from the same finite ports with lifted depths. -/
theorem lift_ofFinPorts (delta : ℕ) (endpoints : GraphEndpoints) {sourceArity targetArity : ℕ}
    (source : Fin sourceArity) (target : Fin targetArity)
    (binderDepth scopeDepth sourceBondDim targetBondDim : ℕ) :
    (ofFinPorts endpoints source target binderDepth scopeDepth sourceBondDim targetBondDim).lift delta =
      ofFinPorts endpoints source target (binderDepth + delta) (scopeDepth + delta)
        sourceBondDim targetBondDim :=
  rfl

end CandidateContractionRecord

end Tensor
end InfoGeometry
