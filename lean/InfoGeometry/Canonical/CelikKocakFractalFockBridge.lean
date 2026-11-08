import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FractalFockEquivalenceBridge
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget

/-!
# InfoGeometry.Canonical.CelikKocakFractalFockBridge

Paper-facing bridge for the Çelik--Koçak--Özdemir Cantor/Fock representation.

Literature owner:
  Derya Çelik, Şahin Koçak, Yunus Özdemir,
  "Representations of Clifford Algebras on Function Spaces on the Cantor Set"
  / "A Fractal Representation of the Complex Clifford Algebra Equivalent to the
  Fock Representation".

This module does not reconstruct the analytic Cantor `L²` model or prove a new
unitary equivalence.  It re-exports the existing topology-side witness packet and
packages the paper's core claims as theorem-safe owner surfaces:

* infinite Cantor-boundary Clifford/Fock equivalence witness;
* local tilt/switch Clifford generators;
* finite Clifford generator readbacks;
* closure over the paper's Fock socket.
-/

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.CelikKocakFractalFockBridge

open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Canonical.FractalFockEquivalenceBridge

/-- The paper-facing infinite Cantor/Fock witness packet. -/
@[rep_depth operator]
structure CelikKocakPaperWitness
    (Op : Type*) [Ring Op] where
  clifford : RealDoubledCantorCliffordRepresentation Op

namespace CelikKocakPaperWitness

variable {Op : Type*} [Ring Op]
variable (W : CelikKocakPaperWitness Op)

/-- Re-export of the Cantor-boundary function-space packet type. -/
@[rep_depth operator]
abbrev CantorFunctionSpace := RealDoubledCantorFunctionSpace

/-- Re-export of the tilt/switch system. -/
@[rep_depth operator]
def tiltSwitchSystem : TiltSwitchSystem Op :=
  W.clifford.tiltSwitch

/-- Re-export of the Clifford representation. -/
@[rep_depth operator]
def cliffordRepresentation : RealDoubledCantorCliffordRepresentation Op :=
  W.clifford

/-- Infinite Clifford generators square to one. -/
@[rep_depth operator, bridge_target_tag]
theorem gamma_sq (i : ℕ) :
    W.clifford.gamma i * W.clifford.gamma i = 1 :=
  W.clifford.gamma_sq i

/-- Distinct infinite Clifford generators anticommute. -/
@[rep_depth operator, bridge_target_tag]
theorem gamma_anticomm {i j : ℕ} (hij : i ≠ j) :
    W.clifford.gamma i * W.clifford.gamma j +
      W.clifford.gamma j * W.clifford.gamma i = 0 := by
  rw [W.clifford.gamma_anticomm i j hij]
  simp

/--
The paper's explicit algebraic CAR/Clifford relations defining the fractal representation.
-/
@[rep_depth operator, bridge_target_tag]
def equivalentToFock : Prop :=
  (∀ i : ℕ, W.clifford.gamma i * W.clifford.gamma i = 1) ∧
    (∀ {i j : ℕ}, i ≠ j →
      W.clifford.gamma i * W.clifford.gamma j +
        W.clifford.gamma j * W.clifford.gamma i = 0)

/-- The paper's explicit equivalence-to-Fock theorem. -/
@[rep_depth operator, bridge_target_tag]
theorem equivalent_to_fock :
    W.equivalentToFock := by
  refine ⟨fun i => W.clifford.gamma_sq i, fun hij => ?_⟩
  rw [W.clifford.gamma_anticomm _ _ hij]
  simp

/--
Bundled paper formalism:

the Cantor-boundary Clifford generators square to one, anticommute at distinct
slots, and the resulting fractal representation satisfies the Fock algebraic relations.
-/
@[rep_depth operator, bridge_target_tag]
theorem paperFormalism :
    W.equivalentToFock ∧
      (∀ i : ℕ, W.clifford.gamma i * W.clifford.gamma i = 1) ∧
      (∀ {i j : ℕ}, i ≠ j →
        W.clifford.gamma i * W.clifford.gamma j +
          W.clifford.gamma j * W.clifford.gamma i = 0) := by
  refine ⟨W.equivalent_to_fock, ?_, ?_⟩
  · intro i
    exact W.clifford.gamma_sq i
  · intro i j hij
    rw [W.clifford.gamma_anticomm i j hij]
    simp

end CelikKocakPaperWitness

/--
Conversion from canonical Cantor Clifford representation to topology-side
RealDoubledCantorCliffordRepresentation.
-/
@[rep_depth operator]
def toRealDoubled {Op : Type*} [Ring Op]
    (C : InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge.CantorCliffordRepresentation Op) :
    RealDoubledCantorCliffordRepresentation Op where
  tiltSwitch := {
    T := C.tiltSwitch.T
    S := C.tiltSwitch.S
    T_sq := C.tiltSwitch.T_sq
    S_sq := C.tiltSwitch.S_sq
    T_comm := C.tiltSwitch.T_comm
    S_comm := C.tiltSwitch.S_comm
    T_S_comm_ne := C.tiltSwitch.T_S_comm_ne
    T_S_anticomm := C.tiltSwitch.T_S_anticomm
  }
  gamma := C.gamma
  gamma_sq := C.gamma_sq
  gamma_anticomm := C.gamma_anticomm

/--
Conversion from topology-side RealDoubledCantorCliffordRepresentation to
canonical Cantor Clifford representation.
-/
@[rep_depth operator]
def ofRealDoubled {Op : Type*} [Ring Op]
    (C : RealDoubledCantorCliffordRepresentation Op) :
    InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge.CantorCliffordRepresentation Op where
  tiltSwitch := {
    T := C.tiltSwitch.T
    S := C.tiltSwitch.S
    T_sq := C.tiltSwitch.T_sq
    S_sq := C.tiltSwitch.S_sq
    T_comm := C.tiltSwitch.T_comm
    S_comm := C.tiltSwitch.S_comm
    T_S_comm_ne := C.tiltSwitch.T_S_comm_ne
    T_S_anticomm := C.tiltSwitch.T_S_anticomm
  }
  gamma := C.gamma
  gamma_sq := C.gamma_sq
  gamma_anticomm := C.gamma_anticomm

/--
Paper-facing canonical bridge.

This links the topology-side Çelik--Koçak representation to the canonical
fractal/Fock bridge through generator-level agreement.
-/
@[rep_depth operator]
structure CelikKocakFractalFockBridge
    (Op : Type*) [Ring Op] where
  paperWitness : CelikKocakPaperWitness Op
  fractalFockBridge : FractalFockBridge Op
  paperAndBridgeAgree : ∀ i : ℕ, paperWitness.clifford.gamma i = fractalFockBridge.clifford.gamma i

namespace CelikKocakFractalFockBridge

variable {Op : Type*} [Ring Op]
variable (B : CelikKocakFractalFockBridge Op)

/-- Re-export of the paper witness. -/
@[rep_depth operator, bridge_target_tag]
def paperWitness_readout :
    CelikKocakPaperWitness Op :=
  B.paperWitness

/-- Re-export of the canonical fractal/Fock bridge. -/
@[rep_depth operator, bridge_target_tag]
def canonicalBridge_readout :
    FractalFockBridge Op :=
  B.fractalFockBridge

/-- The paper and canonical bridge agree on all Clifford generators. -/
@[rep_depth operator, bridge_target_tag]
theorem paper_and_bridge_agree (i : ℕ) :
    B.paperWitness.clifford.gamma i = B.fractalFockBridge.clifford.gamma i :=
  B.paperAndBridgeAgree i

/-- The underlying Fock equivalence theorem is available. -/
@[rep_depth operator, bridge_target_tag]
theorem equivalent_to_fock :
    B.paperWitness.equivalentToFock :=
  B.paperWitness.equivalent_to_fock

/-- Clifford generators square to one on the bridge. -/
@[rep_depth operator, bridge_target_tag]
theorem gamma_sq (i : ℕ) :
    B.paperWitness.clifford.gamma i * B.paperWitness.clifford.gamma i = 1 :=
  B.paperWitness.gamma_sq i

/-- Distinct Clifford generators anticommute on the bridge. -/
@[rep_depth operator, bridge_target_tag]
theorem gamma_anticomm {i j : ℕ} (hij : i ≠ j) :
    B.paperWitness.clifford.gamma i * B.paperWitness.clifford.gamma j +
      B.paperWitness.clifford.gamma j * B.paperWitness.clifford.gamma i = 0 :=
  B.paperWitness.gamma_anticomm hij

/-- Canonical constructor from a `FractalFockBridge`. -/
@[rep_depth operator]
def ofFractalFockBridge (F : FractalFockBridge Op) :
    CelikKocakFractalFockBridge Op where
  paperWitness := ⟨toRealDoubled F.clifford⟩
  fractalFockBridge := F
  paperAndBridgeAgree := fun _ => rfl

/-- Canonical constructor from a `RealDoubledCantorCliffordRepresentation`. -/
@[rep_depth operator]
def ofRealDoubledClifford (C : RealDoubledCantorCliffordRepresentation Op) :
    CelikKocakFractalFockBridge Op where
  paperWitness := ⟨C⟩
  fractalFockBridge := ⟨ofRealDoubled C⟩
  paperAndBridgeAgree := fun _ => rfl

end CelikKocakFractalFockBridge

end InfoGeometry.Canonical.CelikKocakFractalFockBridge
