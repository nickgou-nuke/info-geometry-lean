import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Canonical.FractalFockEquivalenceBridge
import InfoGeometry.Meta.Architecture

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

namespace InfoGeometry.Canonical.CelikKocakFractalFockBridge

open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Canonical.FractalFockEquivalenceBridge

/-- The paper-facing infinite Cantor/Fock witness lane. -/
@[rep_depth operator]
abbrev CelikKocakPaperWitness
    (Op : Type*) [Ring Op] :=
  CelikKocakInfiniteFockWitness Op

namespace CelikKocakPaperWitness

variable {Op : Type*} [Ring Op]
variable (W : CelikKocakInfiniteFockWitness Op)

/-- Re-export of the Cantor-boundary function-space packet. -/
@[rep_depth operator]
def cantorFunctionSpace : RealDoubledCantorFunctionSpace :=
  W.cantorFunctionSpace

/-- Re-export of the tilt/switch system. -/
@[rep_depth operator]
def tiltSwitchSystem : TiltSwitchSystem Op :=
  W.tiltSwitch

/-- Re-export of the Clifford representation. -/
@[rep_depth operator]
def cliffordRepresentation : RealDoubledCantorCliffordRepresentation Op :=
  W.clifford

/-- The paper's explicit equivalence-to-Fock witness. -/
@[rep_depth operator]
theorem equivalent_to_fock :
    W.equivalentToFock :=
  W.equivalentToFock_witness

/-- Infinite Clifford generators square to one. -/
@[rep_depth operator]
theorem gamma_sq (i : ℕ) :
    W.clifford.gamma i * W.clifford.gamma i = 1 :=
  W.clifford.gamma_sq i

/-- Distinct infinite Clifford generators anticommute. -/
@[rep_depth operator]
theorem gamma_anticomm {i j : ℕ} (hij : i ≠ j) :
    W.clifford.gamma i * W.clifford.gamma j +
      W.clifford.gamma j * W.clifford.gamma i = 0 := by
  rw [W.clifford.gamma_anticomm i j hij]
  simp

end CelikKocakPaperWitness

/--
Paper-facing canonical bridge.

This keeps the existing topology-side witness visible from the canonical
namespace and records the paper's output as a theorem-safe closure target.
-/
@[rep_depth operator]
structure CelikKocakFractalFockBridge
    (Op : Type*) [Ring Op] where
  paperWitness : CelikKocakPaperWitness Op
  fractalFockBridge : FractalFockBridge Op
  paperAndBridgeAgree : Prop
  paperAndBridgeAgree_witness : paperAndBridgeAgree

namespace CelikKocakFractalFockBridge

variable {Op : Type*} [Ring Op]
variable (B : CelikKocakFractalFockBridge Op)

/-- Re-export of the paper witness. -/
@[rep_depth operator]
def paperWitness_readout :
    CelikKocakPaperWitness Op :=
  B.paperWitness

/-- Re-export of the canonical fractal/Fock bridge. -/
@[rep_depth operator]
def canonicalBridge_readout :
    FractalFockBridge Op :=
  B.fractalFockBridge

/-- The paper and canonical bridge agree, as supplied. -/
@[rep_depth operator]
theorem paper_and_bridge_agree :
    B.paperAndBridgeAgree :=
  B.paperAndBridgeAgree_witness

/-- The underlying Fock equivalence witness is available. -/
@[rep_depth operator]
theorem equivalent_to_fock :
    B.paperWitness.equivalentToFock :=
  B.paperWitness.equivalentToFock_witness

end CelikKocakFractalFockBridge

end InfoGeometry.Canonical.CelikKocakFractalFockBridge
