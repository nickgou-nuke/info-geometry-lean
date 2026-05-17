import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Canonical.CelikKocakFractalFockBridge
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge

/-!
# InfoGeometry.Canonical.CelikKocakPaperFormalism

Paper-facing consolidation for the Celik--Koçak fractal Cantor/Fock
representation.

This file does not reconstruct the analytic Cantor `L²` model or prove a new
unitary equivalence.  It packages the existing witness chain as a single
paper-facing owner surface:

* Cantor tilt/switch Clifford representation;
* infinite fractal/Fock equivalence witness;
* combined theorem-safe owner target.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Canonical.CelikKocakFractalFockBridge
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.FractalFockEquivalenceBridge

/-- Paper-facing infinite fractal/Fock witness. -/
@[rep_depth operator]
abbrev PaperWitness (Op : Type*) [Ring Op] := CelikKocakPaperWitness Op

namespace PaperWitness

variable {Op : Type*} [Ring Op]
variable (W : PaperWitness Op)

/-- Re-export of the Cantor-boundary function-space packet. -/
@[rep_depth operator]
def cantorFunctionSpace : RealDoubledCantorFunctionSpace :=
  W.cantorFunctionSpace

/-- Re-export of the tilt/switch system. -/
@[rep_depth operator]
def tiltSwitchSystem : TiltSwitchSystem Op :=
  W.tiltSwitchSystem

/-- Re-export of the Clifford representation. -/
@[rep_depth operator]
def cliffordRepresentation : CantorCliffordRepresentation Op :=
  W.cliffordRepresentation

/-- The paper's explicit equivalence-to-Fock witness. -/
@[rep_depth operator]
theorem equivalent_to_fock :
    W.equivalentToFock :=
  W.equivalent_to_fock

/-- Infinite Clifford generators square to one. -/
@[rep_depth operator]
theorem gamma_sq (i : ℕ) :
    W.cliffordRepresentation.gamma i * W.cliffordRepresentation.gamma i = 1 :=
  W.gamma_sq i

/-- Distinct infinite Clifford generators anticommute. -/
@[rep_depth operator]
theorem gamma_anticomm {i j : ℕ} (hij : i ≠ j) :
    W.cliffordRepresentation.gamma i * W.cliffordRepresentation.gamma j +
      W.cliffordRepresentation.gamma j * W.cliffordRepresentation.gamma i = 0 := by
  rw [W.gamma_anticomm hij]
  simp

end PaperWitness

/--
Paper-facing consolidated owner target.

This is the formalism entry point for the Celik--Koçak Cantor/Fock paper
surface.  It wraps the already-owned Clifford/Fock chain rather than
reconstructing the analytic model again.
-/
@[owner_target_tag]
structure CelikKocakPaperFormalismOwnerTarget
    (Op H : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] where
  core : FractalCantorCliffordFockOwnerTarget Op H

/-- The paper-facing formalism owner target follows from the existing core chain. -/
@[rep_depth operator]
theorem celikKocakPaperFormalismOwnerTarget
    (Op H : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] :
    CelikKocakPaperFormalismOwnerTarget Op H := by
  refine ⟨fractalCantorCliffordFockOwnerTarget Op H⟩

end InfoGeometry.Canonical.CelikKocakPaperFormalism
