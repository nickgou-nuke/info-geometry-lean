import Mathlib
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Canonical.CelikKocakFractalFockBridge
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge

/-!
# InfoGeometry.Canonical.CelikKocakPaperFormalism

Paper-facing consolidation for the Celik--Koçak fractal Cantor/Fock
representation.

This file does not reconstruct the analytic Cantor `L²` model or prove a new
unitary equivalence. It packages the existing witness chain as a single
paper-facing owner surface.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

/-- Paper-facing infinite fractal/Fock witness. -/
abbrev PaperWitness (Op : Type*) [Ring Op] :=
  CelikKocakInfiniteFockWitness Op

/-- Re-export of the Cantor-boundary function-space packet. -/
def paperCantorFunctionSpace {Op : Type*} [Ring Op]
    (W : PaperWitness Op) : RealDoubledCantorFunctionSpace :=
  W.cantorFunctionSpace

/-- Re-export of the tilt/switch system. -/
def paperTiltSwitchSystem {Op : Type*} [Ring Op]
    (W : PaperWitness Op) : TiltSwitchSystem Op :=
  W.tiltSwitch

/-- Re-export of the Clifford representation. -/
def paperCliffordRepresentation {Op : Type*} [Ring Op]
    (W : PaperWitness Op) : RealDoubledCantorCliffordRepresentation Op :=
  W.clifford

/-- The paper's explicit equivalence-to-Fock witness. -/
theorem paper_equivalent_to_fock {Op : Type*} [Ring Op]
    (W : PaperWitness Op) : W.equivalentToFock :=
  W.equivalentToFock_witness

/-- Infinite Clifford generators square to one. -/
theorem paper_gamma_sq {Op : Type*} [Ring Op]
    (W : PaperWitness Op) (i : ℕ) :
    (paperCliffordRepresentation W).gamma i *
      (paperCliffordRepresentation W).gamma i = 1 := by
  simpa [paperCliffordRepresentation] using W.clifford.gamma_sq i

/-- Distinct infinite Clifford generators anticommute. -/
theorem paper_gamma_anticomm {Op : Type*} [Ring Op]
    (W : PaperWitness Op) {i j : ℕ} (hij : i ≠ j) :
    (paperCliffordRepresentation W).gamma i *
        (paperCliffordRepresentation W).gamma j +
      (paperCliffordRepresentation W).gamma j *
        (paperCliffordRepresentation W).gamma i = 0 := by
  have h := W.clifford.gamma_anticomm i j hij
  simpa [paperCliffordRepresentation, eq_neg_iff_add_eq_zero] using h

/--
Paper-facing consolidated owner target.

This is the formalism entry point for the Celik--Koçak Cantor/Fock paper
surface. It wraps the already-owned Clifford/Fock chain rather than
reconstructing the analytic model again.
-/
@[owner_target_tag]
structure CelikKocakPaperFormalismOwnerTarget
    (Op H : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] where
  core : FractalCantorCliffordFockOwnerTarget Op H

/-- The paper-facing formalism owner target follows from the existing core chain. -/
theorem celikKocakPaperFormalismOwnerTarget
    (Op H : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] :
    CelikKocakPaperFormalismOwnerTarget Op H := by
  refine ⟨fractalCantorCliffordFockOwnerTarget Op H⟩

end InfoGeometry.Canonical.CelikKocakPaperFormalism
