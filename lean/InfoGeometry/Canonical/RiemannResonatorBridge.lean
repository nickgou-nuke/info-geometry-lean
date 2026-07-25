import InfoGeometry.Meta.Architecture
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.RiemannResonatorBridge

Finite real-linear resonator bridge for the Mellin/Vandermonde lane.

This file stays in the repo's real-linear operator language:

* the deformation is a real-linear rotor operator `qRotor`,
* `qVandermondeTensor` is a finite matrix of real-linear operators,
* `thermalBerryConnectionShadow` is defined by a supercharge commutator,
* `thermalHolonomyShadow` is the rotor operator itself,
* phase lock is the trivial-holonomy condition `thermalHolonomyShadow = Id`.

This file does **not** prove any theorem about Riemann zeros, KMS contour
integrals, or Bost-Connes dynamics. It is the honest real-linear rotor bridge.
-/

namespace InfoGeometry.Canonical.RiemannResonatorBridge

open Matrix

section RotorShadow

variable {E : Type _} [AddCommGroup E] [Module ℝ E]

/-- Finite resonator data with commuting supercharge lanes. -/
@[rep_depth operator]
structure ResonatorShadowData (n : ℕ) where
  phaseAngle : ℝ
  nodes : Fin n → ℝ
  qRotor : E →ₗ[ℝ] E
  phase_zero_trivial : phaseAngle = 0 → qRotor = LinearMap.id
  leftSupercharge : Matrix (Fin n) (Fin n) (E →ₗ[ℝ] E)
  rightSupercharge : Matrix (Fin n) (Fin n) (E →ₗ[ℝ] E)
  supercharges_commute :
    leftSupercharge * rightSupercharge = rightSupercharge * leftSupercharge

namespace ResonatorShadowData

variable {n : ℕ} (R : ResonatorShadowData (E := E) n)

/-- Finite rotor-valued `q`-deformed Vandermonde tensor. -/
@[rep_depth operator]
def qVandermondeTensor : Matrix (Fin n) (Fin n) (E →ₗ[ℝ] E) :=
  fun i j =>
    ((R.nodes j) ^ (i : ℕ)) • R.qRotor

/--
Commutator-defined Berry connection shadow on the real-linear lane.
-/
@[rep_depth operator]
def thermalBerryConnectionShadow : Matrix (Fin n) (Fin n) (E →ₗ[ℝ] E) :=
  R.leftSupercharge * R.rightSupercharge - R.rightSupercharge * R.leftSupercharge

/-- The commutator-defined Berry shadow vanishes on the commuting slice. -/
@[rep_depth operator]
theorem thermalBerryConnectionShadow_eq_zero :
    R.thermalBerryConnectionShadow = 0 := by
  unfold thermalBerryConnectionShadow
  rw [R.supercharges_commute]
  simp

/-- Finite thermal holonomy shadow on the real-linear lane. -/
@[rep_depth operator]
def thermalHolonomyShadow : E →ₗ[ℝ] E := R.qRotor

/-- Phase lock is trivial holonomy in the real-linear lane. -/
@[rep_depth operator]
def PhaseLocked : Prop :=
  R.thermalHolonomyShadow = LinearMap.id

/-- Zero phase gives trivial holonomy. -/
@[rep_depth operator]
theorem thermalHolonomyShadow_eq_id_of_phaseAngle_zero
    (hθ : R.phaseAngle = 0) :
    R.thermalHolonomyShadow = LinearMap.id := by
  unfold thermalHolonomyShadow
  exact R.phase_zero_trivial hθ

/-- Phase lock implies trivial holonomy by definition. -/
@[rep_depth operator]
theorem phase_locked_holonomy_eq_id
    (hLock : R.PhaseLocked) :
    R.thermalHolonomyShadow = LinearMap.id := hLock

/--
Combined finite resonator packet: commuting supercharges give a flat Berry
shadow, and phase lock gives trivial holonomy.
-/
@[rep_depth operator]
theorem resonator_shadow_packet
    (hLock : R.PhaseLocked) :
    R.thermalBerryConnectionShadow = 0
      ∧ R.thermalHolonomyShadow = LinearMap.id := by
  exact ⟨R.thermalBerryConnectionShadow_eq_zero, R.phase_locked_holonomy_eq_id hLock⟩

end ResonatorShadowData

end RotorShadow

end InfoGeometry.Canonical.RiemannResonatorBridge
