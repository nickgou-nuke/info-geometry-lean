import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
Projectors associated with an involution.

This file proves only the scalar algebraic statement.  It does not identify an
involution with a split-octonion element, a Clifford generator, or a physical
time direction.
-/

def hyperbolicProjectorPlus {R : Type*} [DivisionRing R] (u : R) : R := (1 / 2 : R) * (1 + u)

def hyperbolicProjectorMinus {R : Type*} [DivisionRing R] (u : R) : R := (1 / 2 : R) * (1 - u)

section Field

variable {R : Type*} [Field R] [CharZero R]

theorem hyperbolicProjectorPlus_idempotent (u : R) (hu : u * u = 1) :
    hyperbolicProjectorPlus u * hyperbolicProjectorPlus u =
      hyperbolicProjectorPlus u := by
  dsimp [hyperbolicProjectorPlus]
  calc
    (1 / 2 : R) * (1 + u) * ((1 / 2 : R) * (1 + u)) =
        (1 / 4 : R) * (1 + 2 * u + u * u) := by ring
    _ = (1 / 4 : R) * (1 + 2 * u + 1) := by rw [hu]
    _ = (1 / 2 : R) * (1 + u) := by ring

theorem hyperbolicProjectorMinus_idempotent (u : R) (hu : u * u = 1) :
    hyperbolicProjectorMinus u * hyperbolicProjectorMinus u =
      hyperbolicProjectorMinus u := by
  dsimp [hyperbolicProjectorMinus]
  calc
    (1 / 2 : R) * (1 - u) * ((1 / 2 : R) * (1 - u)) =
        (1 / 4 : R) * (1 - 2 * u + u * u) := by ring
    _ = (1 / 4 : R) * (1 - 2 * u + 1) := by rw [hu]
    _ = (1 / 2 : R) * (1 - u) := by ring

theorem hyperbolicProjectors_orthogonal (u : R) (hu : u * u = 1) :
    hyperbolicProjectorPlus u * hyperbolicProjectorMinus u = 0 := by
  dsimp [hyperbolicProjectorPlus, hyperbolicProjectorMinus]
  calc
    (1 / 2 : R) * (1 + u) * ((1 / 2 : R) * (1 - u)) =
        (1 / 4 : R) * (1 - u * u) := by ring
    _ = (1 / 4 : R) * (1 - 1) := by rw [hu]
    _ = 0 := by ring

end Field

theorem hyperbolicProjectors_resolve_identity {R : Type*} [DivisionRing R] [CharZero R] (u : R) :
    hyperbolicProjectorPlus u + hyperbolicProjectorMinus u = 1 := by
  dsimp [hyperbolicProjectorPlus, hyperbolicProjectorMinus]
  rw [← mul_add, add_add_sub_cancel, ← two_mul, mul_one, one_div_mul_cancel (NeZero.ne (2 : R))]

theorem hyperbolicProjectors_complete {R : Type*} [Field R] [CharZero R] (u : R) (hu : u * u = 1) :
    (hyperbolicProjectorPlus u * hyperbolicProjectorPlus u =
        hyperbolicProjectorPlus u) ∧
    (hyperbolicProjectorMinus u * hyperbolicProjectorMinus u =
        hyperbolicProjectorMinus u) ∧
    (hyperbolicProjectorPlus u * hyperbolicProjectorMinus u = 0) ∧
    (hyperbolicProjectorPlus u + hyperbolicProjectorMinus u = 1) := by
  exact ⟨hyperbolicProjectorPlus_idempotent u hu,
    hyperbolicProjectorMinus_idempotent u hu,
    hyperbolicProjectors_orthogonal u hu,
    hyperbolicProjectors_resolve_identity u⟩

def hyperbolicInvolutionLocus {R : Type*} [Ring R] : Set R := {u | u * u = 1}

theorem hyperbolicInvolutionLocus_closed {R : Type*} [Ring R] [TopologicalSpace R]
    [ContinuousMul R] [T1Space R] :
    IsClosed (hyperbolicInvolutionLocus (R := R)) := by
  change IsClosed ((fun u : R => u * u) ⁻¹' ({1} : Set R))
  exact isClosed_singleton.preimage (continuous_id.mul continuous_id)

def hyperbolicProjectorReadout {R : Type*} [DivisionRing R] : {u : R // u * u = 1} → R × R :=
  fun u => (hyperbolicProjectorPlus u.1, hyperbolicProjectorMinus u.1)

theorem continuous_hyperbolicProjectorReadout {R : Type*} [DivisionRing R]
    [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R]
    [ContinuousSub R] [ContinuousConstSMul R R] :
    Continuous (hyperbolicProjectorReadout (R := R)) := by
  change Continuous (fun u : {u : R // u * u = 1} =>
    ((1 / 2 : R) * (1 + u.1), (1 / 2 : R) * (1 - u.1)))
  fun_prop

theorem hyperbolicProjectorReadout_spec {R : Type*} [DivisionRing R]
    (u : {u : R // u * u = 1}) :
    hyperbolicProjectorReadout u =
      (hyperbolicProjectorPlus u.1, hyperbolicProjectorMinus u.1) := rfl

end InfoGeometry.Canonical
