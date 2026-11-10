/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Geometric-algebra rotor substrate for braid interfaces

This file records only a Clifford/geometric-algebra substrate interface.  It is
not a formalization of Fibonacci anyon braiding, and it does not prove an Artin
braid representation.

#### BUCKET 1: CLOSED FINITE THEOREMS

`rotor_substrate_readout`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The readout is conditional on an explicitly supplied Clifford anti-commutator
identity.

#### BUCKET 3: OPEN CLOSURE DEBT

Deriving the anti-commutator from quadratic-form orthogonality and connecting
the resulting rotors to Fibonacci F/R matrices remain open here.
-/

namespace InfoGeometry.Algebra.AnyonBraidGA

open CliffordAlgebra
open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingRotorSubstrate

variable {B : Type*} [Ring B]

/-- Two elements in a non-commutative ring `[Ring B]` anticommute when `u * v + v * u = 0`. -/
def RingVectorAnticommutes (u v : B) : Prop :=
  u * v + v * u = 0

/-- In any non-commutative ring `[Ring B]`, if `u` and `v` anticommute (`u * v + v * u = 0`),
their bivector product `u * v` satisfies `(u * v) * (u * v) = - (u * u * (v * v))`. -/
theorem bivector_sq_of_anticommute_ring {u v : B} (h : RingVectorAnticommutes u v) :
    (u * v) * (u * v) = - (u * u * (v * v)) := by
  have huv : v * u = - (u * v) := eq_neg_of_add_eq_zero_right h
  calc
    (u * v) * (u * v) = u * (v * u) * v := by noncomm_ring
    _ = u * (- (u * v)) * v := by rw [huv]
    _ = - (u * u * (v * v)) := by noncomm_ring

/-- In any non-commutative ring `[Ring B]`, if `u * u = 1`, `v * v = 1`, and `u` and `v`
anticommute (`u * v + v * u = 0`), then the bivector `u * v` squares to `-1`. -/
theorem bivector_sq_neg_one_of_orthonormal_ring {u v : B}
    (hu : u * u = 1) (hv : v * v = 1) (h : RingVectorAnticommutes u v) :
    (u * v) * (u * v) = -1 := by
  rw [bivector_sq_of_anticommute_ring h, hu, hv, mul_one]

end NonCommRingRotorSubstrate

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- Clifford anti-commutator for two vectors in the chosen quadratic space. -/
def CliffordVectorAnticommutes (u v : M) : Prop :=
  (ι Q u) * (ι Q v) + (ι Q v) * (ι Q u) = 0

/-- Orthogonality implies Clifford anti-commutation. -/
theorem CliffordVectorAnticommutes_of_isOrtho {u v : M} (h : Q.IsOrtho u v) :
    CliffordVectorAnticommutes Q u v := by
  dsimp [CliffordVectorAnticommutes]
  simpa using (CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho (Q := Q) (a := u) (b := v) h)

/--
Geometric-algebra substrate readout.

This now has a genuine finite logical witness: the anti-commutator vanishes
whenever the vectors are orthogonal for the chosen quadratic form.
-/
theorem rotor_substrate_readout_of_isOrtho (u v : M)
    (h : Q.IsOrtho u v) :
    (ι Q u) * (ι Q v) + (ι Q v) * (ι Q u) = 0 := by
  simpa [CliffordVectorAnticommutes] using
    (CliffordVectorAnticommutes_of_isOrtho (Q := Q) (u := u) (v := v) h)

end InfoGeometry.Algebra.AnyonBraidGA
