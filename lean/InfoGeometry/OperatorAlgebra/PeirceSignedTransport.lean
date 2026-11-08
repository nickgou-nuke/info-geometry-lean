/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SignedBoundaryTransport
import InfoGeometry.OperatorAlgebra.PeirceBoundaryDynamics

/-! # Peirce support, reflection, and nonscalar double commutators

The symmetric and signed transports exchange diagonal corners, erase the odd
input, and have even output. Left reflection exchanges their signs; reflection
of the input introduces an additional minus. No diagonal basis is chosen.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.IdempotentCartan

variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

section Peirce
variable {p : A} (hp : p*p=p)
include hp

/-- Left grading converts the symmetric transfer to the signed transfer. -/
theorem reflection_crossTransport (a b : A) :
    LinearMap.mulLeft R (reflection p) *
        crossTransport R (component10 p a) (component01 p b) =
      skewTransport R (component10 p a) (component01 p b) := by
  ext x
  change reflection p *
    (component10 p a*x*component01 p b+component01 p b*x*component10 p a) =
    component10 p a*x*component01 p b-component01 p b*x*component10 p a
  simp only [reflection, two_nsmul, component10, component01, complementIdempotent]
  noncomm_ring [hp, idempotent_mul_nested p hp]

/-- The opposite direction uses the involution law of the existing reflection. -/
theorem reflection_skewTransport (a b : A) :
    LinearMap.mulLeft R (reflection p) *
        skewTransport R (component10 p a) (component01 p b) =
      crossTransport R (component10 p a) (component01 p b) := by
  ext x
  have h := congrArg (fun f : Module.End R A => f x) (reflection_crossTransport R hp a b)
  change reflection p * crossTransport R (component10 p a) (component01 p b) x =
    skewTransport R (component10 p a) (component01 p b) x at h
  change reflection p * skewTransport R (component10 p a) (component01 p b) x = _
  rw [← h, ← mul_assoc, reflection_sq hp, one_mul]

/-- Grading the input changes the sign, rather than reproducing the output law. -/
theorem crossTransport_reflection (a b : A) :
    crossTransport R (component10 p a) (component01 p b) *
        LinearMap.mulLeft R (reflection p) =
      -skewTransport R (component10 p a) (component01 p b) := by
  ext x
  change component10 p a*(reflection p*x)*component01 p b+
    component01 p b*(reflection p*x)*component10 p a =
    -(component10 p a*x*component01 p b-component01 p b*x*component10 p a)
  simp only [reflection, two_nsmul, component10, component01, complementIdempotent]
  noncomm_ring [hp, idempotent_mul_nested p hp]

theorem skewTransport_reflection (a b : A) :
    skewTransport R (component10 p a) (component01 p b) *
        LinearMap.mulLeft R (reflection p) =
      -crossTransport R (component10 p a) (component01 p b) := by
  ext x
  change component10 p a*(reflection p*x)*component01 p b-
    component01 p b*(reflection p*x)*component10 p a =
    -(component10 p a*x*component01 p b+component01 p b*x*component10 p a)
  simp only [reflection, two_nsmul, component10, component01, complementIdempotent]
  noncomm_ring [hp, idempotent_mul_nested p hp]

/-- Exact first output corner, with arbitrary independent arrows. -/
theorem crossTransport_component11 (a b x : A) :
    component11 p (crossTransport R (component10 p a) (component01 p b) x) =
      component10 p a*x*component01 p b := by
  simp only [component11, crossTransport_apply, component10, component01, complementIdempotent]
  noncomm_ring [hp, idempotent_mul_nested p hp]

theorem crossTransport_component00 (a b x : A) :
    component00 p (crossTransport R (component10 p a) (component01 p b) x) =
      component01 p b*x*component10 p a := by
  simp only [component00, crossTransport_apply, component10, component01, complementIdempotent]
  noncomm_ring [hp, idempotent_mul_nested p hp]

theorem crossTransport_even_output (a b x : A) :
    evenPart p (crossTransport R (component10 p a) (component01 p b) x) =
      crossTransport R (component10 p a) (component01 p b) x := by
  unfold evenPart
  rw [crossTransport_component11 R hp, crossTransport_component00 R hp]
  rfl

theorem skewTransport_even_output (a b x : A) :
    evenPart p (skewTransport R (component10 p a) (component01 p b) x) =
      skewTransport R (component10 p a) (component01 p b) x := by
  simp only [evenPart, component11, component00, skewTransport_apply,
    component10, component01, complementIdempotent]
  noncomm_ring [hp, idempotent_mul_nested p hp]

/-- Odd input is annihilated, not transported into another odd channel. -/
theorem crossTransport_odd_input (a b x : A) :
    crossTransport R (component10 p a) (component01 p b) (oddPart p x) = 0 := by
  simp only [crossTransport_apply, oddPart, component10, component01, complementIdempotent]
  noncomm_ring [hp, idempotent_mul_nested p hp]

theorem skewTransport_odd_input (a b x : A) :
    skewTransport R (component10 p a) (component01 p b) (oddPart p x) = 0 := by
  simp only [skewTransport_apply, oddPart, component10, component01, complementIdempotent]
  noncomm_ring [hp, idempotent_mul_nested p hp]

/-- The symmetric transport factors through the existing even projection. -/
theorem crossTransport_even_input (a b x : A) :
    crossTransport R (component10 p a) (component01 p b) (evenPart p x) =
      crossTransport R (component10 p a) (component01 p b) x := by
  have h := congrArg (crossTransport R (component10 p a) (component01 p b))
    (even_add_odd p x)
  simpa only [map_add, crossTransport_odd_input R hp, add_zero] using h

theorem skewTransport_even_input (a b x : A) :
    skewTransport R (component10 p a) (component01 p b) (evenPart p x) =
      skewTransport R (component10 p a) (component01 p b) x := by
  have h := congrArg (skewTransport R (component10 p a) (component01 p b))
    (even_add_odd p x)
  simpa only [map_add, skewTransport_odd_input R hp, add_zero] using h

end Peirce

section DoubleCommutator
variable {q r : A} (hq : q*q=0) (hr : r*r=0)
include hq hr

/-- The second commutator retains the square of the full operator weight. -/
theorem pair_double_commutator_sum :
    lieOp R (q*r-r*q) (lieOp R (q*r-r*q) (q+r)) =
      (4 : ℕ) • ((q*r+r*q)*(q*r+r*q)*(q+r)) := by
  rw [pair_commutator_on_sum R hq hr, map_nsmul, lieOp_mul]
  have hm : lieOp R (q*r-r*q) (q*r+r*q)=0 := by
    rw [lieOp_apply, ← pair_quadratic_commute hq hr, sub_self]
  rw [hm, zero_mul, zero_add, pair_commutator_on_difference R hq hr]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

theorem pair_double_commutator_difference :
    lieOp R (q*r-r*q) (lieOp R (q*r-r*q) (q-r)) =
      (4 : ℕ) • ((q*r+r*q)*(q*r+r*q)*(q-r)) := by
  rw [pair_commutator_on_difference R hq hr, map_nsmul, lieOp_mul]
  have hm : lieOp R (q*r-r*q) (q*r+r*q)=0 := by
    rw [lieOp_apply, ← pair_quadratic_commute hq hr, sub_self]
  rw [hm, zero_mul, zero_add, pair_commutator_on_sum R hq hr]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

end DoubleCommutator
end InfoGeometry.OperatorAlgebra.LieJordan
