/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.AssociativeGaugeConnection

/-!
# Corrected curvature and central connection shifts

These are local algebraic transport identities on an arbitrary associative
coefficient ring. The affine gauge potential is the existing owner definition.
Central shifts contribute their derivative curl to the curvature and the
opposite curl to the curving. Global descent data is a separate construction.
-/

namespace InfoGeometry.Geometry.AssociativeGaugeConnection

variable {R A : Type*} [Ring R] [Ring A] [Module R A] [SMulCommClass R A A]

theorem conjugate_add (g : Aˣ) (x y : A) :
    conjugate g (x + y) = conjugate g x + conjugate g y := by
  simp [conjugate, mul_add, add_mul]

theorem correctedCurvature_gauge_covariant (D E : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x)) (a b c : A) (g : Aˣ) :
    curvature D E (gaugePotential D a g) (gaugePotential E b g) + conjugate g c =
      conjugate g (curvature D E a b + c) := by
  rw [curvature_gauge_covariant D E hD hE hcomm, conjugate_add]

omit [SMulCommClass R A A] in
/-- Only these three mixed commutators are required to vanish. -/
theorem curvature_add_commuting_shifts (D E : Module.End R A) (a b s t : A)
    (hat : Commute a t) (hsb : Commute s b) (hst : Commute s t) :
    curvature D E (a + s) (b + t) = curvature D E a b + (D t - E s) := by
  simp only [curvature, map_add, mul_add, add_mul]
  rw [hat.eq, hsb.eq, hst.eq]
  noncomm_ring

/-- Local analogue of the connection/curving transformation with central shifts. -/
theorem correctedCurvature_gauge_centralShift (D E : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x)) (a b c s t : A) (g : Aˣ)
    (hs : ∀ x : A, Commute s x) (ht : ∀ x : A, Commute t x) :
    curvature D E (gaugePotential D a g + s) (gaugePotential E b g + t) +
        (conjugate g c - (D t - E s)) =
      conjugate g (curvature D E a b + c) := by
  rw [curvature_add_commuting_shifts D E _ _ s t
    (ht _).symm (hs _) (hs t)]
  rw [curvature_gauge_covariant D E hD hE hcomm, conjugate_add]
  noncomm_ring

theorem correctedFlat_gauge_centralShift (D E : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x)) (a b c s t : A) (g : Aˣ)
    (hs : ∀ x : A, Commute s x) (ht : ∀ x : A, Commute t x)
    (hflat : curvature D E a b + c = 0) :
    curvature D E (gaugePotential D a g + s) (gaugePotential E b g + t) +
      (conjugate g c - (D t - E s)) = 0 := by
  rw [correctedCurvature_gauge_centralShift D E hD hE hcomm a b c s t g hs ht,
    hflat]
  simp [conjugate]

end InfoGeometry.Geometry.AssociativeGaugeConnection
