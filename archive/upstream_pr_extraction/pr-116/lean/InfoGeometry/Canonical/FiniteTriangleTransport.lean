import Mathlib

/-!
# Finite incidence-graph transport

This is a finite algebraic transport owner.  A triangle is represented by its
three oriented edges, and holonomy is their composition.  The closure defect
is an endomorphism difference; no manifold curvature is asserted.
-/

namespace InfoGeometry.Canonical.FiniteTriangleTransport

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

structure EdgeTransportDatum where
  edge01 : V ≃ₗ[R] V
  edge12 : V ≃ₗ[R] V
  edge20 : V ≃ₗ[R] V

def triangleHolonomy (T : EdgeTransportDatum (R := R) (V := V)) : V ≃ₗ[R] V :=
  T.edge01.trans (T.edge12.trans T.edge20)

def closureDefect (T : EdgeTransportDatum (R := R) (V := V)) :
    V →ₗ[R] V :=
  (triangleHolonomy T).toLinearMap - (LinearEquiv.refl R V).toLinearMap

theorem triangleHolonomy_apply (T : EdgeTransportDatum (R := R) (V := V))
    (x : V) :
    triangleHolonomy T x = T.edge20 (T.edge12 (T.edge01 x)) := by
  simp [triangleHolonomy]

theorem closureDefect_apply (T : EdgeTransportDatum (R := R) (V := V))
    (x : V) :
    closureDefect T x = triangleHolonomy T x - x := by
  rfl

theorem closureDefect_eq_zero_iff
    (T : EdgeTransportDatum (R := R) (V := V)) :
    closureDefect T = 0 ↔ triangleHolonomy T = LinearEquiv.refl R V := by
  constructor
  · intro h
    apply LinearEquiv.ext
    intro x
    have hx := LinearMap.congr_fun h x
    change triangleHolonomy T x - x = 0 at hx
    exact sub_eq_zero.mp hx
  · intro h
    apply LinearMap.ext
    intro x
    change triangleHolonomy T x - x = 0
    rw [h]
    simp

theorem closureDefect_eq_zero_iff_pointwise
    (T : EdgeTransportDatum (R := R) (V := V)) :
    closureDefect T = 0 ↔ ∀ x, triangleHolonomy T x = x := by
  rw [closureDefect_eq_zero_iff]
  constructor
  · intro h x
    simpa using congrArg (fun e => e x) h
  · intro h
    apply LinearEquiv.ext
    intro x
    exact h x

end InfoGeometry.Canonical.FiniteTriangleTransport
