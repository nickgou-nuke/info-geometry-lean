import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.MassieuOptimalTransport

Minimal algebraic natural-gradient identity for the 1D Massieu/log-barrier lane.
-/

namespace InfoGeometry.Canonical.MassieuOptimalTransport

variable {R : Type*} [CommRing R]

/--
Abstract polynomial encoding of the 1D Massieu/log-barrier relations:

* `dPhi * a = -1`
* `H * (a*a) = 1`
-/
structure MassieuGradientState (R : Type*) [CommRing R] where
  a    : R
  dPhi : R
  H    : R
  grad_rel : dPhi * a = -1
  hess_rel : H * (a * a) = 1

/--
If the flow equation is `H * Δa = -dPhi`, then `Δa = a`.
-/
theorem natural_gradient_is_coordinate
    (s : MassieuGradientState R) (Δa : R)
    (h_flow : s.H * Δa = -s.dPhi) :
    Δa = s.a := by
  have h1 : (s.H * Δa) * (s.a * s.a) = (-s.dPhi) * (s.a * s.a) := by
    rw [h_flow]
  have h2 : (s.H * (s.a * s.a)) * Δa = (-s.dPhi) * (s.a * s.a) := by
    calc
      (s.H * (s.a * s.a)) * Δa = (s.H * Δa) * (s.a * s.a) := by ring
      _ = (-s.dPhi) * (s.a * s.a) := h1
  have h3 : 1 * Δa = (-s.dPhi) * (s.a * s.a) := by
    rw [s.hess_rel] at h2
    exact h2
  have h4 : Δa = (-s.dPhi) * (s.a * s.a) := by
    calc
      Δa = 1 * Δa := by ring
      _ = (-s.dPhi) * (s.a * s.a) := h3
  have h5 : Δa = -(s.dPhi * s.a) * s.a := by
    calc
      Δa = (-s.dPhi) * (s.a * s.a) := h4
      _ = -(s.dPhi * s.a) * s.a := by ring
  have h6 : Δa = -(-1) * s.a := by
    rw [s.grad_rel] at h5
    exact h5
  calc
    Δa = -(-1) * s.a := h6
    _ = 1 * s.a := by ring
    _ = s.a := by ring

end InfoGeometry.Canonical.MassieuOptimalTransport

