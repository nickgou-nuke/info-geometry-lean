import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra

theorem cofactor_expansion {R : Type*} [CommRing R] (xA yA xB yB xC yC : R) :
  xA * (yB * 1 - 1 * yC) - yA * (xB * 1 - 1 * xC) + 1 * (xB * yC - yB * xC) =
  (xB * yC + xA * yB + yA * xC) - (yA * xB + yB * xC + xA * yC) := by
  ring
