import Mathlib.Tactic
import InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary

/-!
# Native Commutator Identities for Boundary Modes

This module records commutator identities for the two boundary-mode terms
provided by `Cl55OperatorProjectiveBoundary`.  The results are ring identities;
they do not define a TKK algebra or an anomaly functional.
-/

variable {A : Type*} [Ring A] [Algebra ℚ A]

namespace NoncommutativeGeometry

open InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary

variable {e f : Fin 5 → A} [hCl : OperatorCl55 e f]

/-- The native Lie algebra commutator for the non-commutative operator ring. -/
def lie_bracket (x y : A) : A := x * y - y * x

/-- Unfolding the bracket gives its defining commutator expression. -/
theorem projective_compensation_tkk_closure :
    lie_bracket (projective_compensation_a e f) (projective_compensation_c e f) =
      projective_compensation_a e f * projective_compensation_c e f -
      projective_compensation_c e f * projective_compensation_a e f := by
  rfl

/-- The commutator of a boundary mode with itself is zero. -/
theorem minus_same_arrow_anomaly_eq_zero :
    lie_bracket (projective_compensation_a e f) (projective_compensation_a e f) = 0 := by
  unfold lie_bracket
  rw [sub_self]

/-- The commutator of the second boundary mode with itself is zero. -/
theorem plus_same_arrow_anomaly_eq_zero :
    lie_bracket (projective_compensation_c e f) (projective_compensation_c e f) = 0 := by
  unfold lie_bracket
  rw [sub_self]

/-- The mixed boundary commutator acts on the first mode by twice that mode. -/
theorem projective_boundary_tkk_scale_symmetry :
    lie_bracket (lie_bracket (projective_compensation_a e f) (projective_compensation_c e f)) (projective_compensation_a e f)
    = projective_compensation_a e f + projective_compensation_a e f := by
  have h_anti := projective_compensation_anticomm (e:=e) (f:=f)
  have h_sq := projective_compensation_a_sq (e:=e) (f:=f)
  set a := projective_compensation_a e f
  set c := projective_compensation_c e f
  unfold lie_bracket

  have h1 : (a * c - c * a) * a - a * (a * c - c * a) = a * c * a + a * c * a := by
    calc
      (a * c - c * a) * a - a * (a * c - c * a)
        = a * c * a + a * c * a - c * (a * a) - (a * a) * c := by noncomm_ring
      _ = a * c * a + a * c * a - c * 0 - 0 * c := by rw [h_sq]
      _ = a * c * a + a * c * a := by simp

  have h2 : a * c * a = a := by
    calc
      a * c * a = a * c * a + 0 := by rw [add_zero]
      _ = a * c * a + c * 0 := by simp
      _ = a * c * a + c * (a * a) := by rw [h_sq]
      _ = (a * c + c * a) * a := by noncomm_ring
      _ = 1 * a := by rw [h_anti]
      _ = a := by rw [one_mul]

  rw [h1, h2]

end NoncommutativeGeometry
