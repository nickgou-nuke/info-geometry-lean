import InfoGeometry.Algebra.ZornVectorMatrix
import Mathlib.Tactic

/-!
# Parity-twisted axial cross channel

This is the primitive three-direction channel used by a chiral/Zorn layer.
The parity scalar is explicit; quaternionic or matrix commutator readouts are
downstream representation adapters and are intentionally not part of this
owner.
-/

namespace InfoGeometry.Algebra.ZornVec3

variable {R : Type*} [CommRing R]

def parityTwistedCross (χ : R) (u v : ZornVec3 R) : ZornVec3 R :=
  fun k => χ * cross u v k

def parityTwist (χ : R) (u : ZornVec3 R) : ZornVec3 R :=
  fun k => χ * u k

theorem parityTwistedCross_apply (χ : R) (u v : ZornVec3 R) (k : Fin 3) :
    parityTwistedCross χ u v k = χ * cross u v k := rfl

theorem parityTwistedCross_eq_smul (χ : R) (u v : ZornVec3 R) :
    parityTwistedCross χ u v = parityTwist χ (cross u v) := rfl

theorem parityTwistedCross_add_left (χ : R) (u v w : ZornVec3 R) :
    parityTwistedCross χ (fun k => u k + v k) w =
      (fun k => parityTwistedCross χ u w k + parityTwistedCross χ v w k) := by
  funext k
  fin_cases k <;> simp [parityTwistedCross, cross] <;> ring

theorem parityTwistedCross_add_right (χ : R) (u v w : ZornVec3 R) :
    parityTwistedCross χ u (fun k => v k + w k) =
      (fun k => parityTwistedCross χ u v k + parityTwistedCross χ u w k) := by
  funext k
  fin_cases k <;> simp [parityTwistedCross, cross] <;> ring

theorem parityTwistedCross_swap (χ : R) (u v : ZornVec3 R) :
    parityTwistedCross χ u v =
      (fun k => -(parityTwistedCross χ v u k)) := by
  funext k
  fin_cases k <;>
    simp [parityTwistedCross, cross] <;>
    ring

theorem parityTwistedCross_self (χ : R) (u : ZornVec3 R) :
    parityTwistedCross χ u u = 0 := by
  funext k
  fin_cases k <;>
    simp [parityTwistedCross, cross] <;>
    ring

theorem parityTwistedCross_basis (χ : R) (i j k : Fin 3) :
    parityTwistedCross χ (basis i) (basis j) k =
      χ * cross (basis i) (basis j) k := rfl

theorem parityTwistedCross_twist_involutive
    (χ : R) (hχ : χ * χ = 1) (u : ZornVec3 R) :
    parityTwist χ (parityTwist χ u) = u := by
  funext k
  calc
    parityTwist χ (parityTwist χ u) k = (χ * χ) * u k := by
      simp [parityTwist]
      ring
    _ = 1 * u k := by rw [hχ]
    _ = u k := one_mul _

end InfoGeometry.Algebra.ZornVec3
