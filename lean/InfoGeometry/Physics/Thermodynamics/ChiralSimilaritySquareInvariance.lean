import Mathlib.Algebra.Group.Units.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic

namespace InfoGeometry.Physics.Thermodynamics

/-!
Generic algebraic similarity identities.  These statements require only a
ring; they do not assert self-adjointness, spectral invariance, or a mass gap.
-/

def similarityDeform {R : Type*} [Ring R] (g : Rˣ) (D : R) : R :=
  (g : R) * D * (↑g⁻¹ : R)

theorem similarityDeform_sq {R : Type*} [Ring R] (g : Rˣ) (D : R) :
    similarityDeform g D * similarityDeform g D =
      similarityDeform g (D * D) := by
  simp [similarityDeform, mul_assoc]

theorem similarityDeform_sq_eq {R : Type*} [Ring R] (g : Rˣ) (D : R)
    (hcomm : (g : R) * (D * D) = (D * D) * (g : R)) :
    similarityDeform g D * similarityDeform g D = D * D := by
  rw [similarityDeform_sq]
  unfold similarityDeform
  calc
    (g : R) * (D * D) * (↑g⁻¹ : R) =
        ((D * D) * (g : R)) * (↑g⁻¹ : R) := by rw [hcomm]
    _ = D * D := by simp

end InfoGeometry.Physics.Thermodynamics
