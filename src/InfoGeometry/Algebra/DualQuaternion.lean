import Mathlib.Algebra.TrivSqZeroExt
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Quaternion

/-!
# Dual Quaternions

We define Dual Quaternions explicitly as the algebra $\mathbb{H}[\epsilon] / \langle\epsilon^2\rangle$.
These represent 3D rigid body motions (SE(3)) and form the flat-space Wigner-Inönü contraction
of the 5-graded super-symmetry representations in the repository.

In Mathlib, the dual numbers over a ring `R` are implemented as `TrivSqZeroExt R R`.
-/

namespace InfoGeometry.Algebra

/-- A Dual Quaternion is a quaternion over the dual numbers. -/
abbrev DualQuaternion (R : Type*) [CommRing R] := Quaternion (TrivSqZeroExt R R)

/-- 
The Dual Quaternion algebra explicitly models the rotation and translation 
components of SE(3). We can embed two real quaternions (the rotation part and the translation part)
into a single dual quaternion.
-/
def DualQuaternion.mk_dual {R : Type*} [CommRing R] (real_part dual_part : Quaternion R) : DualQuaternion R :=
  ⟨TrivSqZeroExt.inr real_part.re + TrivSqZeroExt.inl dual_part.re,
   TrivSqZeroExt.inr real_part.imI + TrivSqZeroExt.inl dual_part.imI,
   TrivSqZeroExt.inr real_part.imJ + TrivSqZeroExt.inl dual_part.imJ,
   TrivSqZeroExt.inr real_part.imK + TrivSqZeroExt.inl dual_part.imK⟩

end InfoGeometry.Algebra
