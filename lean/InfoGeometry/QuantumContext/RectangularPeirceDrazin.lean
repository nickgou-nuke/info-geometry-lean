/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.RectangularDrazinLift
import InfoGeometry.Core.PeirceDecomposition

/-!
# Peirce compression and reconstruction of a full matrix Drazin inverse

The existing four-corner decomposition is the owner. Commutation with the
support is a stated invariant-splitting criterion, not commutativity of the
matrix algebra. Nilpotence of the complementary corner remains explicit.
-/

namespace InfoGeometry.QuantumContext.RectangularPeirceDrazin

open Matrix InfoGeometry.Algebra.RectangularRetract
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.QuantumContext.Drazin
open InfoGeometry.QuantumContext.RectangularDrazinLift

variable {R m n : Type*} [Ring R]
variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {K : Matrix n m R} {Q : Matrix m n R}

/-- Reconstruction from the compressed matrix and the complementary Peirce corner. -/
theorem split_of_commute (h : Q * K = 1) (T : Matrix n n R)
    (hc : Commute (K * Q) T) :
    T = cornerHom K Q h (Q * T * K) + (1 - K * Q) * T * (1 - K * Q) := by
  have hp := support_idempotent h
  have h10 : (K * Q) * T * (1 - K * Q) = 0 := by
    rw [hc.eq, Matrix.mul_assoc, hp.mul_one_sub_self, Matrix.mul_zero]
  have h01 : (1 - K * Q) * T * (K * Q) = 0 := by
    rw [Matrix.mul_assoc, ← hc.eq, ← Matrix.mul_assoc,
      hp.one_sub_mul_self, Matrix.zero_mul]
  have hs := peirce_decomposition (K * Q) T
  simp only [component11, component10, component01, component00,
    complementIdempotent, h10, h01, add_zero] at hs
  simpa only [cornerHom_apply, Matrix.mul_assoc] using hs

theorem retraction_mul_complement_corner (h : Q * K = 1) (T : Matrix n n R) :
    Q * ((1 - K * Q) * T * (1 - K * Q)) = 0 := by
  have hz : Q * (1 - K * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, retraction_mul_support h, sub_self]
  simp only [← Matrix.mul_assoc, hz, Matrix.zero_mul]

theorem complement_corner_mul_inclusion (h : Q * K = 1) (T : Matrix n n R) :
    ((1 - K * Q) * T * (1 - K * Q)) * K = 0 := by
  have hz : (1 - K * Q) * K = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, support_mul_inclusion h, sub_self]
  simp only [Matrix.mul_assoc, hz, Matrix.mul_zero]

/-- Construct a full ambient Drazin inverse from compression and a nilpotent
complementary corner. No inverse or nilpotence is inferred merely from a projector. -/
theorem isDrazinInverse_of_retract (h : Q * K = 1) (T : Matrix n n R)
    (hc : Commute (K * Q) T) {D : Matrix m m R} {k r : ℕ}
    (hD : IsDrazinInverse (Q * T * K) D k)
    (hN : ((1 - K * Q) * T * (1 - K * Q)) ^ r = 0) :
    IsDrazinInverse T (cornerHom K Q h D) (k + r + 1) := by
  have hlift := isDrazinInverse_lift h
    (retraction_mul_complement_corner h T)
    (complement_corner_mul_inclusion h T) hD hN
  rw [← split_of_commute h T hc] at hlift
  exact hlift

end InfoGeometry.QuantumContext.RectangularPeirceDrazin
