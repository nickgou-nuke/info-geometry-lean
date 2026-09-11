import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic curvature decomposition for dual statistical connections

This file deliberately formalizes the curvature-decomposition identities as an
algebraic packet.  It does not pretend to derive connection-curvature formulas
from arbitrary tensors.  A later manifold owner can instantiate this packet
from genuine affine connections.
-/

namespace InfoGeometry.Statistical

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

/-- Commutator of two tangent endomorphisms. -/
def endComm (A B : Module.End ℝ T) : Module.End ℝ T :=
  A.comp B - B.comp A

@[simp] theorem endComm_apply (A B : Module.End ℝ T) (x : T) :
    endComm A B x = A (B x) - B (A x) := rfl

/-- Endomorphism commutator is skew in its two arguments. -/
theorem endComm_swap (A B : Module.End ℝ T) :
    endComm A B = -endComm B A := by
  unfold endComm
  abel

/--
An algebraic packet containing the two standard curvature decomposition
identities for dual connections `∇ = ∇⁰ + K` and `∇* = ∇⁰ - K`.
-/
structure CurvatureDecompositionPacket (T : Type*) [AddCommGroup T] [Module ℝ T] where
  Rnabla : T → T → Module.End ℝ T
  RnablaStar : T → T → Module.End ℝ T
  Rzero : T → T → Module.End ℝ T
  K : T → Module.End ℝ T
  dK : T → T → Module.End ℝ T

  curvature_sum : ∀ X Y,
    Rnabla X Y + RnablaStar X Y =
      (2 : ℝ) • Rzero X Y + (2 : ℝ) • endComm (K X) (K Y)

  curvature_diff : ∀ X Y,
    Rnabla X Y - RnablaStar X Y = (2 : ℝ) • dK X Y

namespace CurvatureDecompositionPacket

/-- The difference endomorphism `D = ∇* - ∇ = -2K`. -/
def difference (C : CurvatureDecompositionPacket T) (X : T) : Module.End ℝ T :=
  (-2 : ℝ) • C.K X

@[simp] theorem difference_eq (C : CurvatureDecompositionPacket T) (X : T) :
    C.difference X = (-2 : ℝ) • C.K X := rfl

/-- `K = -1/2 D` for the convention `D = -2K`. -/
theorem K_eq_neg_half_difference
    (C : CurvatureDecompositionPacket T) (X : T) :
    C.K X = (-1 / 2 : ℝ) • C.difference X := by
  simp [difference, smul_smul]

/-- Dual flatness forces the covariant exterior derivative of `K` to vanish. -/
theorem dual_flat_dK_zero
    (C : CurvatureDecompositionPacket T)
    (hflat : ∀ X Y, C.Rnabla X Y = 0 ∧ C.RnablaStar X Y = 0)
    (X Y : T) :
    C.dK X Y = 0 := by
  have hdiff := C.curvature_diff X Y
  rw [(hflat X Y).1, (hflat X Y).2, sub_zero] at hdiff
  have hscaled : (2 : ℝ) • C.dK X Y = 0 := hdiff.symm
  have hinv := congrArg (fun F : Module.End ℝ T => (1 / 2 : ℝ) • F) hscaled
  simpa [smul_smul] using hinv

/--
Dual flatness gives the mean/Levi-Civita curvature formula
`R⁰(X,Y) = -[K_X,K_Y]`.
-/
theorem dual_flat_curvature
    (C : CurvatureDecompositionPacket T)
    (hflat : ∀ X Y, C.Rnabla X Y = 0 ∧ C.RnablaStar X Y = 0)
    (X Y : T) :
    C.Rzero X Y = -endComm (C.K X) (C.K Y) := by
  have hsum := C.curvature_sum X Y
  rw [(hflat X Y).1, (hflat X Y).2, zero_add] at hsum
  have hscaled :
      (2 : ℝ) • (C.Rzero X Y + endComm (C.K X) (C.K Y)) = 0 := by
    rw [smul_add]
    exact hsum.symm
  have hinv := congrArg (fun F : Module.End ℝ T => (1 / 2 : ℝ) • F) hscaled
  have hzero : C.Rzero X Y + endComm (C.K X) (C.K Y) = 0 := by
    simpa [smul_smul] using hinv
  exact eq_neg_of_add_eq_zero_left hzero

/-- Scaling both entries of an endomorphism commutator scales by the product. -/
theorem endComm_smul_smul
    (a b : ℝ) (A B : Module.End ℝ T) :
    endComm (a • A) (b • B) = (a * b) • endComm A B := by
  ext x
  simp [endComm, smul_sub, smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-- The difference-tensor commutator is four times the `K` commutator. -/
theorem difference_comm
    (C : CurvatureDecompositionPacket T) (X Y : T) :
    endComm (C.difference X) (C.difference Y) =
      (4 : ℝ) • endComm (C.K X) (C.K Y) := by
  rw [difference, difference, endComm_smul_smul]
  norm_num

/--
Dual flatness in difference-tensor form:
`R⁰(X,Y) = -(1/4)[D_X,D_Y]`.
-/
theorem dual_flat_curvature_difference
    (C : CurvatureDecompositionPacket T)
    (hflat : ∀ X Y, C.Rnabla X Y = 0 ∧ C.RnablaStar X Y = 0)
    (X Y : T) :
    C.Rzero X Y = (-1 / 4 : ℝ) • endComm (C.difference X) (C.difference Y) := by
  rw [C.dual_flat_curvature hflat X Y, C.difference_comm X Y]
  simp [smul_smul]

end CurvatureDecompositionPacket

end InfoGeometry.Statistical
