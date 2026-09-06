import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Basic
import Mathlib.Tactic

/-!
# Algebraic curvature decomposition for dual statistical connections

This module formalizes the theorem-safe algebraic content of the midpoint
connection decomposition.  It does not pretend to derive curvature identities
from unrelated tensors: the general sum/difference identities are explicit
fields of the datum, and dual-flat formulas are proved as corollaries.
-/

namespace InfoGeometry.Geometry.Statistical

section EndomorphismCommutator

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

/-- Commutator of real-linear endomorphisms. -/
def endCommutator (A B : Module.End ℝ T) : Module.End ℝ T :=
  A.comp B - B.comp A

@[simp] theorem endCommutator_apply (A B : Module.End ℝ T) (x : T) :
    endCommutator A B x = A (B x) - B (A x) := by
  rfl

@[simp] theorem endCommutator_swap (A B : Module.End ℝ T) :
    endCommutator B A = -endCommutator A B := by
  unfold endCommutator
  abel

@[simp] theorem endCommutator_self (A : Module.End ℝ T) :
    endCommutator A A = 0 := by
  unfold endCommutator
  simp

end EndomorphismCommutator

section CurvaturePacket

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

/--
Algebraic curvature data for a pair of connections `∇`, `∇*`, their midpoint
`∇⁰`, and difference operator `K`.

The two curvature decomposition identities are stored explicitly.  This keeps
this module independent of any particular manifold/connection implementation
while ensuring every downstream theorem follows from stated hypotheses.
-/
structure CurvatureDecomposition (T : Type*) [AddCommGroup T] [Module ℝ T] where
  Rnabla : T → T → Module.End ℝ T
  RnablaStar : T → T → Module.End ℝ T
  Rzero : T → T → Module.End ℝ T
  K : T → Module.End ℝ T
  dK : T → T → Module.End ℝ T
  difference : T → Module.End ℝ T
  difference_eq_neg_two_K :
    ∀ X, difference X = (-2 : ℝ) • K X
  curvature_sum :
    ∀ X Y,
      Rnabla X Y + RnablaStar X Y =
        (2 : ℝ) • Rzero X Y +
          (2 : ℝ) • endCommutator (K X) (K Y)
  curvature_diff :
    ∀ X Y,
      Rnabla X Y - RnablaStar X Y =
        (2 : ℝ) • dK X Y

namespace CurvatureDecomposition

variable (C : CurvatureDecomposition T)

/-- Dual flatness means both dual curvature operators vanish identically. -/
def IsDualFlat : Prop :=
  ∀ X Y, C.Rnabla X Y = 0 ∧ C.RnablaStar X Y = 0

/-- Under dual flatness, the covariant exterior difference term vanishes. -/
theorem dK_eq_zero_of_dualFlat
    (hflat : C.IsDualFlat)
    (X Y : T) :
    C.dK X Y = 0 := by
  have hdiff := C.curvature_diff X Y
  rcases hflat X Y with ⟨hnabla, hnablaStar⟩
  rw [hnabla, hnablaStar] at hdiff
  simp only [sub_self] at hdiff
  have hhalf := congrArg
    (fun F : Module.End ℝ T => (1 / 2 : ℝ) • F) hdiff
  have htwo : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  have hz : (0 : Module.End ℝ T) = C.dK X Y := by
    simpa [smul_smul, htwo] using hhalf
  exact hz.symm

/--
Under dual flatness, midpoint curvature is the negative commutator of the
statistical difference endomorphisms `K_X`.
-/
theorem Rzero_eq_neg_endCommutator_of_dualFlat
    (hflat : C.IsDualFlat)
    (X Y : T) :
    C.Rzero X Y = -endCommutator (C.K X) (C.K Y) := by
  have hsum := C.curvature_sum X Y
  rcases hflat X Y with ⟨hnabla, hnablaStar⟩
  rw [hnabla, hnablaStar] at hsum
  simp only [zero_add] at hsum
  have hhalf := congrArg
    (fun F : Module.End ℝ T => (1 / 2 : ℝ) • F) hsum
  have htwo : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  have hzero :
      C.Rzero X Y + endCommutator (C.K X) (C.K Y) = 0 := by
    simpa [smul_add, smul_smul, htwo] using hhalf.symm
  exact eq_neg_of_add_eq_zero_left hzero

/-- The difference-operator commutator is four times the `K`-commutator. -/
theorem difference_endCommutator_eq_four_K
    (X Y : T) :
    endCommutator (C.difference X) (C.difference Y) =
      (4 : ℝ) • endCommutator (C.K X) (C.K Y) := by
  rw [C.difference_eq_neg_two_K X, C.difference_eq_neg_two_K Y]
  unfold endCommutator
  rw [LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.smul_comp, LinearMap.comp_smul]
  simp [smul_sub, smul_smul]

/--
Equivalent dual-flat formula in terms of `D = ∇* - ∇ = -2K`:
`R⁰ = -1/4 [D_X,D_Y]`.
-/
theorem Rzero_eq_neg_quarter_difference_commutator_of_dualFlat
    (hflat : C.IsDualFlat)
    (X Y : T) :
    C.Rzero X Y =
      (-1 / 4 : ℝ) • endCommutator (C.difference X) (C.difference Y) := by
  rw [C.Rzero_eq_neg_endCommutator_of_dualFlat hflat X Y,
    C.difference_endCommutator_eq_four_K X Y]
  norm_num [smul_smul]

end CurvatureDecomposition

end CurvaturePacket

section MetricSkewness

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
The commutator of two symmetric endomorphisms is skew-adjoint for the real
inner product.
-/
theorem endCommutator_skew_of_symmetric
    (A B : Module.End ℝ E)
    (hA : A.IsSymmetric)
    (hB : B.IsSymmetric)
    (u v : E) :
    inner ℝ (endCommutator A B u) v +
      inner ℝ u (endCommutator A B v) = 0 := by
  simp only [endCommutator_apply, inner_sub_left, inner_sub_right]
  rw [hA (B u) v, hB (A u) v, hA u (B v), hB u (A v)]
  ring

end MetricSkewness

end InfoGeometry.Geometry.Statistical
