import InfoGeometry.Exceptional.FreudenthalSymplecticTKKJacobiObstruction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure

/-!
# Conditional mixed-Jacobi bridge

The total TKK bracket needs one additional mixed-triple symmetry.  This file
does not assume that identity globally; it proves exactly the Jacobi component
that follows when the identity is supplied for the chosen inputs.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-! The missing TKK datum is a genuine mixed-triple law.  It is kept
explicit because it is not implied by the current symplectic operator
closure. -/
structure TKKMixedTripleData where
  mixed_triple : ∀ x z y : FreudenthalCharge J,
    (mixedSymplecticBracket D z y : Module.End ℝ (FreudenthalCharge J)) x =
      (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z

theorem tkk_mixed_jacobi_plus1_component_eq_zero
    (x y z : FreudenthalCharge J) :
    (tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injPlus1 D y) (injMinus1 D z))).plus1 +
      (tkkTotalBracket D (injPlus1 D y)
        (tkkTotalBracket D (injMinus1 D z) (injMinus1 D x))).plus1 +
      (tkkTotalBracket D (injMinus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injPlus1 D y))).plus1 = 0 := by
  simp [tkkTotalBracket, injMinus1, injPlus1]

/-! The opposite component is not definitionally zero.  It is exactly the
remaining mixed-triple condition recorded by the obstruction owner. -/
theorem tkk_mixed_jacobi_minus1_component_eq_zero
    (x z y : FreudenthalCharge J)
    (htriple :
      (mixedSymplecticBracket D z y : Module.End ℝ (FreudenthalCharge J)) x =
        (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z) :
    (tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injPlus1 D y) (injMinus1 D z))).minus1 +
      (tkkTotalBracket D (injPlus1 D y)
        (tkkTotalBracket D (injMinus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injMinus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injPlus1 D y))).minus1 = 0 := by
  exact tkk_mixed_jacobi_minus1_of_triple_identity D x z y htriple

theorem tkk_mixed_jacobi_minus1_component_of_data
    (data : TKKMixedTripleData D) (x z y : FreudenthalCharge J) :
    (tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injPlus1 D y) (injMinus1 D z))).minus1 +
      (tkkTotalBracket D (injPlus1 D y)
        (tkkTotalBracket D (injMinus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injMinus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injPlus1 D y))).minus1 = 0 := by
  exact tkk_mixed_jacobi_minus1_component_eq_zero D x z y
    (data.mixed_triple x z y)

end InfoGeometry.Exceptional.Freudenthal
