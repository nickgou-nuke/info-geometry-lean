import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Canonical.ZornVectorMatrixIsomorphism

namespace InfoGeometry.Canonical

/-!
Compatibility between the integral coordinate product and its rational
polynomial extension.  This is the missing scalar-extension statement below
the rational Zorn comparison; it does not claim a tensor-product universal
property.
-/

theorem rationalizeIntegral_splitOctonionMul
    (x y : StandardIntegralSplitOctonion) :
    rationalizeIntegral (splitOctonionMul x y) =
      splitOctonionMulQ
        (rationalizeIntegral x)
        (rationalizeIntegral y) := by
  funext b
  fin_cases b <;>
    simp [rationalizeIntegral, splitOctonionMul, splitOctonionMulQ,
      splitQuaternionOf, splitQuaternionLPart, splitQuaternionConj,
      splitQuaternionAdd, splitQuaternionMul,
      splitOctonionOfQuaternionPair,
      splitQuaternionOfQ, splitQuaternionLPartQ, splitQuaternionConjQ,
      splitQuaternionAddQ, splitQuaternionMulQ,
      splitOctonionOfQuaternionPairQ] <;>
    ring

theorem rationalizeIntegral_coordinateConj
    (x : StandardIntegralSplitOctonion) :
    coordinateConj (rationalizeIntegral x) =
      fun b =>
        match b with
        | .one => x .one
        | .l => -x .l
        | .i => -x .i
        | .il => -x .il
        | .j => -x .j
        | .jl => -x .jl
        | .k => -x .k
        | .kl => -x .kl := by
  funext b
  fin_cases b <;> rfl

end InfoGeometry.Canonical
