import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.Canonical.SplitComplex

/-!
# The real split-complex carrier as the first split Cayley-Dickson step

This file identifies the canonical `γ = 1` Albert doubling of `ℝ` with the
existing split-complex coordinate carrier. It proves only the first doubling
step; later split quaternion and split octonion identifications are separate
theorems.
-/

namespace InfoGeometry.Algebra.SplitCayleyDicksonRealBridge

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.SplitComplex

/-- Send split-complex coordinates to the canonical doubled real carrier. -/
def toAlbertPair (z : Carrier ℝ) : AlbertStep ℝ ℝ (1 : ℝ) :=
  ⟨z.re, z.im⟩

/-- The `γ = 1` Albert product on `ℝ × ℝ` agrees with split-complex
multiplication in the existing coordinate carrier. -/
theorem real_split_product (x y : Carrier ℝ) :
    AlbertStep.mul (toAlbertPair x) (toAlbertPair y) =
      toAlbertPair (x * y) := by
  cases x with
  | mk xr xi =>
    cases y with
    | mk yr yi =>
      ext <;> simp [AlbertStep.mul, toAlbertPair, Carrier.mul_re,
        Carrier.mul_im] <;> ring

end InfoGeometry.Algebra.SplitCayleyDicksonRealBridge
