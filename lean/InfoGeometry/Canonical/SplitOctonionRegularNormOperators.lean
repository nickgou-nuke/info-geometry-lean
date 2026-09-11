import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionRegularOperators

noncomputable section

namespace SplitOctonion

open scoped Quaternion

def splitConjugate (x : SplitOctonion) : SplitOctonion :=
  ⟨star x.a, -x.b⟩

theorem splitConjugate_injective : Function.Injective splitConjugate := by
  intro x y h
  apply SplitOctonion.ext
  · have ha := congrArg SplitOctonion.a h
    simpa only [splitConjugate, star_star] using congrArg star ha
  · have hb := congrArg SplitOctonion.b h
    simpa only [splitConjugate, neg_inj] using hb

theorem splitConjugate_mul_leftRegular (x z : SplitOctonion) :
    leftRegular (splitConjugate x) (leftRegular x z) =
      normSQ x • z := by
  rcases x with ⟨a, b⟩
  rcases z with ⟨c, d⟩
  change (⟨star a, -b⟩ : SplitOctonion) *
      ((⟨a, b⟩ : SplitOctonion) * ⟨c, d⟩) =
    normSQ ⟨a, b⟩ • (⟨c, d⟩ : SplitOctonion)
  apply SplitOctonion.ext <;>
    ext <;>
    simp [mul_a, mul_b, normSQ] <;>
    ring

theorem leftRegular_splitConjugate_comp (x : SplitOctonion) :
    (leftRegular (splitConjugate x)).comp (leftRegular x) =
      normSQ x • LinearMap.id := by
  apply LinearMap.ext
  intro z
  exact splitConjugate_mul_leftRegular x z

theorem splitConjugate_mul_leftRegular_null (x z : SplitOctonion)
    (hx : normSQ x = 0) :
    leftRegular (splitConjugate x) (leftRegular x z) = 0 := by
  rw [splitConjugate_mul_leftRegular, hx, zero_smul]

theorem range_leftRegular_le_ker_leftRegular_splitConjugate (x : SplitOctonion)
    (hx : normSQ x = 0) :
    LinearMap.range (leftRegular x) ≤
      LinearMap.ker (leftRegular (splitConjugate x)) := by
  rintro y ⟨z, rfl⟩
  exact splitConjugate_mul_leftRegular_null x z hx

theorem leftRegular_not_bijective_of_null (x : SplitOctonion)
    (hx0 : x ≠ 0) (hx : normSQ x = 0) :
    ¬ Function.Bijective (leftRegular x) := by
  intro hbij
  have hsurj : Function.Surjective (leftRegular x) := hbij.2
  have hzero : leftRegular (splitConjugate x) = 0 := by
    apply LinearMap.ext
    intro y
    obtain ⟨z, hz⟩ := hsurj y
    rw [← hz]
    exact splitConjugate_mul_leftRegular_null x z hx
  have hone := LinearMap.congr_fun hzero 1
  have hconj : splitConjugate x = 0 := by
    simpa only [leftRegular_apply_one, LinearMap.zero_apply] using hone
  apply hx0
  apply splitConjugate_injective
  simpa only [splitConjugate, star_zero, neg_zero, zero_a, zero_b] using hconj

end SplitOctonion
