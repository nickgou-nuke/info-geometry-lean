import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionQuaternionPolar

noncomputable section

namespace SplitOctonion

def splitConj (X : SplitOctonion) : SplitOctonion :=
  ⟨star X.a, -X.b⟩

@[simp] theorem splitConj_a (X : SplitOctonion) :
    (splitConj X).a = star X.a := rfl

@[simp] theorem splitConj_b (X : SplitOctonion) :
    (splitConj X).b = -X.b := rfl

theorem splitConj_involutive (X : SplitOctonion) :
    splitConj (splitConj X) = X := by
  apply SplitOctonion.ext
  · simp [splitConj, star_star]
  · simp [splitConj]

theorem splitConj_mul_self (X : SplitOctonion) :
    splitConj X * X = (normSQ X) • (1 : SplitOctonion) := by
  have hnorm : normSQ X = Quaternion.normSq X.a - Quaternion.normSq X.b := by
    unfold normSQ
    rw [normSq_eq_re_mul_star, normSq_eq_re_mul_star]
  apply SplitOctonion.ext
  · simp only [mul_a, splitConj, one_a, smul_a]
    have hb : star X.b * (-X.b) =
        -((Quaternion.normSq X.b : ℝ) • (1 : H)) := by
      calc
        star X.b * (-X.b) = -(star X.b * X.b) := mul_neg _ _
        _ = -((Quaternion.normSq X.b : ℝ) • (1 : H)) := by
          rw [H_star_mul_self]
    rw [H_star_mul_self, hb, hnorm]
    module
  · simp only [mul_b, splitConj, one_b, smul_b]
    calc
      X.b * star X.a + (-X.b) * star X.a =
          X.b * star X.a + -(X.b * star X.a) := by
            exact congrArg (fun q => X.b * star X.a + q)
              (neg_mul X.b (star X.a))
      _ = 0 := add_neg_cancel _
      _ = (normSQ X) • (0 : H) := by simp

theorem self_mul_splitConj (X : SplitOctonion) :
    X * splitConj X = (normSQ X) • (1 : SplitOctonion) := by
  have hnorm : normSQ X = Quaternion.normSq X.a - Quaternion.normSq X.b := by
    unfold normSQ
    rw [normSq_eq_re_mul_star, normSq_eq_re_mul_star]
  apply SplitOctonion.ext
  · simp only [mul_a, splitConj, one_a, smul_a]
    change X.a * star X.a + star (-X.b) * X.b =
      (normSQ X) • (1 : H)
    have hstarneg : star (-X.b) = -star X.b := by
      simp
    have ha : X.a * star X.a = (Quaternion.normSq X.a : ℝ) • (1 : H) := by
      simpa [star_star] using H_star_mul_self (star X.a)
    rw [hstarneg]
    calc
      X.a * star X.a + (-star X.b) * X.b =
          X.a * star X.a + -(star X.b * X.b) := by
            exact congrArg (fun q => X.a * star X.a + q)
              (neg_mul (star X.b) X.b)
      _ = (normSQ X) • (1 : H) := by
        rw [ha, H_star_mul_self, hnorm]
        module
  · simp only [mul_b, splitConj, one_b, smul_b, star_star]
    calc
      (-X.b) * X.a + X.b * X.a =
          -(X.b * X.a) + X.b * X.a := by
            exact congrArg (fun q => q + X.b * X.a)
              (neg_mul X.b X.a)
      _ = 0 := neg_add_cancel _
      _ = (normSQ X) • (0 : H) := by simp

end SplitOctonion
