import InfoGeometry.Basic
import InfoGeometry.KL.Finite

/-!
# Core Entropy

Core entropy/KL definitions and normalization identities.
-/

namespace InfoGeometry.Core

open InfoGeometry
open scoped BigOperators ENNReal

variable {α : Type*}

@[simp] lemma logDensity_def (P : ProbabilityDist α) (x : α) :
    logDensity P x = Real.log (P x).toReal := rfl

@[simp] lemma surprisal_def (P : ProbabilityDist α) (x : α) :
    surprisal P x = -logDensity P x := rfl

section Fintype

variable [Fintype α]

@[simp] lemma entropy_def (P : ProbabilityDist α) :
    InfoGeometry.entropy P = expectation P (surprisal P) := rfl

@[simp] lemma expectation_const (P : ProbabilityDist α) (c : ℝ) :
    expectation P (fun _ => c) = c := by
  classical
  calc
    expectation P (fun _ => c)
        = ∑ x, (P x).toReal * c := rfl
    _ = (∑ x, (P x).toReal) * c := by
          symm
          simpa using (Finset.sum_mul (s := Finset.univ) (f := fun x => (P x).toReal) (a := c))
    _ = c := by
          have hsum_ennreal : (Finset.univ.sum fun x => P x) = (1 : ℝ≥0∞) := by
            simpa [tsum_fintype] using P.tsum_coe
          have hsum_toReal : (Finset.univ.sum fun x => (P x).toReal) = 1 := by
            have htoReal :
                (Finset.univ.sum fun x => (P x).toReal)
                  = ENNReal.toReal (Finset.univ.sum fun x => P x) := by
              simpa using
                (ENNReal.toReal_sum (s := (Finset.univ)) (f := fun x => P x)
                  (by
                    intro x hx
                    exact P.apply_ne_top x)).symm
            simpa [hsum_ennreal] using htoReal
          simp [hsum_toReal]

@[simp] lemma expectation_zero (P : ProbabilityDist α) :
    expectation P (fun _ => (0 : ℝ)) = 0 := by
  simp [expectation_const]

@[simp] lemma expectation_one (P : ProbabilityDist α) :
    expectation P (fun _ => (1 : ℝ)) = 1 := by
  simp [expectation_const]

end Fintype

section Measurable

variable [MeasurableSpace α]

@[simp] lemma klDiv_def (P Q : ProbabilityDist α) :
    InfoGeometry.KL.kl_div P.toMeasure Q.toMeasure = InfoGeometry.fin_kl_div P Q := rfl

@[simp] lemma klDiv_self (P : ProbabilityDist α) :
    InfoGeometry.KL.kl_div P.toMeasure P.toMeasure = 0 :=
  InfoGeometry.KL.klDiv_self P.toMeasure

lemma klDiv_eq_zero_iff_toMeasure_eq
    (P Q : ProbabilityDist α) :
    InfoGeometry.KL.kl_div P.toMeasure Q.toMeasure = 0 ↔ P.toMeasure = Q.toMeasure := by
  simpa using (InfoGeometry.KL.klDiv_eq_zero_iff (μ := P.toMeasure) (ν := Q.toMeasure))

@[simp] lemma fin_kl_div_self (P : ProbabilityDist α) :
    InfoGeometry.fin_kl_div P P = 0 := by
  rw [← klDiv_def]
  exact klDiv_self (P := P)

lemma fin_kl_div_eq_zero_iff_toMeasure_eq
    (P Q : ProbabilityDist α) :
    InfoGeometry.fin_kl_div P Q = 0 ↔ P.toMeasure = Q.toMeasure := by
  rw [← klDiv_def]
  exact klDiv_eq_zero_iff_toMeasure_eq (P := P) (Q := Q)

end Measurable

end InfoGeometry.Core
