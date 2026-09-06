import InfoGeometry.Basic

/-!
# Core Entropy

Core entropy/KL definitions and normalization identities.
-/

namespace InfoGeometry.Core

open InfoGeometry

variable {α : Type _} [Fintype α]

@[simp] lemma logDensity_def (P : ProbabilityDist α) (x : α) :
    logDensity P x = Real.log (P.prob x) := rfl

@[simp] lemma surprisal_def (P : ProbabilityDist α) (x : α) :
    surprisal P x = -logDensity P x := rfl

@[simp] lemma entropy_def (P : ProbabilityDist α) :
    entropy P = expectation P (surprisal P) := rfl

@[simp] lemma klDiv_def (P Q : ProbabilityDist α) :
    klDiv P Q = expectation P (fun x => logDensity P x - logDensity Q x) := rfl

lemma expectation_const (P : ProbabilityDist α) (c : ℝ) :
    expectation P (fun _ => c) = c := by
  calc
    expectation P (fun _ => c)
        = ∑ x, P.prob x * c := rfl
    _ = (∑ x, P.prob x) * c := by
          symm
          simpa using (Finset.sum_mul (s := Finset.univ) (f := P.prob) (a := c))
    _ = c := by simp [P.sum_one]

end InfoGeometry.Core
