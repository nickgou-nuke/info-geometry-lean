theory Vortex_Partition
  imports Main
  "HOL-Library.Factorial"
  "HOL-Library.Power"
  "HOL-Library.Sum_List"
begin

section ‹Vortex partition function symmetry›

(* Factorial as real *)
definition fact_real :: "nat ⇒ real" where
  "fact_real n = (fact n :: real)"

(* Vortex partial sum up to N (inclusive) *)
definition vortex_partial :: "nat ⇒ real ⇒ real ⇒ real ⇒ real" where
  "vortex_partial N q ε₁ ε₂ = (∑ k = 0..n. (q / (ε₁ * ε₂)) ^ k / (fact_real k)^2) where n = N"

lemma vortex_partial_symmetric:
  "vortex_partial N q ε₁ ε₂ = vortex_partial N q ε₂ ε₁"
proof -
  have "vortex_partial N q ε₁ ε₂ = (∑ k = 0..N. (q / (ε₁ * ε₂)) ^ k / (fact_real k)^2)"
    by (simp add: vortex_partial_def)
  also have "... = (∑ k = 0..N. (q / (ε₂ * ε₁)) ^ k / (fact_real k)^2)"
  proof (rule sum.congr)
    fix k assume "k ≤ N"
    have "(q / (ε₁ * ε₂)) ^ k = (q / (ε₂ * ε₁)) ^ k"
    proof -
      have "ε₁ * ε₂ = ε₂ * ε₁" by (ring_ac)
      thus ?thesis by simp
    qed
    thus "(q / (ε₁ * ε₂)) ^ k / (fact_real k)^2 = (q / (ε₂ * ε₁)) ^ k / (fact_real k)^2"
      by simp
  qed
  also have "... = (∑ k = 0..N. (q / (ε₂ * ε₁)) ^ k / (fact_real k)^2)" by simp
  also have " = vortex_partial N q ε₂ ε₁"
    by (simp add: vortex_partial_def)
  finally:)
  finally show ?thesis .
qed

end