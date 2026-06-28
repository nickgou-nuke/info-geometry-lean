theory WheelerComplexity
  imports Main
begin

text \<open>
  Formalization of Wheeler's 'It from Bit' complexity generation.
  We define a locale containing an initial state, a deterministic transition 
  function, and a complexity weighting function.
\<close>

locale cosmological_complexity =
  fixes init_state :: "'s"
    and transition :: "'s \<Rightarrow> 's"
    and complexity :: "'s \<Rightarrow> nat"
begin

text \<open>Recursive function to compute the state at time n.\<close>
primrec state_at :: "nat \<Rightarrow> 's" where
  "state_at 0 = init_state"
| "state_at (Suc n) = transition (state_at n)"

text \<open>Definition of a strictly expansive transition function.\<close>
definition strictly_expansive :: "bool" where
  "strictly_expansive \<equiv> \<forall>s. complexity s < complexity (transition s)"

text \<open>Step-wise complexity growth.\<close>
lemma complexity_grows_step:
  assumes "strictly_expansive"
  shows "complexity (state_at n) < complexity (state_at (Suc n))"
  using assms unfolding strictly_expansive_def by simp

text \<open>Monotonic growth of complexity over time.\<close>
lemma complexity_monotonic:
  assumes "strictly_expansive"
  assumes "n < m"
  shows "complexity (state_at n) < complexity (state_at m)"
using assms(2)
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case
  proof (cases "n = m")
    case True
    then show ?thesis using assms(1) complexity_grows_step by simp
  next
    case False
    with Suc.prems have "n < m" by simp
    then have "complexity (state_at n) < complexity (state_at m)" by (rule Suc.IH)
    also have "\<dots> < complexity (state_at (Suc m))"
      using assms(1) complexity_grows_step by simp
    finally show ?thesis .
  qed
qed

text \<open>Non-strict monotonicity for non-strict time inequalities.\<close>
lemma complexity_monotonic_le:
  assumes "strictly_expansive"
  assumes "n \<le> m"
  shows "complexity (state_at n) \<le> complexity (state_at m)"
  by (metis assms(1) assms(2) complexity_monotonic less_imp_le order_class.le_less_linear)

end

end
