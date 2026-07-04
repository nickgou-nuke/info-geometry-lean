theory LieBracketLimit
  imports Main
begin

locale Lie_algebra =
  fixes V :: "'a set"
    and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and smul :: "'k \<Rightarrow> 'a \<Rightarrow> 'a"
    and zero :: "'a"
    and br :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes
    closed_add: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> add x y \<in> V"
    and closed_smul: "x \<in> V \<Longrightarrow> smul c x \<in> V"
    and closed_zero: "zero \<in> V"
    and closed_br: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> br x y \<in> V"
    and add_comm: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> add x y = add y x"
    and add_assoc: "\<lbrakk>x \<in> V; y \<in> V; z \<in> V\<rbrakk> \<Longrightarrow> add (add x y) z = add x (add y z)"
    and add_zero: "x \<in> V \<Longrightarrow> add x zero = x"
    and br_add_left: "\<lbrakk>x \<in> V; y \<in> V; z \<in> V\<rbrakk> \<Longrightarrow> br (add x y) z = add (br x z) (br y z)"
    and br_add_right: "\<lbrakk>x \<in> V; y \<in> V; z \<in> V\<rbrakk> \<Longrightarrow> br x (add y z) = add (br x y) (br x z)"
    and br_smul_left: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> br (smul c x) y = smul c (br x y)"
    and br_smul_right: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> br x (smul c y) = smul c (br x y)"
    and br_skew: "x \<in> V \<Longrightarrow> br x x = zero"
    and jacobi: "\<lbrakk>x \<in> V; y \<in> V; z \<in> V\<rbrakk> \<Longrightarrow> add (br x (br y z)) (add (br y (br z x)) (br z (br x y))) = zero"

locale Lie_algebra_directed_system =
  fixes V :: "nat \<Rightarrow> 'a set"
    and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and smul :: "'k \<Rightarrow> 'a \<Rightarrow> 'a"
    and zero :: "'a"
    and br :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes
    inc: "\<And>n. V n \<subseteq> V (Suc n)"
    and is_lie: "\<And>n. Lie_algebra (V n) add smul zero br"
begin

lemma V_mono: "n \<le> m \<Longrightarrow> V n \<subseteq> V m"
proof (induction m)
  case 0
  then have "n = 0" by simp
  then show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases "n = Suc m")
    case True
    then show ?thesis by simp
  next
    case False
    with Suc.prems have "n \<le> m" by simp
    then have "V n \<subseteq> V m" using Suc.IH by simp
    also have "V m \<subseteq> V (Suc m)" using inc by simp
    finally show ?thesis .
  qed
qed

definition V_inf :: "'a set" where
"V_inf = (\<Union>n. V n)"

lemma common_bound2:
  assumes "x \<in> V_inf" "y \<in> V_inf"
  obtains n where "x \<in> V n" "y \<in> V n"
proof -
  from assms obtain n1 n2 where "x \<in> V n1" "y \<in> V n2"
    unfolding V_inf_def by auto
  let ?n = "max n1 n2"
  have "V n1 \<subseteq> V ?n" and "V n2 \<subseteq> V ?n"
    using V_mono by auto
  then have "x \<in> V ?n" "y \<in> V ?n"
    using `x \<in> V n1` `y \<in> V n2` by auto
  thus ?thesis using that by blast
qed

lemma common_bound3:
  assumes "x \<in> V_inf" "y \<in> V_inf" "z \<in> V_inf"
  obtains n where "x \<in> V n" "y \<in> V n" "z \<in> V n"
proof -
  from assms obtain n1 n2 n3 where "x \<in> V n1" "y \<in> V n2" "z \<in> V n3"
    unfolding V_inf_def by auto
  let ?n = "max n1 (max n2 n3)"
  have "V n1 \<subseteq> V ?n" and "V n2 \<subseteq> V ?n" and "V n3 \<subseteq> V ?n"
    using V_mono by auto
  then have "x \<in> V ?n" "y \<in> V ?n" "z \<in> V ?n"
    using `x \<in> V n1` `y \<in> V n2` `z \<in> V n3` by auto
  thus ?thesis using that by blast
qed

theorem colimit_is_Lie_algebra: "Lie_algebra V_inf add smul zero br"
proof (unfold_locales)
  show "zero \<in> V_inf"
  proof -
    have "zero \<in> V 0" using is_lie[of 0] Lie_algebra.closed_zero by blast
    thus ?thesis unfolding V_inf_def by blast
  qed
next
  fix x y assume "x \<in> V_inf" "y \<in> V_inf"
  then obtain n where n: "x \<in> V n" "y \<in> V n" using common_bound2 by blast
  have "add x y \<in> V n" using is_lie[of n] n Lie_algebra.closed_add by blast
  thus "add x y \<in> V_inf" unfolding V_inf_def by auto
next
  fix c x assume "x \<in> V_inf"
  then obtain n where n: "x \<in> V n" unfolding V_inf_def by auto
  have "smul c x \<in> V n" using is_lie[of n] n Lie_algebra.closed_smul by blast
  thus "smul c x \<in> V_inf" unfolding V_inf_def by auto
next
  fix x y assume "x \<in> V_inf" "y \<in> V_inf"
  then obtain n where n: "x \<in> V n" "y \<in> V n" using common_bound2 by blast
  have "br x y \<in> V n" using is_lie[of n] n Lie_algebra.closed_br by blast
  thus "br x y \<in> V_inf" unfolding V_inf_def by auto
next
  fix x y assume "x \<in> V_inf" "y \<in> V_inf"
  then obtain n where n: "x \<in> V n" "y \<in> V n" using common_bound2 by blast
  show "add x y = add y x" using is_lie[of n] n Lie_algebra.add_comm by blast
next
  fix x y z assume "x \<in> V_inf" "y \<in> V_inf" "z \<in> V_inf"
  then obtain n where n: "x \<in> V n" "y \<in> V n" "z \<in> V n" using common_bound3 by blast
  show "add (add x y) z = add x (add y z)" using is_lie[of n] n Lie_algebra.add_assoc by blast
next
  fix x assume "x \<in> V_inf"
  then obtain n where n: "x \<in> V n" unfolding V_inf_def by auto
  show "add x zero = x" using is_lie[of n] n Lie_algebra.add_zero by blast
next
  fix x y z assume "x \<in> V_inf" "y \<in> V_inf" "z \<in> V_inf"
  then obtain n where n: "x \<in> V n" "y \<in> V n" "z \<in> V n" using common_bound3 by blast
  show "br (add x y) z = add (br x z) (br y z)" using is_lie[of n] n Lie_algebra.br_add_left by blast
next
  fix x y z assume "x \<in> V_inf" "y \<in> V_inf" "z \<in> V_inf"
  then obtain n where n: "x \<in> V n" "y \<in> V n" "z \<in> V n" using common_bound3 by blast
  show "br x (add y z) = add (br x y) (br x z)" using is_lie[of n] n Lie_algebra.br_add_right by blast
next
  fix c x y assume "x \<in> V_inf" "y \<in> V_inf"
  then obtain n where n: "x \<in> V n" "y \<in> V n" using common_bound2 by blast
  show "br (smul c x) y = smul c (br x y)" using is_lie[of n] n Lie_algebra.br_smul_left by blast
next
  fix c x y assume "x \<in> V_inf" "y \<in> V_inf"
  then obtain n where n: "x \<in> V n" "y \<in> V n" using common_bound2 by blast
  show "br x (smul c y) = smul c (br x y)" using is_lie[of n] n Lie_algebra.br_smul_right by blast
next
  fix x assume "x \<in> V_inf"
  then obtain n where n: "x \<in> V n" unfolding V_inf_def by auto
  show "br x x = zero" using is_lie[of n] n Lie_algebra.br_skew by blast
next
  fix x y z assume "x \<in> V_inf" "y \<in> V_inf" "z \<in> V_inf"
  then obtain n where n: "x \<in> V n" "y \<in> V n" "z \<in> V n" using common_bound3 by blast
  show "add (br x (br y z)) (add (br y (br z x)) (br z (br x y))) = zero"
    using is_lie[of n] n Lie_algebra.jacobi by blast
qed

end

end
