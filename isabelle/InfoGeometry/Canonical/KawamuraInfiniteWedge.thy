theory KawamuraInfiniteWedge
  imports Main
begin

section \<open>Kawamura's Infinite Wedge and Recursive Fermion System\<close>

text \<open>
  Following Katsunori Kawamura, we construct the branching functions 
  on the space of Maya diagrams which give rise to the infinite wedge 
  representation of the CAR algebra and its extension to the Cuntz algebra O2.
\<close>

type_synonym maya_index = int

definition vacuum :: "maya_index set" where
  "vacuum = {j. j \<le> 0}"

definition dual_vacuum :: "maya_index set" where
  "dual_vacuum = {j. j \<ge> 1}"

definition is_maya :: "maya_index set \<Rightarrow> bool" where
  "is_maya S \<longleftrightarrow> finite ((S - vacuum) \<union> (vacuum - S))"

definition is_dual_maya :: "maya_index set \<Rightarrow> bool" where
  "is_dual_maya S \<longleftrightarrow> finite ((S - dual_vacuum) \<union> (dual_vacuum - S))"

subsection \<open>Branching Functions\<close>

definition s_plus :: "maya_index set \<Rightarrow> maya_index set" where
  "s_plus S = S \<inter> {j. j \<ge> 1}"

definition s_minus :: "maya_index set \<Rightarrow> maya_index set" where
  "s_minus S = S \<inter> {j. j \<le> 0}"

definition shift_plus :: "maya_index set \<Rightarrow> maya_index set" where
  "shift_plus S = {j + 1 | j. j \<in> S}"

definition negate_index :: "maya_index set \<Rightarrow> maya_index set" where
  "negate_index S = {1 - j | j. j \<in> S}"

definition g1 :: "maya_index set \<Rightarrow> maya_index set" where
  "g1 S = negate_index (shift_plus (s_plus S) \<union> (s_minus S) \<union> {1})"

definition g2 :: "maya_index set \<Rightarrow> maya_index set" where
  "g2 S = negate_index (shift_plus (s_plus S) \<union> (s_minus S))"

subsection \<open>Finiteness Helper Lemmas\<close>

text \<open>The "particles" (elements \<ge> 1 in S) are finite for a Maya diagram.\<close>

lemma maya_particles_finite:
  assumes "is_maya S"
  shows "finite (S \<inter> {j. j \<ge> 1})"
proof -
  have "S \<inter> {j. j \<ge> (1::int)} \<subseteq> S - vacuum"
    unfolding vacuum_def by auto
  moreover have "S - vacuum \<subseteq> (S - vacuum) \<union> (vacuum - S)"
    by auto
  moreover have "finite ((S - vacuum) \<union> (vacuum - S))"
    using assms unfolding is_maya_def by auto
  ultimately show ?thesis
    using finite_subset by blast
qed

text \<open>The "holes" (elements \<le> 0 not in S) are finite for a Maya diagram.\<close>

lemma maya_holes_finite:
  assumes "is_maya S"
  shows "finite ({j. j \<le> (0::int)} - S)"
proof -
  have "{j. j \<le> (0::int)} - S \<subseteq> vacuum - S"
    unfolding vacuum_def by auto
  moreover have "vacuum - S \<subseteq> (S - vacuum) \<union> (vacuum - S)"
    by auto
  moreover have "finite ((S - vacuum) \<union> (vacuum - S))"
    using assms unfolding is_maya_def by auto
  ultimately show ?thesis
    using finite_subset by blast
qed

text \<open>@{term shift_plus} is the image of @{term "(+) 1"}, preserving finiteness.\<close>

lemma shift_plus_eq_image:
  "shift_plus A = (\<lambda>j. j + 1) ` A"
  unfolding shift_plus_def by auto

lemma shift_plus_finite:
  assumes "finite A"
  shows "finite (shift_plus A)"
  unfolding shift_plus_eq_image using assms by auto

text \<open>@{term negate_index} is the image of @{term "\<lambda>j. 1 - j"}, preserving finiteness.\<close>

lemma negate_index_eq_image:
  "negate_index A = (\<lambda>j. 1 - j) ` A"
  unfolding negate_index_def by auto

lemma negate_index_finite:
  assumes "finite A"
  shows "finite (negate_index A)"
  unfolding negate_index_eq_image using assms by auto

lemma s_plus_finite:
  assumes "is_maya S"
  shows "finite (s_plus S)"
  unfolding s_plus_def using maya_particles_finite[OF assms] by auto

subsection \<open>Thermodynamic Limit Colimit Properties\<close>

text \<open>
  The branching functions g1 and g2 map Maya diagrams to Dual Maya diagrams,
  implementing the Z2 symmetry breaking of the Cuntz algebra over the Fermi sea.
\<close>

text \<open>
  Proof strategy for g2: We show that the symmetric difference 
  @{term "(g2 S - dual_vacuum) \<union> (dual_vacuum - g2 S)"} is a subset of a finite set.

  Part 1: Elements in @{term "g2 S"} but not in @{term dual_vacuum} (i.e. elements \<le> 0)
  come from @{term "negate_index (shift_plus (s_plus S))"}, which is finite since
  @{term "s_plus S"} is finite.

  Part 2: Elements in @{term dual_vacuum} but not in @{term "g2 S"} (i.e. elements \<ge> 1 
  not hit by the branching) correspond bijectively to "holes" 
  @{term "{j. j \<le> 0} - S"}, which is finite.
\<close>

lemma g2_maps_maya_to_dual:
  assumes "is_maya S"
  shows "is_dual_maya (g2 S)"
  unfolding is_dual_maya_def
proof (rule finite_subset)
  let ?particles = "negate_index (shift_plus (s_plus S))"
  let ?holes_img = "(\<lambda>j. 1 - j) ` ({j. j \<le> (0::int)} - S)"
  show "finite (?particles \<union> ?holes_img)"
  proof (intro finite_UnI)
    show "finite ?particles"
      by (rule negate_index_finite[OF shift_plus_finite[OF s_plus_finite[OF assms]]])
    show "finite ?holes_img"
      using maya_holes_finite[OF assms] by auto
  qed
  show "(g2 S - dual_vacuum) \<union> (dual_vacuum - g2 S) \<subseteq> ?particles \<union> ?holes_img"
  proof (rule subsetI)
    fix j :: maya_index
    assume "j \<in> (g2 S - dual_vacuum) \<union> (dual_vacuum - g2 S)"
    then consider (a) "j \<in> g2 S" "j \<notin> dual_vacuum" | (b) "j \<in> dual_vacuum" "j \<notin> g2 S"
      by auto
    then show "j \<in> ?particles \<union> ?holes_img"
    proof cases
      case a
      \<comment> \<open>j \<in> g2 S but j \<notin> dual_vacuum, so j < 1\<close>
      from a(2) have hj: "j < 1" unfolding dual_vacuum_def by auto
      from a(1) obtain i where hi: "i \<in> shift_plus (s_plus S) \<union> s_minus S" "j = 1 - i"
        unfolding g2_def negate_index_def by auto
      from hi(1) consider (sp) "i \<in> shift_plus (s_plus S)" | (sm) "i \<in> s_minus S"
        by auto
      then show ?thesis
      proof cases
        case sp
        have "j \<in> ?particles"
          unfolding negate_index_def using sp hi(2) by auto
        then show ?thesis by auto
      next
        case sm
        \<comment> \<open>i \<in> S \<inter> {j. j \<le> 0}, so i \<le> 0, so 1-i \<ge> 1, contradicting j < 1\<close>
        from sm have "i \<le> 0" unfolding s_minus_def by auto
        with hi(2) hj show ?thesis by auto
      qed
    next
      case b
      \<comment> \<open>j \<in> dual_vacuum but j \<notin> g2 S, so j \<ge> 1\<close>
      from b(1) have hj: "j \<ge> 1" unfolding dual_vacuum_def by auto
      \<comment> \<open>1-j \<le> 0 and 1-j \<notin> S (otherwise j would be in g2 S via negate_index of s_minus)\<close>
      have h1j_le: "1 - j \<le> 0" using hj by auto
      have h1j_notin: "1 - j \<notin> S"
      proof
        assume h: "1 - j \<in> S"
        have "1 - j \<in> s_minus S" unfolding s_minus_def using h h1j_le by auto
        then have "j \<in> negate_index (shift_plus (s_plus S) \<union> s_minus S)"
          unfolding negate_index_def by force
        then have "j \<in> g2 S" unfolding g2_def by auto
        with b(2) show False by auto
      qed
      have "1 - j \<in> {j. j \<le> (0::int)} - S" using h1j_le h1j_notin by auto
      hence "1 - (1 - j) \<in> (\<lambda>j. 1 - j) ` ({j. j \<le> (0::int)} - S)" by (rule imageI)
      then have "j \<in> ?holes_img" by simp
      then show ?thesis by auto
    qed
  qed
qed

lemma g1_maps_maya_to_dual:
  assumes "is_maya S"
  shows "is_dual_maya (g1 S)"
  unfolding is_dual_maya_def
proof (rule finite_subset)
  let ?particles = "negate_index (shift_plus (s_plus S))"
  let ?zero = "{0::int}"
  let ?holes_img = "(\<lambda>j. 1 - j) ` ({j. j \<le> (0::int)} - S)"
  show "finite (?particles \<union> ?zero \<union> ?holes_img)"
  proof (intro finite_UnI)
    show "finite ?particles"
      by (rule negate_index_finite[OF shift_plus_finite[OF s_plus_finite[OF assms]]])
    show "finite ?zero" by auto
    show "finite ?holes_img"
      using maya_holes_finite[OF assms] by auto
  qed
  show "(g1 S - dual_vacuum) \<union> (dual_vacuum - g1 S) \<subseteq> ?particles \<union> ?zero \<union> ?holes_img"
  proof (rule subsetI)
    fix j :: maya_index
    assume "j \<in> (g1 S - dual_vacuum) \<union> (dual_vacuum - g1 S)"
    then consider (a) "j \<in> g1 S" "j \<notin> dual_vacuum" | (b) "j \<in> dual_vacuum" "j \<notin> g1 S"
      by auto
    then show "j \<in> ?particles \<union> ?zero \<union> ?holes_img"
    proof cases
      case a
      from a(2) have hj: "j < 1" unfolding dual_vacuum_def by auto
      from a(1) obtain i where hi: "i \<in> shift_plus (s_plus S) \<union> s_minus S \<union> {1}" "j = 1 - i"
        unfolding g1_def negate_index_def by auto
      from hi(1) consider
          (sp) "i \<in> shift_plus (s_plus S)"
        | (sm) "i \<in> s_minus S"
        | (one) "i = 1"
        by auto
      then show ?thesis
      proof cases
        case sp
        have "j \<in> ?particles"
          unfolding negate_index_def using sp hi(2) by auto
        then show ?thesis by auto
      next
        case sm
        from sm have "i \<le> 0" unfolding s_minus_def by auto
        with hi(2) hj show ?thesis by auto
      next
        case one
        with hi(2) have "j = 0" by auto
        then show ?thesis by auto
      qed
    next
      case b
      from b(1) have hj: "j \<ge> 1" unfolding dual_vacuum_def by auto
      have h1j_le: "1 - j \<le> 0" using hj by auto
      have h1j_notin: "1 - j \<notin> S"
      proof
        assume h: "1 - j \<in> S"
        have "1 - j \<in> s_minus S" unfolding s_minus_def using h h1j_le by auto
        then have "j \<in> negate_index (shift_plus (s_plus S) \<union> s_minus S \<union> {1})"
          unfolding negate_index_def by force
        then have "j \<in> g1 S" unfolding g1_def by auto
        with b(2) show False by auto
      qed
      have "1 - j \<in> {j. j \<le> (0::int)} - S" using h1j_le h1j_notin by auto
      hence "1 - (1 - j) \<in> (\<lambda>j. 1 - j) ` ({j. j \<le> (0::int)} - S)" by (rule imageI)
      then have "j \<in> ?holes_img" by simp
      then show ?thesis by auto
    qed
  qed
qed

lemma g1_g2_ranges_disjoint:
  shows "g1 S1 \<noteq> g2 S2"
proof
  assume "g1 S1 = g2 S2"
  hence "0 \<in> g2 S2"
  proof -
    have "0 \<in> g1 S1"
      unfolding g1_def negate_index_def by force
    thus ?thesis using \<open>g1 S1 = g2 S2\<close> by simp
  qed
  then obtain i where "i \<in> shift_plus (s_plus S2) \<union> s_minus S2" and "0 = 1 - i"
    unfolding g2_def negate_index_def by auto
  hence "i = 1" by simp
  with \<open>i \<in> shift_plus (s_plus S2) \<union> s_minus S2\<close>
  consider (sp) "i \<in> shift_plus (s_plus S2)" | (sm) "i \<in> s_minus S2" by auto
  thus False
  proof cases
    case sp
    then obtain j where "j \<in> s_plus S2" and "i = j + 1"
      unfolding shift_plus_def by auto
    hence "j \<ge> 1" unfolding s_plus_def by auto
    hence "i \<ge> 2" using \<open>i = j + 1\<close> by simp
    thus False using \<open>i = 1\<close> by simp
  next
    case sm
    hence "i \<le> 0" unfolding s_minus_def by auto
    thus False using \<open>i = 1\<close> by simp
  qed
qed

subsection \<open>Isometry Properties (Left Inverses)\<close>

definition g_pullback :: "maya_index set \<Rightarrow> maya_index set" where
  "g_pullback B = (B \<inter> {j. j \<le> 0}) \<union> {j - 1 | j. j \<in> B \<and> j \<ge> 2}"

definition g1_inverse :: "maya_index set \<Rightarrow> maya_index set" where
  "g1_inverse A = g_pullback (negate_index A)"

definition g2_inverse :: "maya_index set \<Rightarrow> maya_index set" where
  "g2_inverse A = g_pullback (negate_index A)"

lemma negate_index_negate [simp]:
  "negate_index (negate_index S) = S"
proof (rule set_eqI)
  fix x
  show "(x \<in> negate_index (negate_index S)) = (x \<in> S)"
    unfolding negate_index_def by force
qed

lemma s_plus_s_minus_union:
  "(s_plus S) \<union> (s_minus S) = S"
  unfolding s_plus_def s_minus_def by auto

lemma g2_isometry:
  shows "g2_inverse (g2 S) = S"
proof -
  have h_neg: "negate_index (g2 S) = shift_plus (s_plus S) \<union> s_minus S"
    unfolding g2_def by simp
  hence "g2_inverse (g2 S) = g_pullback (shift_plus (s_plus S) \<union> s_minus S)"
    unfolding g2_inverse_def by simp
  also have "... = S"
    unfolding g_pullback_def
  proof (rule set_eqI)
    fix k :: maya_index
    let ?B = "shift_plus (s_plus S) \<union> s_minus S"
    show "(k \<in> ?B \<inter> {j. j \<le> 0} \<union> {j - 1 | j. j \<in> ?B \<and> j \<ge> 2}) = (k \<in> S)"
    proof
      assume "k \<in> ?B \<inter> {j. j \<le> 0} \<union> {j - 1 | j. j \<in> ?B \<and> j \<ge> 2}"
      then consider (a) "k \<in> ?B" "k \<le> 0" | (b) "k \<in> {j - 1 | j. j \<in> ?B \<and> j \<ge> 2}"
        by auto
      then show "k \<in> S"
      proof cases
        case a
        from a(1) consider (sp) "k \<in> shift_plus (s_plus S)" | (sm) "k \<in> s_minus S"
          by auto
        then show ?thesis
        proof cases
          case sp
          then obtain i where "i \<in> s_plus S" "k = i + 1"
            unfolding shift_plus_def by auto
          hence "i \<ge> 1" unfolding s_plus_def by auto
          hence "k \<ge> 2" using \<open>k = i + 1\<close> by simp
          with a(2) show ?thesis by simp
        next
          case sm
          then show ?thesis unfolding s_minus_def by auto
        qed
      next
        case b
        then obtain j where hj: "j \<in> ?B" "j \<ge> 2" "k = j - 1" by auto
        from hj(1) consider (sp) "j \<in> shift_plus (s_plus S)" | (sm) "j \<in> s_minus S"
          by auto
        then show ?thesis
        proof cases
          case sp
          then obtain i where "i \<in> s_plus S" "j = i + 1"
            unfolding shift_plus_def by auto
          hence "k = i" using hj(3) by simp
          with \<open>i \<in> s_plus S\<close> show ?thesis unfolding s_plus_def by auto
        next
          case sm
          hence "j \<le> 0" unfolding s_minus_def by auto
          with hj(2) show ?thesis by simp
        qed
      qed
    next
      assume "k \<in> S"
      show "k \<in> ?B \<inter> {j. j \<le> 0} \<union> {j - 1 | j. j \<in> ?B \<and> j \<ge> 2}"
      proof (cases "k \<le> 0")
        case True
        hence "k \<in> s_minus S" unfolding s_minus_def using \<open>k \<in> S\<close> by auto
        hence "k \<in> ?B" by auto
        with True show ?thesis by force
      next
        case False
        hence "k \<ge> 1" by simp
        hence "k \<in> s_plus S" unfolding s_plus_def using \<open>k \<in> S\<close> by auto
        hence "k + 1 \<in> shift_plus (s_plus S)" unfolding shift_plus_def by auto
        hence hj: "k + 1 \<in> ?B" by auto
        have hj2: "k + 1 \<ge> 2" using \<open>k \<ge> 1\<close> by simp
        have "k = (k + 1) - 1" by simp
        with hj hj2 show ?thesis by force
      qed
    qed
  qed
  finally show ?thesis .
qed

lemma g1_isometry:
  shows "g1_inverse (g1 S) = S"
proof -
  have h_neg: "negate_index (g1 S) = shift_plus (s_plus S) \<union> s_minus S \<union> {1}"
    unfolding g1_def by simp
  hence "g1_inverse (g1 S) = g_pullback (shift_plus (s_plus S) \<union> s_minus S \<union> {1})"
    unfolding g1_inverse_def by simp
  also have "... = S"
    unfolding g_pullback_def
  proof (rule set_eqI)
    fix k :: maya_index
    let ?B = "shift_plus (s_plus S) \<union> s_minus S \<union> {1}"
    show "(k \<in> ?B \<inter> {j. j \<le> 0} \<union> {j - 1 | j. j \<in> ?B \<and> j \<ge> 2}) = (k \<in> S)"
    proof
      assume "k \<in> ?B \<inter> {j. j \<le> 0} \<union> {j - 1 | j. j \<in> ?B \<and> j \<ge> 2}"
      then consider (a) "k \<in> ?B" "k \<le> 0" | (b) "k \<in> {j - 1 | j. j \<in> ?B \<and> j \<ge> 2}"
        by auto
      then show "k \<in> S"
      proof cases
        case a
        from a(1) consider (sp) "k \<in> shift_plus (s_plus S)" | (sm) "k \<in> s_minus S" | (one) "k = 1"
          by auto
        then show ?thesis
        proof cases
          case sp
          then obtain i where "i \<in> s_plus S" "k = i + 1"
            unfolding shift_plus_def by auto
          hence "i \<ge> 1" unfolding s_plus_def by auto
          hence "k \<ge> 2" using \<open>k = i + 1\<close> by simp
          with a(2) show ?thesis by simp
        next
          case sm
          then show ?thesis unfolding s_minus_def by auto
        next
          case one
          with a(2) show ?thesis by simp
        qed
      next
        case b
        then obtain j where hj: "j \<in> ?B" "j \<ge> 2" "k = j - 1" by auto
        from hj(1) consider (sp) "j \<in> shift_plus (s_plus S)" | (sm) "j \<in> s_minus S" | (one) "j = 1"
          by auto
        then show ?thesis
        proof cases
          case sp
          then obtain i where "i \<in> s_plus S" "j = i + 1"
            unfolding shift_plus_def by auto
          hence "k = i" using hj(3) by simp
          with \<open>i \<in> s_plus S\<close> show ?thesis unfolding s_plus_def by auto
        next
          case sm
          hence "j \<le> 0" unfolding s_minus_def by auto
          with hj(2) show ?thesis by simp
        next
          case one
          with hj(2) show ?thesis by simp
        qed
      qed
    next
      assume "k \<in> S"
      show "k \<in> ?B \<inter> {j. j \<le> 0} \<union> {j - 1 | j. j \<in> ?B \<and> j \<ge> 2}"
      proof (cases "k \<le> 0")
        case True
        hence "k \<in> s_minus S" unfolding s_minus_def using \<open>k \<in> S\<close> by auto
        hence "k \<in> ?B" by auto
        with True show ?thesis by force
      next
        case False
        hence "k \<ge> 1" by simp
        hence "k \<in> s_plus S" unfolding s_plus_def using \<open>k \<in> S\<close> by auto
        hence "k + 1 \<in> shift_plus (s_plus S)" unfolding shift_plus_def by auto
        hence hj: "k + 1 \<in> ?B" by auto
        have hj2: "k + 1 \<ge> 2" using \<open>k \<ge> 1\<close> by simp
        have "k = (k + 1) - 1" by simp
        with hj hj2 show ?thesis by force
      qed
    qed
  qed
  finally show ?thesis .
qed

end


