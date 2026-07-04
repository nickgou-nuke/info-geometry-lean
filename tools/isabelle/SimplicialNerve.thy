theory SimplicialNerve
  imports Main
begin

text \<open>Categories\<close>

locale Category =
  fixes Obj :: "'o set"
    and Hom :: "'o \<Rightarrow> 'o \<Rightarrow> 'm set"
    and Id :: "'o \<Rightarrow> 'm"
    and Comp :: "'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> 'm"
  assumes Id_type: "x \<in> Obj \<Longrightarrow> Id x \<in> Hom x x"
      and Comp_type: "x \<in> Obj \<Longrightarrow> y \<in> Obj \<Longrightarrow> z \<in> Obj \<Longrightarrow>
                      f \<in> Hom x y \<Longrightarrow> g \<in> Hom y z \<Longrightarrow> Comp x y z f g \<in> Hom x z"
      and Comp_assoc: "x \<in> Obj \<Longrightarrow> y \<in> Obj \<Longrightarrow> z \<in> Obj \<Longrightarrow> w \<in> Obj \<Longrightarrow>
                       f \<in> Hom x y \<Longrightarrow> g \<in> Hom y z \<Longrightarrow> h \<in> Hom z w \<Longrightarrow>
                       Comp x z w (Comp x y z f g) h = Comp x y w f (Comp y z w g h)"
      and Comp_Id_left: "x \<in> Obj \<Longrightarrow> y \<in> Obj \<Longrightarrow> f \<in> Hom x y \<Longrightarrow> Comp x x y (Id x) f = f"
      and Comp_Id_right: "x \<in> Obj \<Longrightarrow> y \<in> Obj \<Longrightarrow> f \<in> Hom x y \<Longrightarrow> Comp x y y f (Id y) = f"

text \<open>2-Truncated Simplicial Sets\<close>

locale TruncatedSimplicialSet =
  fixes V :: "'v set"
    and E :: "'e set"
    and T :: "'t set"
    and d0_1 :: "'e \<Rightarrow> 'v"
    and d1_1 :: "'e \<Rightarrow> 'v"
    and d0_2 :: "'t \<Rightarrow> 'e"
    and d1_2 :: "'t \<Rightarrow> 'e"
    and d2_2 :: "'t \<Rightarrow> 'e"
  assumes d0_d1: "\<And>t. t \<in> T \<Longrightarrow> d0_1 (d1_2 t) = d0_1 (d0_2 t)"
      and d0_d2: "\<And>t. t \<in> T \<Longrightarrow> d0_1 (d2_2 t) = d1_1 (d0_2 t)"
      and d1_d2: "\<And>t. t \<in> T \<Longrightarrow> d1_1 (d2_2 t) = d1_1 (d1_2 t)"

text \<open>The Nerve of a Category\<close>

type_synonym ('o, 'm) nerve_edge = "'o \<times> 'o \<times> 'm"
type_synonym ('o, 'm) nerve_triangle = "'o \<times> 'o \<times> 'o \<times> 'm \<times> 'm"

definition (in Category) Nerve_V :: "'o set" where
  "Nerve_V = Obj"

definition (in Category) Nerve_E :: "('o, 'm) nerve_edge set" where
  "Nerve_E = { (x, y, f). x \<in> Obj \<and> y \<in> Obj \<and> f \<in> Hom x y }"

definition (in Category) Nerve_T :: "('o, 'm) nerve_triangle set" where
  "Nerve_T = { (x, y, z, f, g). x \<in> Obj \<and> y \<in> Obj \<and> z \<in> Obj \<and> f \<in> Hom x y \<and> g \<in> Hom y z }"

definition Nerve_d0_1 :: "('o, 'm) nerve_edge \<Rightarrow> 'o" where
  "Nerve_d0_1 = (\<lambda>(x, y, f). y)"

definition Nerve_d1_1 :: "('o, 'm) nerve_edge \<Rightarrow> 'o" where
  "Nerve_d1_1 = (\<lambda>(x, y, f). x)"

definition Nerve_d0_2 :: "('o, 'm) nerve_triangle \<Rightarrow> ('o, 'm) nerve_edge" where
  "Nerve_d0_2 = (\<lambda>(x, y, z, f, g). (y, z, g))"

definition (in Category) Nerve_d1_2 :: "('o, 'm) nerve_triangle \<Rightarrow> ('o, 'm) nerve_edge" where
  "Nerve_d1_2 = (\<lambda>(x, y, z, f, g). (x, z, Comp x y z f g))"

definition Nerve_d2_2 :: "('o, 'm) nerve_triangle \<Rightarrow> ('o, 'm) nerve_edge" where
  "Nerve_d2_2 = (\<lambda>(x, y, z, f, g). (x, y, f))"

text \<open>Verifying that the Nerve generates a Truncated Simplicial Set\<close>

context Category
begin

sublocale TruncatedSimplicialSet
  Nerve_V Nerve_E Nerve_T Nerve_d0_1 Nerve_d1_1 Nerve_d0_2 Nerve_d1_2 Nerve_d2_2
proof
  fix t assume "t \<in> Nerve_T"
  then obtain x y z f g where t_def: "t = (x, y, z, f, g)" and
    "x \<in> Obj" "y \<in> Obj" "z \<in> Obj" "f \<in> Hom x y" "g \<in> Hom y z"
    unfolding Nerve_T_def by auto

  show "Nerve_d0_1 (Nerve_d1_2 t) = Nerve_d0_1 (Nerve_d0_2 t)"
    unfolding t_def Nerve_d1_2_def Nerve_d0_2_def Nerve_d0_1_def by simp

  show "Nerve_d0_1 (Nerve_d2_2 t) = Nerve_d1_1 (Nerve_d0_2 t)"
    unfolding t_def Nerve_d2_2_def Nerve_d0_2_def Nerve_d0_1_def Nerve_d1_1_def by simp

  show "Nerve_d1_1 (Nerve_d2_2 t) = Nerve_d1_1 (Nerve_d1_2 t)"
    unfolding t_def Nerve_d2_2_def Nerve_d1_2_def Nerve_d1_1_def by simp
qed

end

text \<open>Abstract simplicial identity verification (functional form)\<close>

lemma (in TruncatedSimplicialSet) simplicial_identity_d0_d1:
  "t \<in> T \<Longrightarrow> (d0_1 \<circ> d1_2) t = (d0_1 \<circ> d0_2) t"
  by (simp add: d0_d1)

lemma (in TruncatedSimplicialSet) simplicial_identity_d0_d2:
  "t \<in> T \<Longrightarrow> (d0_1 \<circ> d2_2) t = (d1_1 \<circ> d0_2) t"
  by (simp add: d0_d2)

lemma (in TruncatedSimplicialSet) simplicial_identity_d1_d2:
  "t \<in> T \<Longrightarrow> (d1_1 \<circ> d2_2) t = (d1_1 \<circ> d1_2) t"
  by (simp add: d1_d2)

end
