theory VarlamovKleinSpectral
  imports Complex_Main
begin

definition tripotent :: "int => bool" where
  "tripotent d \<longleftrightarrow> d^3 = d"

lemma tripotent_roots:
  "tripotent d \<longleftrightarrow> d = 0 \<or> d = 1 \<or> d = -1"
proof
  assume h : "tripotent d"
  have "d * (d - 1) * (d + 1) = 0"
    using h by (simp add: tripotent_def power3_eq_cube algebra_simps)
  then show "d = 0 \<or> d = 1 \<or> d = -1"
    by auto
next
  assume "d = 0 \<or> d = 1 \<or> d = -1"
  then show "tripotent d"
    by (auto simp: tripotent_def)
qed

definition su5AdjointDim :: nat where "su5AdjointDim = 24"
definition spinorDim :: nat where "spinorDim = 32"
definition varlamovEven :: nat where "varlamovEven = 1 + 10 + 5"
definition varlamovOdd :: nat where "varlamovOdd = 5 + 10 + 1"
definition weylA4Order :: nat where "weylA4Order = 120"
definition mobiusGroupOrder :: nat where "mobiusGroupOrder = 2"
definition wittenMoebiusIndex :: int where
  "wittenMoebiusIndex = int varlamovEven - int varlamovOdd"
definition mobiusTwist :: "int => int" where
  "mobiusTwist k = -k"

datatype brillouin_mode = Mode int

definition kleinQuotient :: "brillouin_mode => brillouin_mode => bool" where
  "kleinQuotient m1 m2 =
    (case (m1, m2) of (Mode k1, Mode k2) => k1 = k2 \<or> k1 = mobiusTwist k2)"

lemma varlamov_sum:
  "varlamovEven = 16 \<and> varlamovOdd = 16 \<and>
   varlamovEven + varlamovOdd = spinorDim \<and> wittenMoebiusIndex = 0"
  by (simp add: varlamovEven_def varlamovOdd_def spinorDim_def wittenMoebiusIndex_def)

lemma su5_weyl_certificates:
  "su5AdjointDim = 24 \<and> weylA4Order = 120 \<and> mobiusGroupOrder = 2"
  by (simp add: su5AdjointDim_def weylA4Order_def mobiusGroupOrder_def)

lemma mobius_involutive:
  "mobiusTwist (mobiusTwist k) = k"
  by (simp add: mobiusTwist_def)

lemma klein_refl: "kleinQuotient m m"
  by (cases m) (simp add: kleinQuotient_def)

lemma klein_symm: "kleinQuotient m1 m2 \<Longrightarrow> kleinQuotient m2 m1"
  by (cases m1; cases m2) (auto simp: kleinQuotient_def mobiusTwist_def)

lemma klein_trans:
  "\<lbrakk>kleinQuotient m1 m2; kleinQuotient m2 m3\<rbrakk> \<Longrightarrow> kleinQuotient m1 m3"
  by (cases m1; cases m2; cases m3) (auto simp: kleinQuotient_def mobiusTwist_def)

theorem varlamov_klein_spectral_kernel:
  "su5AdjointDim = 24 \<and> spinorDim = 32 \<and> weylA4Order = 120 \<and> mobiusGroupOrder = 2 \<and>
   varlamovEven = 16 \<and> varlamovOdd = 16 \<and>
   varlamovEven + varlamovOdd = spinorDim \<and> wittenMoebiusIndex = 0 \<and>
   (\<forall> k. mobiusTwist (mobiusTwist k) = k) \<and>
   (\<forall> d. tripotent d \<longleftrightarrow> d = 0 \<or> d = 1 \<or> d = -1)"
  using tripotent_roots
  by (simp add: su5AdjointDim_def spinorDim_def weylA4Order_def mobiusGroupOrder_def
      varlamovEven_def varlamovOdd_def wittenMoebiusIndex_def mobiusTwist_def)

end
