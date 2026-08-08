theory ShimuraKTheory
  imports Main
begin

typedecl AdelicShimuraClass
typedecl KTheory

consts
  k_theoretic_direct_image :: "AdelicShimuraClass \<Rightarrow> KTheory"

lemma direct_image_mapping:
  "k_theoretic_direct_image x = k_theoretic_direct_image x"
  by simp

end
