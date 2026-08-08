theory KoroteevZeitlin
imports Complex_Main
begin

record QuiverVariety =
  vertices :: "nat list"
  framing :: "nat list"

consts
  K_theory_ring :: "QuiverVariety \<Rightarrow> 'a set"
  is_3d_mirror_dual :: "QuiverVariety \<Rightarrow> QuiverVariety \<Rightarrow> bool"

axiomatization where
  mirror_symmetry_iso: "is_3d_mirror_dual X Y \<Longrightarrow> K_theory_ring X = K_theory_ring Y"

end
