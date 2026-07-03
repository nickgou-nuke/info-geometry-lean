theory RealSplitG2Classification imports Main begin

datatype classification_status = NativeGroupEquivalence | CharacteristicZeroDerivationEvidence | OpenDebt

definition current_status :: classification_status where
  "current_status = CharacteristicZeroDerivationEvidence"
definition derivation_rows :: nat where "derivation_rows = 512"
definition derivation_cols :: nat where "derivation_cols = 64"
definition derivation_rank :: nat where "derivation_rank = 50"
definition derivation_nullity :: nat where "derivation_nullity = 14"
definition g2_rank :: nat where "g2_rank = 2"
definition g2_roots :: nat where "g2_roots = 12"
definition g2_positive_roots :: nat where "g2_positive_roots = 6"
definition g2_weyl_order :: nat where "g2_weyl_order = 12"

lemma derivation_rank_nullity_packet:
  "derivation_rows = 64 * 8 \<and>
   derivation_rank + derivation_nullity = derivation_cols \<and>
   derivation_nullity = 14"
  by (simp add: derivation_rows_def derivation_rank_def derivation_nullity_def derivation_cols_def)

lemma g2_root_weyl_packet:
  "g2_rank = 2 \<and> g2_roots = 12 \<and> g2_positive_roots = 6 \<and>
   g2_weyl_order = 12 \<and> g2_rank + g2_roots = derivation_nullity"
  by (simp add: g2_rank_def g2_roots_def g2_positive_roots_def g2_weyl_order_def derivation_nullity_def)

lemma current_status_not_native_group_equivalence:
  "current_status \<noteq> NativeGroupEquivalence"
  by (simp add: current_status_def)

end
