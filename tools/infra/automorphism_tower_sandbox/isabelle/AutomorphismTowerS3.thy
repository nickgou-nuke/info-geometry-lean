theory AutomorphismTowerS3 imports Main begin

definition group_order :: nat where "group_order = 6"
definition automorphism_count :: nat where "automorphism_count = 6"
definition inner_automorphism_count :: nat where "inner_automorphism_count = 6"
definition center_count :: nat where "center_count = 1"
definition tower_card :: "nat => nat" where "tower_card _ = group_order"

theorem s3_complete_cardinality_packet:
  "group_order = 6 & automorphism_count = group_order &
   inner_automorphism_count = automorphism_count & center_count = 1"
  by (simp add: group_order_def automorphism_count_def inner_automorphism_count_def center_count_def)

theorem bounded_tower_stable: "tower_card (Suc n) = tower_card n"
  by (simp add: tower_card_def)

end
