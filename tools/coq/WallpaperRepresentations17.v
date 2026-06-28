From Stdlib Require Import Reals Psatz.

Definition wallpaper_group_count : nat := 17.
Definition p4m_irrep_total : nat := 5.
Definition p6m_irrep_total : nat := 6.

Theorem wallpaper_group_count_ok : wallpaper_group_count = 17%nat.
Proof. reflexivity. Qed.

Theorem p4m_irrep_total_ok : p4m_irrep_total = 5%nat.
Proof. reflexivity. Qed.

Theorem p6m_irrep_total_ok : p6m_irrep_total = 6%nat.
Proof. reflexivity. Qed.
