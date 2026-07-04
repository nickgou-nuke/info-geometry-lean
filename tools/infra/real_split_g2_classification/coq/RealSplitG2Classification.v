From Stdlib Require Import Arith Lia.

Inductive classification_status :=
| native_group_equivalence
| characteristic_zero_derivation_evidence
| open_debt.

Definition current_status : classification_status := characteristic_zero_derivation_evidence.
Definition derivation_rows : nat := 512.
Definition derivation_cols : nat := 64.
Definition derivation_rank : nat := 50.
Definition derivation_nullity : nat := 14.
Definition norm_positive : nat := 4.
Definition norm_negative : nat := 4.
Definition norm_zero : nat := 0.
Definition norm_multiplicative_symbolic : bool := true.
Definition g2_rank : nat := 2.
Definition g2_roots : nat := 12.
Definition g2_positive_roots : nat := 6.
Definition g2_weyl_order : nat := 12.

Theorem derivation_rank_nullity_packet :
  derivation_rows = 64 * 8 /\
  derivation_rank + derivation_nullity = derivation_cols /\
  derivation_nullity = 14.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem g2_root_weyl_packet :
  g2_rank = 2 /\ g2_roots = 12 /\ g2_positive_roots = 6 /\ g2_weyl_order = 12 /\
  g2_rank + g2_roots = derivation_nullity.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem split_norm_packet :
  norm_positive = 4 /\ norm_negative = 4 /\ norm_zero = 0 /\
  norm_positive + norm_negative + norm_zero = 8 /\
  norm_multiplicative_symbolic = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem current_status_not_native_group_equivalence :
  current_status <> native_group_equivalence.
Proof. vm_compute. discriminate. Qed.
