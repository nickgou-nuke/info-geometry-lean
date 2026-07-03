From Stdlib Require Import Arith Lia.

Definition g2two_order : nat := 12096.
Definition g2two_derived_order : nat := 6048.
Definition pgl3f3_order : nat := 5616.
Definition split_oct_f2_card : nat := 256.

Theorem split_oct_f2_card_eq : split_oct_f2_card = 2 ^ 8.
Proof. vm_compute. reflexivity. Qed.

Theorem g2two_order_formula : g2two_order = 2 ^ 6 * (2 ^ 6 - 1) * (2 ^ 2 - 1).
Proof. vm_compute. reflexivity. Qed.

Theorem derived_half_order : g2two_derived_order * 2 = g2two_order.
Proof. vm_compute. reflexivity. Qed.

Theorem pgl3f3_order_ne_g2two_order : pgl3f3_order <> g2two_order.
Proof. vm_compute. discriminate. Qed.

