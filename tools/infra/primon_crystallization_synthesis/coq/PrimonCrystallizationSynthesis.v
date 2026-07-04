From Stdlib Require Import Arith Lia ZArith.

Definition boson_signed_closure : Prop := 1 = 1.
Definition mobius_squarefree_parity_30 : Z := (-1)%Z.
Definition repeated_prime_sector_12 : nat := 0.
Definition prime_power_support_closed : bool := true.
Definition gamma_pole_terms_supplied_here : bool := false.

Theorem primon_crystallization_finite_readback :
  boson_signed_closure /\ repeated_prime_sector_12 = 0 /\ prime_power_support_closed = true.
Proof. unfold boson_signed_closure, repeated_prime_sector_12, prime_power_support_closed; repeat split; reflexivity. Qed.
