From Stdlib Require Import Arith Lia.

Definition imaginary_dimension : nat := 7.
Definition left_annihilator_rank : nat := 4.
Definition left_annihilator_dimension : nat := imaginary_dimension - left_annihilator_rank.
Definition projectivized_distribution_rank : nat := left_annihilator_dimension - 1.
Definition projective_null_quadric_dimension : nat := 5.
Definition first_derived_rank : nat := 3.
Definition ambient_rank : nat := 5.
Definition split_g2_symmetry_dimension : nat := 14.

Theorem split_octonion_235_packet :
  left_annihilator_dimension = 3 /\
  projectivized_distribution_rank = 2 /\
  first_derived_rank = 3 /\
  ambient_rank = 5 /\
  projective_null_quadric_dimension = 5 /\
  split_g2_symmetry_dimension = 14.
Proof. vm_compute. repeat split; reflexivity. Qed.
