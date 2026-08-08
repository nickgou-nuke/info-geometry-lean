From Stdlib Require Import Arith Lia List String.
Import ListNotations.
Open Scope nat_scope.
Open Scope string_scope.

Definition dlaDimSYK (n : nat) : nat := 2^(2*n - 1) - 2.
Definition dlaDimSK (L : nat) : nat := 2*(4^(L-1)-1).
Definition poolSizeSK (L : nat) : nat := L*(L-1).
Definition poolSizeSYK (n : nat) : nat := n + 3*n*(n-1)/2.
Definition majoranaCount (n : nat) : nat := 2*n.
Definition hilbertDim (n : nat) : nat := 2^n.
Definition matrixAlgDim (n : nat) : nat := hilbertDim n * hilbertDim n.
Definition clBalancedDim (n : nat) : nat := 2^(2*n).
Definition cl55MatrixDim : nat := 32*32.

Inductive Concept := Quantum_SK_Model | SYK_Majorana_Model | Symmetry_Adapted_Operator_Pool | Jordan_Wigner_Clifford_Embedding | Pin55_Spinor_Block | Dense_Dynamical_Lie_Algebra.
Inductive Edge := has_pool_size | has_dla_dimension | embeds_by | realizes_cl55_block | scales_as.
Definition edgeHolds a e b :=
  match a,e,b with
  | Quantum_SK_Model, has_pool_size, Symmetry_Adapted_Operator_Pool => true
  | SYK_Majorana_Model, has_pool_size, Symmetry_Adapted_Operator_Pool => true
  | SYK_Majorana_Model, embeds_by, Jordan_Wigner_Clifford_Embedding => true
  | Jordan_Wigner_Clifford_Embedding, realizes_cl55_block, Pin55_Spinor_Block => true
  | SYK_Majorana_Model, has_dla_dimension, Dense_Dynamical_Lie_Algebra => true
  | Dense_Dynamical_Lie_Algebra, scales_as, SYK_Majorana_Model => true
  | _,_,_ => false
  end.

Theorem sk_syk_kernel :
  dlaDimSYK 4 = 126 /\
  dlaDimSK 8 = 32766 /\
  poolSizeSK 8 = 56 /\
  poolSizeSYK 4 = 22 /\
  majoranaCount 4 = 8 /\
  hilbertDim 10 = 1024 /\
  matrixAlgDim 5 = 1024 /\
  clBalancedDim 5 = 1024 /\
  cl55MatrixDim = 1024 /\
  dlaDimSYK 4 < dlaDimSK 8.
Proof. cbv; repeat split; lia. Qed.

Theorem graph_kernel :
  edgeHolds Quantum_SK_Model has_pool_size Symmetry_Adapted_Operator_Pool = true /\
  edgeHolds SYK_Majorana_Model has_pool_size Symmetry_Adapted_Operator_Pool = true /\
  edgeHolds SYK_Majorana_Model embeds_by Jordan_Wigner_Clifford_Embedding = true /\
  edgeHolds Jordan_Wigner_Clifford_Embedding realizes_cl55_block Pin55_Spinor_Block = true /\
  edgeHolds SYK_Majorana_Model has_dla_dimension Dense_Dynamical_Lie_Algebra = true /\
  edgeHolds Dense_Dynamical_Lie_Algebra scales_as SYK_Majorana_Model = true.
Proof. compute; repeat split; reflexivity. Qed.
