From Stdlib Require Import Arith Lia QArith List String.
Import ListNotations.
Open Scope nat_scope.
Open Scope Q_scope.
Open Scope string_scope.

Definition n5 : nat := 5.
Definition nullVectorDim : nat := 2*n5.
Definition soDim (n:nat) : nat := n*(n-1)/2.
Definition matrixDim (n:nat) : nat := n*n.
Definition slDim (n:nat) : nat := matrixDim n - 1.
Definition skewDim (n:nat) : nat := n*(n-1)/2.
Definition so55NullBlockDim : nat := matrixDim n5 + skewDim n5 + skewDim n5.
Definition su5PartitionDim : nat := slDim n5 + 1 + skewDim n5 + skewDim n5.
Definition spinEven16Dim : nat := 1 + 10 + 5.
Definition spinOdd16Dim : nat := 5 + 10 + 1.
Definition varlamovModePartitionDim : nat := spinEven16Dim + spinOdd16Dim.
Definition involutionParity (diag off:Q) : Q*Q := (diag, -off).
Definition mobiusInversionZ2 (even odd:Q) : Q*Q := ((even+odd)/2, (even-odd)/2).
Definition mobiusReconstructZ2 (x y:Q) : Q*Q := (x+y, x-y).
Definition kleinBottleQuotientAverage (a b c d:Q) : Q := (a+b+c+d)/4.
Definition tripotentDetPolynomial (d:Q) : Q := d*(d-1)*(d+1).
Definition poincareCasimir (m:Q) : Q := -m*m.
Definition spectralSpringStiffness (C1:Q) : Q := -C1.
Definition brillouinPairing (k:Q) : Q*Q := (k,-k).
Definition kleinBottleModeInvariant (k:Q) : Q := fst (brillouinPairing k) + snd (brillouinPairing k).

Theorem so55_null_su5_klein_spectral_kernel :
  nullVectorDim = 10%nat /\ soDim nullVectorDim = 45%nat /\ slDim n5 = 24%nat /\ skewDim n5 = 10%nat /\
  so55NullBlockDim = 45%nat /\ su5PartitionDim = 45%nat /\ su5PartitionDim = so55NullBlockDim /\
  spinEven16Dim = 16%nat /\ spinOdd16Dim = 16%nat /\ varlamovModePartitionDim = 32%nat /\
  fst (involutionParity (fst (involutionParity (7/3) (5/2))) (snd (involutionParity (7/3) (5/2)))) == 7/3 /\
  snd (involutionParity (fst (involutionParity (7/3) (5/2))) (snd (involutionParity (7/3) (5/2)))) == 5/2 /\
  fst (mobiusReconstructZ2 (fst (mobiusInversionZ2 7 3)) (snd (mobiusInversionZ2 7 3))) == 7 /\
  snd (mobiusReconstructZ2 (fst (mobiusInversionZ2 7 3)) (snd (mobiusInversionZ2 7 3))) == 3 /\
  kleinBottleQuotientAverage 1 2 3 4 == 5/2 /\
  tripotentDetPolynomial (-1) == 0 /\ tripotentDetPolynomial 0 == 0 /\ tripotentDetPolynomial 1 == 0 /\
  spectralSpringStiffness (poincareCasimir 3) == 9 /\ kleinBottleModeInvariant (11/7) == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Inductive Concept := SO55_Null_Basis | SU5_Adjoint_24 | Dilaton_Line_1 | Fermion_Ten_B | Fermion_TenBar_C | Spinor_Exterior_16 | Klein_Mobius_Spectral_Quotient.
Inductive Edge := decomposes_to | trace_splits_to | skew_splits_to | classifies_spin_modes | quotients_modes.
Definition edgeHolds a e b :=
  match a,e,b with
  | SO55_Null_Basis, decomposes_to, SU5_Adjoint_24 => true
  | SO55_Null_Basis, trace_splits_to, Dilaton_Line_1 => true
  | SO55_Null_Basis, skew_splits_to, Fermion_Ten_B => true
  | SO55_Null_Basis, skew_splits_to, Fermion_TenBar_C => true
  | Spinor_Exterior_16, quotients_modes, Klein_Mobius_Spectral_Quotient => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds SO55_Null_Basis decomposes_to SU5_Adjoint_24 = true /\
  edgeHolds SO55_Null_Basis trace_splits_to Dilaton_Line_1 = true /\
  edgeHolds SO55_Null_Basis skew_splits_to Fermion_Ten_B = true /\
  edgeHolds SO55_Null_Basis skew_splits_to Fermion_TenBar_C = true /\
  edgeHolds Spinor_Exterior_16 quotients_modes Klein_Mobius_Spectral_Quotient = true.
Proof. compute; repeat split; reflexivity. Qed.
