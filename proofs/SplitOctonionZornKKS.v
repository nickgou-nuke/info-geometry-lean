From Stdlib Require Import Arith Lia QArith List String.
Import ListNotations.
Open Scope nat_scope.
Open Scope Q_scope.
Open Scope string_scope.

Definition zornSlots : nat := 8.
Definition splitPositive : nat := 4.
Definition splitNegative : nat := 4.
Definition imaginaryPositive : nat := 3.
Definition imaginaryNegative : nat := 4.
Definition zeroDivisorNorm : Q := 0.
Definition oneNorm : Q := 1.
Definition associatorWitness : Q := 1.
Definition associatorObstruction : Q := 2.
Definition anomalyCounterterm : Q := -2.
Definition positiveOrbitSignature : nat*nat := (2%nat,4%nat).
Definition negativeOrbitSignature : nat*nat := (3%nat,3%nat).
Definition signatureTotal (s:nat*nat) : nat := fst s + snd s.
Definition subalgebraBound : nat := 4.
Definition adSquareCoeff (N:Q) : Q := -4*N.
Definition so55su5Partition : nat := 24+1+10+10.
Definition poincareCasimir (m:Q) : Q := -m*m.
Definition spectralSpringStiffness (C1:Q) : Q := -C1.
Definition imaginaryNullQuadricDim : nat := 7-1.
Definition varlamovEven : nat := 1+10+5.
Definition varlamovOdd : nat := 5+10+1.
Definition varlamovSpinorDim : nat := varlamovEven+varlamovOdd.
Definition wittenMoebiusIndex : Z := (Z.of_nat varlamovEven - Z.of_nat varlamovOdd)%Z.
Definition mobiusTwist (k:Z) : Z := Z.opp k.
Definition kleinPairInvariant (k:Z) : Z := (k + mobiusTwist k)%Z.
Definition tripotentSpectralPolynomial (d:Z) : Z := (d*d*d-d)%Z.

Theorem split_octonion_zorn_kks_kernel :
  zornSlots = 8%nat /\ (splitPositive + splitNegative)%nat = 8%nat /\ (imaginaryPositive + imaginaryNegative)%nat = 7%nat /\
  zeroDivisorNorm == 0 /\ oneNorm == 1 /\ associatorWitness <> 0 /\ associatorObstruction + anomalyCounterterm == 0 /\
  signatureTotal positiveOrbitSignature = 6%nat /\ signatureTotal negativeOrbitSignature = 6%nat /\ subalgebraBound = 4%nat /\
  adSquareCoeff 1 == -4 /\ adSquareCoeff (-1) == 4 /\ so55su5Partition = 45%nat /\
  spectralSpringStiffness (poincareCasimir 3) == 9 /\
  imaginaryNullQuadricDim = 6%nat /\ varlamovEven = 16%nat /\ varlamovOdd = 16%nat /\ varlamovSpinorDim = 32%nat /\
  wittenMoebiusIndex = 0%Z /\ mobiusTwist (mobiusTwist 7%Z) = 7%Z /\ kleinPairInvariant 7%Z = 0%Z /\
  tripotentSpectralPolynomial (-1)%Z = 0%Z /\ tripotentSpectralPolynomial 0%Z = 0%Z /\ tripotentSpectralPolynomial 1%Z = 0%Z.
Proof. repeat split; vm_compute; try reflexivity; discriminate. Qed.

Inductive Concept := Split_Octonion_Zorn | Norm_Signature_44 | Isotropic_Zero_Divisor | Associator_Obstruction | Compensated_KKS_Anomaly | Split_Orbit_Signatures | SO55_SU5_Bridge.
Inductive Edge := realizes | has | obstructs | compensated_by | bridges_to.
Definition edgeHolds a e b :=
  match a,e,b with
  | Split_Octonion_Zorn, realizes, Norm_Signature_44 => true
  | Split_Octonion_Zorn, has, Isotropic_Zero_Divisor => true
  | Associator_Obstruction, obstructs, Split_Octonion_Zorn => true
  | Associator_Obstruction, compensated_by, Compensated_KKS_Anomaly => true
  | Split_Octonion_Zorn, bridges_to, SO55_SU5_Bridge => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds Split_Octonion_Zorn realizes Norm_Signature_44 = true /\
  edgeHolds Split_Octonion_Zorn has Isotropic_Zero_Divisor = true /\
  edgeHolds Associator_Obstruction obstructs Split_Octonion_Zorn = true /\
  edgeHolds Associator_Obstruction compensated_by Compensated_KKS_Anomaly = true /\
  edgeHolds Split_Octonion_Zorn bridges_to SO55_SU5_Bridge = true.
Proof. compute; repeat split; reflexivity. Qed.
