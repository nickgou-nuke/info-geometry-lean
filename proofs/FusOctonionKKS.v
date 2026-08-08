From Stdlib Require Import Arith Lia QArith List String.
Import ListNotations.
Open Scope nat_scope.
Open Scope Q_scope.
Open Scope string_scope.

Definition octonionDim : nat := 8.
Definition imaginaryOctonionDim : nat := 7.
Definition octonionOrbitDim : nat := 6.
Definition g2Dim : nat := 14.
Definition su3StabilizerDim : nat := 8.
Definition g2OrbitDim : nat := g2Dim - su3StabilizerDim.
Definition fanoLineCount : nat := 7.
Definition fanoDirectedProducts : nat := 21.
Definition associatorObstruction : Q := 2.
Definition kksFormSample (mu bracketXY:Q) : Q := -mu*bracketXY.
Definition signatureTotal (s:nat*nat) : nat := fst s + snd s.
Definition sphereS6Signature : nat*nat := (6%nat,0%nat).
Definition splitSignature33 : nat*nat := (3%nat,3%nat).
Definition splitSignature24 : nat*nat := (2%nat,4%nat).
Definition so55su5Partition : nat := 24+1+10+10.
Definition spinEven16 : nat := 1+10+5.
Definition spinOdd16 : nat := 5+10+1.
Definition mobiusInv (even odd:Q) : Q*Q := ((even+odd)/2,(even-odd)/2).
Definition mobiusRec (x y:Q) : Q*Q := (x+y,x-y).
Definition kleinAverage4 (a b c d:Q) : Q := (a+b+c+d)/4.
Definition tripotentPolynomial (d:Q) : Q := d*(d-1)*(d+1).
Definition poincareCasimir (m:Q) : Q := -m*m.
Definition spectralSpringStiffness (C1:Q) : Q := -C1.
Definition kksClosedObstruction (a:Q) : Q := a.

Theorem fus_octonion_kks_kernel :
  octonionDim = 8%nat /\ imaginaryOctonionDim = 7%nat /\ octonionOrbitDim = 6%nat /\ g2OrbitDim = 6%nat /\
  fanoLineCount = 7%nat /\ fanoDirectedProducts = 21%nat /\ associatorObstruction == 2 /\
  kksFormSample 3 5 == -15 /\ kksClosedObstruction associatorObstruction == 2 /\
  signatureTotal sphereS6Signature = 6%nat /\ signatureTotal splitSignature33 = 6%nat /\ signatureTotal splitSignature24 = 6%nat /\
  so55su5Partition = 45%nat /\ spinEven16 = 16%nat /\ spinOdd16 = 16%nat /\
  fst (mobiusRec (fst (mobiusInv 7 3)) (snd (mobiusInv 7 3))) == 7 /\
  snd (mobiusRec (fst (mobiusInv 7 3)) (snd (mobiusInv 7 3))) == 3 /\
  kleinAverage4 1 2 3 4 == 5/2 /\
  tripotentPolynomial (-1) == 0 /\ tripotentPolynomial 0 == 0 /\ tripotentPolynomial 1 == 0 /\
  spectralSpringStiffness (poincareCasimir 3) == 9.
Proof. repeat split; vm_compute; reflexivity. Qed.

Inductive Concept := Fus_Octonion_KKS | Moufang_Loop | Octonion_Associator_Obstruction | Nearly_Kahler_S6_Orbit | Split_Hyperboloid_Orbit | SO55_SU5_Klein_Spectral.
Inductive Edge := generalizes_to | obstructed_by | induces | split_induces | bridges_to.
Definition edgeHolds a e b :=
  match a,e,b with
  | Fus_Octonion_KKS, generalizes_to, Moufang_Loop => true
  | Fus_Octonion_KKS, obstructed_by, Octonion_Associator_Obstruction => true
  | Fus_Octonion_KKS, induces, Nearly_Kahler_S6_Orbit => true
  | Fus_Octonion_KKS, split_induces, Split_Hyperboloid_Orbit => true
  | Fus_Octonion_KKS, bridges_to, SO55_SU5_Klein_Spectral => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds Fus_Octonion_KKS generalizes_to Moufang_Loop = true /\
  edgeHolds Fus_Octonion_KKS obstructed_by Octonion_Associator_Obstruction = true /\
  edgeHolds Fus_Octonion_KKS induces Nearly_Kahler_S6_Orbit = true /\
  edgeHolds Fus_Octonion_KKS split_induces Split_Hyperboloid_Orbit = true /\
  edgeHolds Fus_Octonion_KKS bridges_to SO55_SU5_Klein_Spectral = true.
Proof. compute; repeat split; reflexivity. Qed.
