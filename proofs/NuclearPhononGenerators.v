From Stdlib Require Import Arith Lia QArith List String.
Import ListNotations.
Open Scope nat_scope.
Open Scope Q_scope.
Open Scope string_scope.

Definition sBosonCount : nat := 1.
Definition dBosonCount : nat := 5.
Definition ibmModeCount : nat := sBosonCount + dBosonCount.
Definition uNGeneratorCount (n:nat) : nat := n*n.
Definition ibmU6GeneratorCount : nat := uNGeneratorCount ibmModeCount.
Definition ibmBilinearPartition : nat := 1 + dBosonCount + dBosonCount + dBosonCount*dBosonCount.
Definition symmetricPairCount (n:nat) : nat := n*(n+1)/2.
Definition antisymmetricPairCount (n:nat) : nat := n*(n-1)/2.
Definition sp6GeneratorCount : nat := symmetricPairCount 3 + symmetricPairCount 3 + 3*3.
Definition collectiveTensorCertificate : nat := antisymmetricPairCount 3 + symmetricPairCount 3 + symmetricPairCount 3 + symmetricPairCount 3.
Record Sp6PhononRaising := mkRaise { Qcoeff:Q; Kcoeff:Q; Tcoeff:Q; omegaQuanta:nat }.
Definition sp6PhononRaising := mkRaise (1/2) (-1/2) (1/2) 2.
Definition sp6PhononLowering := mkRaise (1/2) (-1/2) (-1/2) 2.
Definition raisingPlusQ A B := Qcoeff A + Qcoeff B.
Definition raisingPlusK A B := Kcoeff A + Kcoeff B.
Definition raisingPlusT A B := Tcoeff A + Tcoeff B.
Definition raisingMinusT A B := Tcoeff A - Tcoeff B.
Definition poincareC1 (m:Q) : Q := -m*m.
Definition springStiffnessFromC1 (C1:Q) : Q := -C1.
Definition springPotential (m lam:Q) : Q := m*m*lam*lam/2.
Definition dilationBracketCoeff (C1:Q) : Q := 2*C1.
Definition phononEnergy (omega n:Q) : Q := (n+1/2)*omega.
Definition uDimension (n:nat) : nat := n*n.
Definition suDimension (n:nat) : nat := n*n - 1.
Definition soDimension (n:nat) : nat := n*(n-1)/2.
Definition spRealDimensionFromHalfRank (n:nat) : nat := n*(2*n+1).
Definition deltaNat (i j:nat) : nat := if Nat.eqb i j then 1 else 0.
Definition matrixUnitFirstCoeff (i j k l:nat) : nat := deltaNat j k.
Definition matrixUnitSecondCoeff (i j k l:nat) : Q :=
  if Nat.eqb l i then -1 else 0.
Definition ccrPositionMomentumBracketNonzero : Prop := ~ (1 == 0).

Theorem nuclear_phonon_generators_kernel :
  ibmModeCount = 6%nat /\ ibmU6GeneratorCount = 36%nat /\ ibmBilinearPartition = 36%nat /\
  symmetricPairCount 3%nat = 6%nat /\ antisymmetricPairCount 3%nat = 3%nat /\ sp6GeneratorCount = 21%nat /\ collectiveTensorCertificate = 21%nat /\
  Qcoeff sp6PhononRaising == 1/2 /\ Kcoeff sp6PhononRaising == -1/2 /\ Tcoeff sp6PhononRaising == 1/2 /\
  raisingPlusQ sp6PhononRaising sp6PhononLowering == 1 /\
  raisingPlusK sp6PhononRaising sp6PhononLowering == -1 /\
  raisingPlusT sp6PhononRaising sp6PhononLowering == 0 /\
  raisingMinusT sp6PhononRaising sp6PhononLowering == 1 /\
  springStiffnessFromC1 (poincareC1 3) == 9 /\
  springStiffnessFromC1 (poincareC1 0) == 0 /\ springPotential 3 2 == 18 /\
  dilationBracketCoeff (poincareC1 3) == -18 /\ phononEnergy 5 1 == 15/2.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem symmetry_group_kernel :
  uDimension 6 = 36%nat /\ suDimension 3 = 8%nat /\
  soDimension 6 = 15%nat /\ soDimension 5 = 10%nat /\ soDimension 3 = 3%nat /\
  spRealDimensionFromHalfRank 3 = 21%nat /\
  matrixUnitFirstCoeff 1 2 2 3 = 1%nat /\
  matrixUnitSecondCoeff 1 2 2 3 == 0 /\
  matrixUnitFirstCoeff 1 2 2 1 = 1%nat /\
  matrixUnitSecondCoeff 1 2 2 1 == -1 /\
  ccrPositionMomentumBracketNonzero.
Proof.
  unfold ccrPositionMomentumBracketNonzero.
  repeat split; vm_compute; try reflexivity; discriminate.
Qed.

Inductive Concept := Nuclear_Phonon | IBM_U6_Bilinear_Generator | Quadrupole_d_dagger_s | Sp6R_Raising_Generator | Noncompact_Dilation_Shear | Casimir_Dilation_Spring.
Inductive Edge := represented_by | counted_by | decomposes_into | raises_by | quantizes.
Definition edgeHolds a e b :=
  match a,e,b with
  | Nuclear_Phonon, represented_by, IBM_U6_Bilinear_Generator => true
  | IBM_U6_Bilinear_Generator, counted_by, Quadrupole_d_dagger_s => true
  | Nuclear_Phonon, raises_by, Sp6R_Raising_Generator => true
  | Sp6R_Raising_Generator, decomposes_into, Noncompact_Dilation_Shear => true
  | Noncompact_Dilation_Shear, quantizes, Casimir_Dilation_Spring => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds Nuclear_Phonon represented_by IBM_U6_Bilinear_Generator = true /\
  edgeHolds IBM_U6_Bilinear_Generator counted_by Quadrupole_d_dagger_s = true /\
  edgeHolds Nuclear_Phonon raises_by Sp6R_Raising_Generator = true /\
  edgeHolds Sp6R_Raising_Generator decomposes_into Noncompact_Dilation_Shear = true /\
  edgeHolds Noncompact_Dilation_Shear quantizes Casimir_Dilation_Spring = true.
Proof. compute; repeat split; reflexivity. Qed.
