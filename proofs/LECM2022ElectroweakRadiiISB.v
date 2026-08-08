From Stdlib Require Import QArith List String.
Import ListNotations.
Open Scope Q_scope.
Open Scope string_scope.

Definition V2 (x:Q) : Q := x*x.
Definition ckmFirstRowSum (Vud Vus Vub:Q) : Q := V2 Vud + V2 Vus + V2 Vub.
Definition ckmUnitarityDefect (Vud Vus Vub:Q) : Q := ckmFirstRowSum Vud Vus Vub - 1.
Definition T_superallowed : Q := 1.
Definition J_superallowed : Q := 0.
Definition bareFermiMatrixSquared : Q := 2.
Definition permyriadToPercent (x:Q) : Q := x/100.
Definition correctedFermiSquared (deltaC:Q) : Q := bareFermiMatrixSquared*(1-deltaC).
Definition FtCorrected (ft deltaR deltaC:Q) : Q := ft*(1+deltaR)*(1-deltaC).
Definition combinedISBObservable (beta radius:Q) : Q := beta + radius.
Definition exactIsospinRadiusConstraint (x:Q) : Q*Q := (x,-x).
Definition isbDeviationFromExact (beta radius:Q) : Q := combinedISBObservable beta radius.
Definition isovectorMonopoleScale (NminusZ A:Q) : Q := NminusZ/A.
Definition uniformSphereCoulombScale (Z R:Q) : Q := Z/R.

Theorem lecm2022_electroweak_radii_isb_kernel :
  ckmFirstRowSum (3/5) (4/5) 0 == 1 /\
  ckmUnitarityDefect (3/5) (4/5) 0 == 0 /\
  T_superallowed == 1 /\ J_superallowed == 0 /\
  permyriadToPercent 10 == 1/10 /\ permyriadToPercent 100 == 1 /\
  correctedFermiSquared 0 == bareFermiMatrixSquared /\
  correctedFermiSquared (1/100) == 99/50 /\
  combinedISBObservable (fst (exactIsospinRadiusConstraint (7/13))) (snd (exactIsospinRadiusConstraint (7/13))) == 0 /\
  combinedISBObservable (3/10) (-1/5) == 1/10 /\
  isbDeviationFromExact (3/10) (-1/5) == 1/10 /\
  isovectorMonopoleScale 2 40 == 1/20 /\
  uniformSphereCoulombScale 20 4 == 5.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Inductive Concept := CKM_First_Row_Unitarity | Superallowed_Beta_Decay | ISB_Correction_deltaC | Electroweak_Nuclear_Radii | Isovector_Monopole_Operator | Combined_ISB_Observable.
Inductive Edge := constrains | measures | corrects | probes | cancels_under_exact_isospin.
Definition edgeHolds a e b :=
  match a,e,b with
  | Superallowed_Beta_Decay, constrains, CKM_First_Row_Unitarity => true
  | ISB_Correction_deltaC, corrects, Superallowed_Beta_Decay => true
  | Electroweak_Nuclear_Radii, probes, ISB_Correction_deltaC => true
  | Isovector_Monopole_Operator, measures, Electroweak_Nuclear_Radii => true
  | Combined_ISB_Observable, cancels_under_exact_isospin, Isovector_Monopole_Operator => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds Superallowed_Beta_Decay constrains CKM_First_Row_Unitarity = true /\
  edgeHolds ISB_Correction_deltaC corrects Superallowed_Beta_Decay = true /\
  edgeHolds Electroweak_Nuclear_Radii probes ISB_Correction_deltaC = true /\
  edgeHolds Isovector_Monopole_Operator measures Electroweak_Nuclear_Radii = true /\
  edgeHolds Combined_ISB_Observable cancels_under_exact_isospin Isovector_Monopole_Operator = true.
Proof. compute; repeat split; reflexivity. Qed.
