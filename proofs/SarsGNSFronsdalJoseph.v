From Stdlib Require Import QArith List String.
Import ListNotations.
Open Scope Q_scope.
Open Scope string_scope.

Definition sigma1 (u v : Q*Q) : Q := fst u * snd v - snd u * fst v.
Definition normSq1 (u : Q*Q) : Q := fst u * fst u + snd u * snd u.
Definition fockExponentQuarter (u : Q*Q) : Q := - normSq1 u / 4.

Lemma sigma1_skew : forall u v, sigma1 v u == - sigma1 u v.
Proof. intros [q p] [r s]; unfold sigma1; field. Qed.

Lemma normSq1_zero : normSq1 (0,0) == 0.
Proof. compute; reflexivity. Qed.

Lemma fockExponent_zero : fockExponentQuarter (0,0) == 0.
Proof. compute; reflexivity. Qed.

Record FronsdalRankOneOrbit := mkOrbit { p0:Q; p1:Q; q0:Q; q1:Q }.
Definition U00 x := p0 x * q0 x.
Definition U01 x := p0 x * q1 x.
Definition U10 x := p1 x * q0 x.
Definition U11 x := p1 x * q1 x.
Definition josephMinor x := U00 x * U11 x - U01 x * U10 x.
Definition starProductCorrection (hbar eta : Q) : Q := - hbar*hbar*eta.
Definition fronsdalQuadraticRelation (hbar eta lhs : Q) : Prop := lhs == starProductCorrection hbar eta.

Lemma rank_one_joseph_minor_zero : forall x, josephMinor x == 0.
Proof. intros [a b c d]; unfold josephMinor, U00, U01, U10, U11; ring. Qed.

Lemma fronsdal_relation_refl : forall hbar eta, fronsdalQuadraticRelation hbar eta (starProductCorrection hbar eta).
Proof. intros; unfold fronsdalQuadraticRelation; reflexivity. Qed.

Inductive Concept := Sars_Weyl_Colimit | Regular_Weyl_GNS_State | Fronsdal_2005 | Singular_Coadjoint_Orbit | Joseph_Ideal_Constraints | Rank_One_Moment_Map.
Inductive Edge := GNS_completion | defines_quantization | cut_out_by | annihilates | embeds_as.
Definition edgeHolds a e b :=
  match a,e,b with
  | Sars_Weyl_Colimit, GNS_completion, Regular_Weyl_GNS_State => true
  | Fronsdal_2005, defines_quantization, Joseph_Ideal_Constraints => true
  | Singular_Coadjoint_Orbit, cut_out_by, Joseph_Ideal_Constraints => true
  | Joseph_Ideal_Constraints, annihilates, Regular_Weyl_GNS_State => true
  | Rank_One_Moment_Map, embeds_as, Singular_Coadjoint_Orbit => true
  | _,_,_ => false
  end.

Theorem gns_fronsdal_joseph_kernel :
  (forall u v, sigma1 v u == - sigma1 u v) /\
  normSq1 (0,0) == 0 /\
  fockExponentQuarter (0,0) == 0 /\
  (forall x, josephMinor x == 0) /\
  (forall hbar eta, fronsdalQuadraticRelation hbar eta (starProductCorrection hbar eta)).
Proof.
  repeat split; intros; try apply sigma1_skew; try apply normSq1_zero; try apply fockExponent_zero; try apply rank_one_joseph_minor_zero; try apply fronsdal_relation_refl.
Qed.

Theorem graph_kernel :
  edgeHolds Sars_Weyl_Colimit GNS_completion Regular_Weyl_GNS_State = true /\
  edgeHolds Fronsdal_2005 defines_quantization Joseph_Ideal_Constraints = true /\
  edgeHolds Singular_Coadjoint_Orbit cut_out_by Joseph_Ideal_Constraints = true /\
  edgeHolds Joseph_Ideal_Constraints annihilates Regular_Weyl_GNS_State = true /\
  edgeHolds Rank_One_Moment_Map embeds_as Singular_Coadjoint_Orbit = true.
Proof. compute; repeat split; reflexivity. Qed.
