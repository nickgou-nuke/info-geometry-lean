From Stdlib Require Import QArith.

Open Scope Q_scope.

Definition massCasimir (m2 : Q) : Q := -m2.
Definition spinCasimir (J : Q) : Q := J * (J + 1).
Definition isospinCasimir (T : Q) : Q := T * (T + 1).
Definition seniorityCasimir (v : Q) : Q := v * (v + 1).
Definition casimirStiffness (C : Q) : Q := -C.
Definition imme (a b c Tz : Q) : Q := a + b*Tz + c*Tz*Tz.
Definition pairHamiltonian (k0 k1 : Q) : Q := k0 + k1.
Definition casimirHamiltonian (alpha beta gamma delta m2 J T v : Q) : Q :=
  alpha*massCasimir m2 + beta*spinCasimir J + gamma*isospinCasimir T + delta*seniorityCasimir v.
Definition generalizedHamiltonian
    (alpha beta gamma delta a b c k0 k1 spring m2 J T v Tz : Q) : Q :=
  casimirHamiltonian alpha beta gamma delta m2 J T v + imme a b c Tz + pairHamiltonian k0 k1 + spring.

Lemma isospin_casimir_T1 : isospinCasimir 1 == 2.
Proof. vm_compute; reflexivity. Qed.

Lemma isospin_casimir_half : isospinCasimir (1/2) == 3/4.
Proof. vm_compute; reflexivity. Qed.

Lemma mass_casimir_stiffness : forall m2, casimirStiffness (massCasimir m2) == m2.
Proof. intros; unfold casimirStiffness, massCasimir; ring. Qed.

Lemma imme_mirror_difference : forall a b c t,
  imme a b c t - imme a b c (-t) == 2*b*t.
Proof. intros; unfold imme; ring. Qed.

Lemma imme_mirror_sum : forall a b c t,
  imme a b c t + imme a b c (-t) == 2*a + 2*c*t*t.
Proof. intros; unfold imme; ring. Qed.

Lemma generalized_mirror_difference : forall alpha beta gamma delta a b c k0 k1 spring m2 J T v t,
  generalizedHamiltonian alpha beta gamma delta a b c k0 k1 spring m2 J T v t -
  generalizedHamiltonian alpha beta gamma delta a b c k0 k1 spring m2 J T v (-t) == 2*b*t.
Proof.
  intros; unfold generalizedHamiltonian, casimirHamiltonian, imme, pairHamiltonian,
    massCasimir, spinCasimir, isospinCasimir, seniorityCasimir; ring.
Qed.

Lemma casimir_isospin_hamiltonian_kernel :
  isospinCasimir 1 == 2 /\
  isospinCasimir (1/2) == 3/4 /\
  (forall m2, casimirStiffness (massCasimir m2) == m2) /\
  (forall a b c t, imme a b c t - imme a b c (-t) == 2*b*t) /\
  (forall a b c t, imme a b c t + imme a b c (-t) == 2*a + 2*c*t*t) /\
  casimirStiffness (massCasimir 94) == 94.
Proof.
  split; [apply isospin_casimir_T1|].
  split; [apply isospin_casimir_half|].
  split; [intro m2; apply mass_casimir_stiffness|].
  split; [intros a b c t; apply imme_mirror_difference|].
  split; [intros a b c t; apply imme_mirror_sum|].
  vm_compute; reflexivity.
Qed.
