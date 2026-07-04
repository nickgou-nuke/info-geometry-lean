From Stdlib Require Import QArith QArith_base.
Open Scope Q_scope.

Inductive mobius_class := Elliptic | Parabolic | Hyperbolic | Loxodromic.

Definition sigma_pair := (Q * Q)%type.

Definition re (s : sigma_pair) : Q := fst s.
Definition im (s : sigma_pair) : Q := snd s.

Definition classify_sigma (s : sigma_pair) : mobius_class :=
  if Qeq_bool (im s) 0 then
    if Qeq_bool (re s) 4 then Parabolic
    else if Qlt_le_dec (re s) 4 then Elliptic else Hyperbolic
  else Loxodromic.

Definition hyper_sigma : sigma_pair := (25#4, 0).
Definition para_sigma : sigma_pair := (4, 0).
Definition ell_sigma : sigma_pair := (0, 0).
Definition lox_sigma : sigma_pair := (3, 4).

Definition gaussian_square (a b : Q) : sigma_pair := (a * a - b * b, 2 * a * b).

Example hyper_sigma_readback : hyper_sigma = ((5#2) * (5#2), 0).
Proof. reflexivity. Qed.

Example para_sigma_readback : para_sigma = (2 * 2, 0).
Proof. reflexivity. Qed.

Example ell_sigma_readback : ell_sigma = (0, 0).
Proof. reflexivity. Qed.

Example lox_sigma_readback : gaussian_square 2 1 = lox_sigma.
Proof. reflexivity. Qed.

Example hyper_classification : classify_sigma hyper_sigma = Hyperbolic.
Proof. reflexivity. Qed.

Example para_classification : classify_sigma para_sigma = Parabolic.
Proof. reflexivity. Qed.

Example ell_classification : classify_sigma ell_sigma = Elliptic.
Proof. reflexivity. Qed.

Example lox_classification : classify_sigma lox_sigma = Loxodromic.
Proof. reflexivity. Qed.

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

Lemma elliptic_trace_sq : forall alpha : R,
  (cos alpha + cos alpha) ^ 2 = 4 * (cos alpha) ^ 2.
Proof.
  intros alpha.
  simpl.
  ring.
Qed.
