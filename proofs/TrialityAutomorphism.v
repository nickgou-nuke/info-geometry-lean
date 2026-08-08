Require Import Setoid.

Inductive Spin8Rep : Type :=
  | Vector : Spin8Rep
  | SpinorPlus : Spin8Rep
  | SpinorMinus : Spin8Rep.

Definition rho (x : Spin8Rep) : Spin8Rep :=
  match x with
  | Vector => SpinorPlus
  | SpinorPlus => SpinorMinus
  | SpinorMinus => Vector
  end.

Definition sigma (x : Spin8Rep) : Spin8Rep :=
  match x with
  | Vector => SpinorPlus
  | SpinorPlus => Vector
  | SpinorMinus => SpinorMinus
  end.

Theorem rho_cubed_id : forall x : Spin8Rep, rho (rho (rho x)) = x.
Proof.
  intro x. destruct x; reflexivity.
Qed.

Theorem sigma_squared_id : forall x : Spin8Rep, sigma (sigma x) = x.
Proof.
  intro x. destruct x; reflexivity.
Qed.

Theorem rho_sigma_rel : forall x : Spin8Rep, sigma (rho (sigma x)) = rho (rho x).
Proof.
  intro x. destruct x; reflexivity.
Qed.
