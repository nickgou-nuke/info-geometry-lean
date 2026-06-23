From Coq Require Import Reals.
From Coq Require Import Lra.

Open Scope R_scope.

Section HodgeTrifactor.

(* 1. Operator algebra *)
Variable M : Type.
Variable zero : M.
Variable one : M.
Variable add : M -> M -> M.
Variable sub : M -> M -> M.
Variable mul : M -> M -> M.
Variable smul : R -> M -> M.

Variable T : M.
Hypothesis T_cubic : mul T (mul T T) = T.

Variable P_ex : M.
Variable P_co : M.
Variable P_har : M.

(* We assume standard algebra properties for M *)
Hypothesis mul_assoc : forall x y z, mul x (mul y z) = mul (mul x y) z.
Hypothesis mul_distr_l : forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Hypothesis mul_distr_r : forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Hypothesis smul_mul_l : forall r x y, mul (smul r x) y = smul r (mul x y).
Hypothesis smul_mul_r : forall r x y, mul x (smul r y) = smul r (mul x y).

(* 2. Partition functions *)
Definition bosonicFactor (x : R) : R := 1 / (1 - x).
Definition fermionicFactor (x : R) : R := 1 + x.
Definition harmonicFactor (x : R) : R := 1 - x.

Theorem bosonic_times_harmonic_eq_one :
  forall x, x <> 1 -> bosonicFactor x * harmonicFactor x = 1.
Proof.
  intros x Hx.
  unfold bosonicFactor, harmonicFactor.
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  - ring.
  - intro H.
    apply Hx.
    lra.
Qed.

Theorem fermionic_times_harmonic_eq_one_sub_sq :
  forall x, fermionicFactor x * harmonicFactor x = 1 - x^2.
Proof.
  intros x.
  unfold fermionicFactor, harmonicFactor.
  ring.
Qed.

End HodgeTrifactor.
