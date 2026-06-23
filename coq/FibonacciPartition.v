From Coq Require Import Reals.
From Coq Require Import Lra.

Open Scope R_scope.

Section FibonacciPartition.

Variable UpperPhi : R.
Variable LowerPhi : R.

Hypothesis UpperPhi_eq_one_add_LowerPhi : UpperPhi = 1 + LowerPhi.
Hypothesis UpperPhi_sq : UpperPhi ^ 2 = UpperPhi + 1.

Theorem Fibonacci_scale_decomp :
  20 * UpperPhi ^ 4 = 100 + 60 * LowerPhi.
Proof.
  assert (UpperPhi ^ 4 = (UpperPhi ^ 2) ^ 2) by ring.
  rewrite H.
  rewrite UpperPhi_sq.
  assert ((UpperPhi + 1) ^ 2 = UpperPhi ^ 2 + 2 * UpperPhi + 1) by ring.
  rewrite H0.
  rewrite UpperPhi_sq.
  rewrite UpperPhi_eq_one_add_LowerPhi.
  ring.
Qed.

Definition bosonicFactor (x : R) : R := 1 / (1 - x).
Definition fermionicFactor (x : R) : R := 1 + x.

Theorem bosonic_minus_fermionic_eq_sq_mul_bosonic :
  forall x, x <> 1 ->
  bosonicFactor x - fermionicFactor x = x ^ 2 * bosonicFactor x.
Proof.
  intros x Hx.
  unfold bosonicFactor, fermionicFactor.
  unfold Rdiv.
  assert (h_diff : 1 - x <> 0) by lra.
  assert (H : 1 * / (1 - x) - (1 + x) = (1 - (1 + x) * (1 - x)) * / (1 - x)).
  {
    rewrite Rmult_minus_distr_r.
    rewrite Rmult_assoc.
    rewrite Rinv_r by exact h_diff.
    ring.
  }
  rewrite H.
  assert (H0 : 1 - (1 + x) * (1 - x) = x ^ 2) by ring.
  rewrite H0.
  ring.
Qed.

End FibonacciPartition.
