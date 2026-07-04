From Stdlib Require Import Reals.
From Stdlib Require Import Field.
Open Scope R_scope.

Lemma mobius_equivalence (L a b c d z : R) :
  L <> 0 ->
  c * z + d <> 0 ->
  (L * a * z + L * b) / (L * c * z + L * d) = (a * z + b) / (c * z + d).
Proof.
  intros HL Hcd.
  assert (H: L * c * z + L * d <> 0).
  {
    intro H0.
    apply Hcd.
    assert (H1: L * (c * z + d) = 0).
    {
      replace (L * (c * z + d)) with (L * c * z + L * d) by ring.
      exact H0.
    }
    destruct (Rmult_integral _ _ H1) as [H2 | H2].
    - exfalso; exact (HL H2).
    - exact H2.
  }
  field.
  split; assumption.
Qed.
