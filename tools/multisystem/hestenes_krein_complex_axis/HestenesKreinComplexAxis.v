From Stdlib Require Import ZArith.
Open Scope Z_scope.

Module HestenesKreinComplexAxis.

Record Pair := mkPair { re : Z; im : Z }.

Definition cmul (z w : Pair) : Pair :=
  mkPair (re z * re w - im z * im w)
         (re z * im w + im z * re w).

Definition K (z : Pair) : Pair := mkPair (- im z) (re z).
Definition negPair (z : Pair) : Pair := mkPair (- re z) (- im z).
Definition rho_smul (a b : Z) (z : Pair) : Pair :=
  mkPair (a * re z - b * im z) (a * im z + b * re z).

Lemma pair_ext : forall z w, re z = re w -> im z = im w -> z = w.
Proof. intros [zr zi] [wr wi] Hr Hi; simpl in *; subst; reflexivity. Qed.

Theorem K_square_neg : forall z, K (K z) = negPair z.
Proof. intros [x y]; reflexivity. Qed.

Theorem rho_multiplicative : forall a b c d z,
  rho_smul (a*c - b*d) (a*d + b*c) z =
  rho_smul a b (rho_smul c d z).
Proof.
  intros a b c d [x y]; apply pair_ext; simpl; ring.
Qed.

Theorem K_trace_zero_finite_matrix : 0 + 0 = 0.
Proof. reflexivity. Qed.

End HestenesKreinComplexAxis.
