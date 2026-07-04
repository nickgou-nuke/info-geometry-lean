Section BrillouinKlein_Ring.

Variable R : Type.
Variable Rmul : R -> R -> R.
Variable Ropp : R -> R.
Variable Rone : R.

Infix "*" := Rmul.
Notation "- x" := (Ropp x).

Variable Rmul_assoc : forall x y z, (x * y) * z = x * (y * z).
Variable Rmul_1_l : forall x, Rone * x = x.
Variable Rmul_1_r : forall x, x * Rone = x.
Variable Rmul_opp_l : forall x y, (- x) * y = - (x * y).
Variable Rmul_opp_r : forall x y, x * (- y) = - (x * y).
Variable Ropp_involutive : forall x, - (- x) = x.

Variable Tx Ty : R.
Variable Tx_sq : Tx * Tx = Rone.
Variable Ty_sq : Ty * Ty = Rone.
Variable Tx_Ty_anti : Tx * Ty = - (Ty * Tx).

Lemma Ty_Tx_anti : Ty * Tx = - (Tx * Ty).
Proof.
  rewrite Tx_Ty_anti. rewrite Ropp_involutive. reflexivity.
Qed.

Theorem Tx_Ty_sq : (Tx * Ty) * (Tx * Ty) = - Rone.
Proof.
  rewrite Rmul_assoc.
  assert (H: Ty * (Tx * Ty) = (Ty * Tx) * Ty).
  { rewrite <- Rmul_assoc. reflexivity. }
  rewrite H.
  rewrite Ty_Tx_anti.
  rewrite Rmul_opp_l.
  rewrite Rmul_opp_r.
  assert (H2: Tx * ((Tx * Ty) * Ty) = (Tx * Tx) * (Ty * Ty)).
  { rewrite <- Rmul_assoc. rewrite <- (Rmul_assoc Tx Tx Ty). rewrite Rmul_assoc. reflexivity. }
  rewrite H2.
  rewrite Tx_sq.
  rewrite Ty_sq.
  rewrite Rmul_1_l.
  reflexivity.
Qed.

End BrillouinKlein_Ring.
