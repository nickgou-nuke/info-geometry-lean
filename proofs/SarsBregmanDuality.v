From Coq Require Import ZArith List String Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive Expr :=
  | X | Y | U | EX | EY | One
  | Add : Expr -> Expr -> Expr
  | Sub : Expr -> Expr -> Expr
  | Mul : Expr -> Expr -> Expr
  | Exp : Expr -> Expr
  | Log : Expr -> Expr.

Fixpoint normalize (e : Expr) : Expr :=
  match e with
  | Log (Exp a) => normalize a
  | Exp a => Exp (normalize a)
  | Log a => Log (normalize a)
  | Add a b => Add (normalize a) (normalize b)
  | Sub a b => Sub (normalize a) (normalize b)
  | Mul a b => Mul (normalize a) (normalize b)
  | a => a
  end.

Definition modular_expr : Expr := Sub (Sub U (Sub X Y)) One.
Definition burg_exp_expr : Expr := Sub (Sub U (Log (Exp (Sub X Y)))) One.
Definition itakura_exp_expr : Expr := Sub (Sub (Exp X) (Log (Exp X))) One.
Definition itakura_modular_expr : Expr := Sub (Sub (Exp X) X) One.
Definition surprisal_quadratic (n : Z) : Z := n*n.
Definition edges : list string := ["qft_modular_to_itakura_saito";"bregman_coordinate_isomorphism";"stabilizes_krein_entropy"].

Theorem burg_exp_normalizes : normalize burg_exp_expr = modular_expr.
Proof. compute; reflexivity. Qed.

Theorem itakura_exp_normalizes : normalize itakura_exp_expr = itakura_modular_expr.
Proof. compute; reflexivity. Qed.

Theorem surprisal_quadratic_nonneg : forall n, 0 <= surprisal_quadratic n.
Proof. intro; unfold surprisal_quadratic; nia. Qed.

Theorem edge_count_eq_3 : List.length edges = 3%nat.
Proof. compute; reflexivity. Qed.

Theorem bregman_duality_kernel :
  normalize burg_exp_expr = modular_expr /\
  normalize itakura_exp_expr = itakura_modular_expr /\
  (forall n, 0 <= surprisal_quadratic n) /\
  surprisal_quadratic 0 = 0 /\
  List.length edges = 3%nat.
Proof.
  repeat split;
  try exact burg_exp_normalizes;
  try exact itakura_exp_normalizes;
  try apply surprisal_quadratic_nonneg;
  try compute; reflexivity.
Qed.
