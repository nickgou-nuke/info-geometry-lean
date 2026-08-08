From Coq Require Import ZArith List String Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive Expr :=
  | VarX
  | VarZ
  | Exp : Expr -> Expr
  | Log : Expr -> Expr
  | One
  | Sub : Expr -> Expr -> Expr.

Fixpoint normalize (e : Expr) : Expr :=
  match e with
  | Log (Exp VarX) => VarX
  | Exp a => Exp (normalize a)
  | Log a => Log (normalize a)
  | Sub a b => Sub (normalize a) (normalize b)
  | a => a
  end.

Definition modular_expr : Expr := Sub (Sub (Exp VarX) One) VarX.
Definition itakura_exp_expr : Expr := Sub (Sub (Exp VarX) (Log (Exp VarX))) One.
Definition modular_reassociated : Expr := Sub (Sub (Exp VarX) VarX) One.
Definition surprisal_quadratic (x : Z) : Z := x*x.
Definition edges : list string := ["exp_coordinate_transform";"bregman_dual";"stabilizes_modular_flow"].

Theorem log_exp_normalizes : normalize (Log (Exp VarX)) = VarX.
Proof. compute; reflexivity. Qed.

Theorem itakura_exp_normal_form : normalize itakura_exp_expr = modular_reassociated.
Proof. compute; reflexivity. Qed.

Theorem surprisal_quadratic_nonneg : forall x, 0 <= surprisal_quadratic x.
Proof. intro; unfold surprisal_quadratic; nia. Qed.

Theorem surprisal_quadratic_zero : surprisal_quadratic 0 = 0.
Proof. compute; reflexivity. Qed.

Theorem edge_count_eq_3 : List.length edges = 3%nat.
Proof. compute; reflexivity. Qed.

Theorem itakura_modular_kernel :
  normalize (Log (Exp VarX)) = VarX /\
  normalize itakura_exp_expr = modular_reassociated /\
  (forall x, 0 <= surprisal_quadratic x) /\
  surprisal_quadratic 0 = 0 /\
  List.length edges = 3%nat.
Proof.
  repeat split;
  try exact log_exp_normalizes;
  try exact itakura_exp_normal_form;
  try apply surprisal_quadratic_nonneg;
  try exact surprisal_quadratic_zero;
  exact edge_count_eq_3.
Qed.
