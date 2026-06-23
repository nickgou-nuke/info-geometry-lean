From Coq Require Import Reals.

Open Scope R_scope.

Section Tripotent.

Variable A : Type.
Variable zero : A.
Variable one : A.
Variable add : A -> A -> A.
Variable sub : A -> A -> A.
Variable mul : A -> A -> A.
Variable smul : R -> A -> A.

Variable OP1 : A.
Variable OP2 : A.

Hypothesis OP1_proj : mul OP1 OP1 = OP1.
Hypothesis OP2_proj : mul OP2 OP2 = OP2.
Hypothesis OP_orth : mul OP1 OP2 = zero.
Hypothesis OP_orth2 : mul OP2 OP1 = zero.

(* Define T = OP1 - OP2 *)
Definition T := sub OP1 OP2.

End Tripotent.
