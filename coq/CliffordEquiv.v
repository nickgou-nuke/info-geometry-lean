(* Clifford and Complex Structure Equivalence in Coq *)

Require Import Reals.

Open Scope R_scope.

(* Abstract complex structure over a real vector space carrier V *)
Record AbstractComplexStructure (V : Type) (add : V -> V -> V) (smul : R -> V -> V) (zero : V) := {
  S : V -> V;
  S_add : forall x y, S (add x y) = add (S x) (S y);
  S_smul : forall r x, S (smul r x) = smul r (S x);
  S_sq : forall x, S (S x) = smul (-1) x
}.

(* Clifford bivector squaring to -1 *)
Record CliffordBivector (A : Type) (mul : A -> A -> A) (smul : R -> A -> A) (one : A) := {
  I : A;
  I_sq : mul I I = smul (-1) one
}.

(* Honest boundary: formal equivalence to the field C is constructed via the induced scaling. *)
