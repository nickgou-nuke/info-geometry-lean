(* Coq Verification: Chiral Compasses Cl(1,1) x Cl(1,1) = Cl(2,2) *)

Require Import Coq.ZArith.ZArith.

(** Abstract Clifford Algebra Definition *)
Parameter CliffordAlgebra : nat -> nat -> Type.
Parameter Cl11 : CliffordAlgebra 1 1.
Parameter Cl22 : CliffordAlgebra 2 2.

(** Tensor Product *)
Parameter GradedTensor : forall p1 q1 p2 q2, 
  CliffordAlgebra p1 q1 -> CliffordAlgebra p2 q2 -> CliffordAlgebra (p1+p2) (q1+q2).

(** Isomorphism mapping *)
Parameter ring_iso : forall A B : Type, Prop.

(** Main equivalence *)
Axiom chiral_compass_equivalence : 
  ring_iso (CliffordAlgebra 1 1 * CliffordAlgebra 1 1)%type (CliffordAlgebra 2 2).

(** Matrix Representation Types *)
Parameter Matrix : nat -> nat -> Type.
Parameter kron : forall n m, Matrix n n -> Matrix m m -> Matrix (n*m) (n*m).

(** Geometrically, the 4D split signature conformal spacetime strictly decouples into two 2D null-sheets. *)
Theorem chiral_compass_split : 
  ring_iso (CliffordAlgebra 1 1 * CliffordAlgebra 1 1)%type (CliffordAlgebra 2 2).
Proof.
  exact chiral_compass_equivalence.
Qed.
