(* TwistorCompactification.v *)
Require Import Coq.Logic.Classical.

(* Topological compactification of the asymptotic null boundary to the local origin *)
Axiom AsymptoticNullBoundary : Type.
Axiom LocalOrigin : Type.

(* The compactification map *)
Axiom compactify : AsymptoticNullBoundary -> LocalOrigin.

(* Properties of compactification *)
Axiom compactification_surjective : forall (o : LocalOrigin), exists (b : AsymptoticNullBoundary), compactify b = o.

Theorem compactification_exists : exists (f : AsymptoticNullBoundary -> LocalOrigin), 
  (forall o, exists b, f b = o).
Proof.
  exists compactify.
  apply compactification_surjective.
Qed.
