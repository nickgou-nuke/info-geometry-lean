(* TwistedKTheory.v *)
(* Formulate the twisted K-theory classes corresponding to the non-perturbative global anomalies. *)

Require Import Coq.Logic.Classical.

Parameter Space : Type.
Parameter Class : Type.
Parameter Anomaly : Type.

Parameter twisted_k_theory : Space -> Type.
Parameter non_perturbative_anomaly : Space -> Anomaly.

Parameter KClass : forall (s : Space), twisted_k_theory s -> Class.
Parameter anomaly_mapping : forall (s : Space), Class -> Anomaly.

Axiom anomaly_correspondence : forall (s : Space) (t : twisted_k_theory s),
  anomaly_mapping s (KClass s t) = non_perturbative_anomaly s.

Theorem global_anomaly_represented_by_k_theory :
  forall (s : Space) (t : twisted_k_theory s),
  anomaly_mapping s (KClass s t) = non_perturbative_anomaly s.
Proof.
  intros s t.
  apply anomaly_correspondence.
Qed.
