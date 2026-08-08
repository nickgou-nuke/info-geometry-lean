Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Equivalence between the conformal expansion limit and the macroscopic quantum collapse (BEC) over the state populations *)

Definition conformal_expansion_limit (rho : R) (Ng Ne : R) :=
  rho > 0 /\ Ng = Ne.

Definition macroscopic_quantum_collapse (Ng Ne : R) :=
  Ng - Ne = 0.

Theorem conformal_expansion_implies_collapse :
  forall rho Ng Ne,
    conformal_expansion_limit rho Ng Ne ->
    macroscopic_quantum_collapse Ng Ne.
Proof.
  intros rho Ng Ne H.
  unfold conformal_expansion_limit in H.
  unfold macroscopic_quantum_collapse.
  destruct H as [Hrho Heq].
  rewrite Heq.
  lra.
Qed.

Theorem collapse_implies_conformal_expansion_if_rho_pos :
  forall rho Ng Ne,
    rho > 0 ->
    macroscopic_quantum_collapse Ng Ne ->
    conformal_expansion_limit rho Ng Ne.
Proof.
  intros rho Ng Ne Hrho H.
  unfold macroscopic_quantum_collapse in H.
  unfold conformal_expansion_limit.
  split.
  - exact Hrho.
  - lra.
Qed.
