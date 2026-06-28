(*
   Coq: theorem-honest local Grand Identity packet
   =============================================

   This file records only exact definitional consequences:
   - a partition-function surface Q
   - Boltzmann potential ln(Q)
   - an abstract expectation observable Kexp
   - the Legendre-style decomposition S_vN = S_B + β * Kexp

   It does not claim a proved de Rham/modular/time equivalence, and it does not
   contain any admitted derivative theorem.
*)

From Stdlib Require Import Reals.
Open Scope R_scope.

Section GrandIdentity.

  Definition spinorialPartitionFunction (Q : R -> R) : R -> R := Q.

  Definition boltzmannEntropy (Q : R -> R) (beta : R) : R :=
    ln (spinorialPartitionFunction Q beta).

  Definition modularEnergyExpectation (Kexp : R -> R) : R -> R := Kexp.

  Definition vonNeumannEntropy (Q Kexp : R -> R) (beta : R) : R :=
    boltzmannEntropy Q beta + beta * modularEnergyExpectation Kexp beta.

  Lemma spinorialPartitionFunction_apply : forall Q beta,
    spinorialPartitionFunction Q beta = Q beta.
  Proof.
    intros; reflexivity.
  Qed.

  Lemma modularEnergyExpectation_apply : forall Kexp beta,
    modularEnergyExpectation Kexp beta = Kexp beta.
  Proof.
    intros; reflexivity.
  Qed.

  Lemma boltzmannEntropy_eq_ln : forall Q beta,
    boltzmannEntropy Q beta = ln (Q beta).
  Proof.
    intros; reflexivity.
  Qed.

  Lemma vonNeumannEntropy_eq_boltzmann_plus_beta_expectation : forall Q Kexp beta,
    vonNeumannEntropy Q Kexp beta = boltzmannEntropy Q beta + beta * Kexp beta.
  Proof.
    intros; reflexivity.
  Qed.

End GrandIdentity.
