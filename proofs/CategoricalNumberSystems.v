Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Inductive NumSys : Type :=
  | Primes : NumSys
  | Naturals : NumSys
  | Rationals : NumSys
  | Reals : NumSys
  | Complex : NumSys.

Inductive Step : NumSys -> NumSys -> Prop :=
  | step_P_N : Step Primes Naturals
  | step_N_Q : Step Naturals Rationals
  | step_Q_R : Step Rationals Reals
  | step_R_C : Step Reals Complex.

Definition Ladder := clos_refl_trans NumSys Step.

Lemma prime_to_complex_ladder : Ladder Primes Complex.
Proof.
  apply rt_trans with Naturals.
  - apply rt_step. apply step_P_N.
  - apply rt_trans with Rationals.
    + apply rt_step. apply step_N_Q.
    + apply rt_trans with Reals.
      * apply rt_step. apply step_Q_R.
      * apply rt_step. apply step_R_C.
Qed.
