Require Import Reals.
Require Import ZArith.

Open Scope R_scope.

(* Complete Set of Commuting Observables (CSCO) state space for Pin(5,5) *)
Module Pin55_CSCO.

Record QuantumNumbers := {
  grade : Z;
  casimir2 : R;
  isospin : R
}.

Record CSCO_State (V : Type) := {
  state_vector : V;
  q_numbers : QuantumNumbers
}.

End Pin55_CSCO.
