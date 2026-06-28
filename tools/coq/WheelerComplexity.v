(** * Wheeler Complexity and State Expansion *)
(** This file provides a formalization of algorithmic information and state 
    expansion in Coq. It defines a basic type for a transition system, a metric 
    for state complexity, and proves a lemma about the monotonic growth of 
    this complexity. *)

Require Import Arith.

(** ** 1. Transition System Definition **)
(** We define a simple transition system where states are represented 
    by sequences of bits (booleans), conceptually analogous to the tape of 
    a Turing machine or a linear state transition system. *)
Inductive state : Type :=
  | halt : state
  | active : bool -> state -> state.

(** ** 2. Complexity Metric **)
(** The state complexity is defined as the depth of the state structure, 
    analogous to the length of a string or tape segment. *)
Fixpoint complexity (s : state) : nat :=
  match s with
  | halt => 0
  | active _ s' => S (complexity s')
  end.

(** We define a specific transition rule that expands the state. 
    It models an algorithmic process that always increases the 
    informational content of the state. *)
Fixpoint transition (s : state) : state :=
  match s with
  | halt => active true halt
  | active b s' => active b (active (negb b) (transition s'))
  end.

(** ** 3. Monotonic Growth **)
(** We prove that under the chosen transition rule, the complexity 
    of the state always strictly increases. *)
Lemma transition_complexity_growth : forall s : state, 
  complexity s < complexity (transition s).
Proof.
  intro s.
  induction s as [| b s' IH].
  - (* Base case: halt *)
    simpl.
    (* 0 < 1 is defined as 1 <= 1 *)
    unfold lt. apply le_n.
  - (* Inductive step: active b s' *)
    simpl.
    (* Prove S (complexity s') < S (S (complexity (transition s'))) *)
    apply le_n_S.
    apply le_S.
    exact IH.
Qed.

(** A weaker transition rule that preserves or increases complexity. *)
Definition simple_step (s : state) : state :=
  match s with
  | halt => halt
  | active b s' => active (negb b) s'
  end.

Lemma simple_step_monotonic : forall s : state,
  complexity s <= complexity (simple_step s).
Proof.
  intro s. destruct s as [| b s'].
  - (* Base case: halt *)
    simpl. apply le_n.
  - (* Inductive step: active b s' *)
    simpl. apply le_n.
Qed.
