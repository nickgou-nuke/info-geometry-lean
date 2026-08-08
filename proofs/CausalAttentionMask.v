Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.

Section CausalAttentionMask.

(* Tokens in a sequence *)
Variable Token : Type.

(* The causal relationship (partial order) between tokens *)
Variable causal_rel : relation Token.

Hypothesis causal_refl : reflexive Token causal_rel.
Hypothesis causal_trans : transitive Token causal_rel.
Hypothesis causal_antisym : antisymmetric Token causal_rel.

(* 
  The Causal Future of a token, which acts as the exact 
  topological causal set for a discrete attention mask.
*)
Definition CausalFuture (t : Token) : Ensemble Token :=
  fun t' => causal_rel t t'.

(* 
  The attention mask allows information flow only from the causal past.
*)
Definition CausalPast (t : Token) : Ensemble Token :=
  fun t' => causal_rel t' t.

End CausalAttentionMask.
