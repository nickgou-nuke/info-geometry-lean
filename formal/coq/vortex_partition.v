Require Import Reals.
Require Import Lia.
Require Import Binomial.
Require Import Omega.

Open Scope R_scope.

(* Factorial as a real number *)
Fixpoint factR (n : nat) : R :=
  match n with
  | 0 => 1
  | S n => (INR (n + 1) * factR n)%R
  end.

(* Vortex partition truncated at N *)
Definition vortex_partial (N : nat) (q eps1 eps2 : R) : R :=
  let fun k => ( (q / (eps1 * eps2)) ^ (k : nat) ) / ( (factR k) ^ 2 ) in
  sum_fun (fun k => ( (q / (eps1 * eps2)) ^ (k : nat) ) / ( (factR k) ^ 2 )) 0 (N + 1).

(* Actually we need to define sum_fun; we'll use the existing Finset sum from Mathcomp? 
   Instead, we'll write a simple recursive sum. *)

Fixpoint vortex_sum (N n : nat) (q eps1 eps2 : R) : R :=
  match n with
  | 0 => 0
  | S m => ( (q / (eps1 * eps2)) ^ (m : nat) ) / ( (factR m) ^ 2 ) + vortex_sum N m q eps1 eps2
  end.

Definition vortex_partial' (N : nat) (q eps1 eps2 : R) : R :=
  vortex_sum N (N + 1) q eps1 eps2.

(* Lemma: swapping eps1 and eps2 does not change the value because the expression depends only on the product. *)
Lemma vortex_symmetric : forall (N : nat) (q eps1 eps2 : R),
  vortex_partial' N q eps1 eps2 = vortex_partial' N q eps2 eps1.
Proof.
  intros N q eps1 eps2.
  induction N as [|N IH].
  - (* N = 0: sum from 0 to 0 is empty? Actually our sum goes to N+1, so for N=0 we sum over k=0..0 inclusive => one term k=0 *)
    simpl.
    (* term k=0: (q/(eps1*eps2))^0 / (0!^2) = 1 / 1 = 1 *)
    field_simp.
    <;> ring.
    <;> field_simp.
    <;> ring.
  - (* inductive step *)
    simpl.
    (* The sum for N+1 is the sum for N plus the term at index N+1 *)
    *)
    rewrite <- plus_nat them step. We'll do a more straightforward approach: show that each term in the sum is symmetric.

Actually we can prove that for each k, (q/(eps1*eps2))^k = (q/(eps2*eps1))^k because multiplication is commutative. Then the sum of symmetric terms is symmetric.

Let's do that.

We'll define term_k eps1 eps2 = (q/(eps1*eps2))^k / (factR k)^2.

Then show term_k eps1 eps2 = term_k eps2 eps1.

Then the sum over k is symmetric.

Let's implement.

*)

Abort.

Restart.

Lemma vortex_symmetric : forall (N : nat) (q eps1 eps2 : R),
  vortex_partial' N q eps1 eps2 = vortex_partial' N q eps2 eps1.
Proof.
  intros N q eps1 eps2.
  (* We'll prove by induction on N that the partial sums are equal. *)
  induction N as [|N IH].
  - (* Base case N=0: sum over k=0..0 *)
    simpl.
    (* term k=0 is 1 *)
    field_simp.
    <;> ring.
    <;> field_simp.
    <;> ring.
  - (* Inductive step: assume true for N, prove for S N *)
    simpl.
    (* Write sum up to (S N)+1 = sum up to N+1 plus term at N+1 *)
    rewrite <- plus_n_O.
    pattern (vortex_sum N (N + 1 + 1) q eps1 eps2) at 1.
    (* Actually easier: prove that for any n, the sum up to n is symmetric. *)
    (* Let's prove a stronger statement: for all n, sum_{k=0}^{n-1} term_k is symmetric. *)
    admit.
Admitted.