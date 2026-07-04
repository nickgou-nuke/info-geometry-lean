From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

(* The threshold for the continuous spectrum in Liouville theory: (c - 1) / 24 *)
Definition liouville_threshold (c : R) : R :=
  (c - 1) / 24.

(* The conformal dimension belongs to the continuous ray if Delta >= threshold *)
Definition in_continuous_spectrum (c Delta : R) : Prop :=
  Delta >= liouville_threshold c.

(* Alternative definition: Delta is threshold + P, where P >= 0 *)
Definition in_continuous_spectrum_alt (c Delta : R) : Prop :=
  exists P : R, P >= 0 /\ Delta = liouville_threshold c + P.

(* Prove that both definitions are equivalent *)
Lemma continuous_spectrum_equiv : forall c Delta : R,
  in_continuous_spectrum c Delta <-> in_continuous_spectrum_alt c Delta.
Proof.
  intros c Delta.
  split.
  - intro H.
    exists (Delta - liouville_threshold c).
    split.
    + unfold in_continuous_spectrum in H. lra.
    + lra.
  - intro H.
    unfold in_continuous_spectrum.
    destruct H as [P [HP HDelta]].
    lra.
Qed.
