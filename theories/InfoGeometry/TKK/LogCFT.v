Require Import Reals.
Require Import Psatz.
Open Scope R_scope.

Definition L0 (h t : R) : R * R * R * R :=
  (h, 1, 0, h).

(* Matrix multiplication for upper triangular Jordan blocks:
   [h, 1] * [h, 1]
   [0, h]   [0, h]
   We define exp(-t L0) as exp(-ht) * [1, -t; 0, 1] *)

Definition exp_minus_tL0 (h t : R) : R * R * R * R :=
  let e := exp (- h * t) in
  (e * 1, e * (-t), 0, e * 1).

(* We just formalize that the 1,2 entry is proportional to -t exp(-ht),
   which represents the logarithmic mixing term in logCFT correlators. *)

Theorem log_cft_mixing :
  forall h t : R,
  let '(m11, m12, m21, m22) := exp_minus_tL0 h t in
  m12 = -t * exp (- h * t).
Proof.
  intros.
  unfold exp_minus_tL0.
  nra.
Qed.
