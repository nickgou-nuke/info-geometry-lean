(* Coq formalization of Zorn Idempotents *)
Require Import Reals.
Require Import Matrix.

Section ZornIsospin.

(* We define the abstract idempotents for Proton and Neutron *)
Variable Eplus Eminus : R.

(* Orthogonal idempotents *)
Hypothesis Eplus_proj : Eplus * Eplus = Eplus.
Hypothesis Eminus_proj : Eminus * Eminus = Eminus.
Hypothesis Orthogonal : Eplus * Eminus = 0.

Lemma Isospin_Independence : Eplus * (Eplus * Eminus) = 0.
Proof.
  rewrite Orthogonal.
  apply Rmult_0_r.
Qed.

End ZornIsospin.
