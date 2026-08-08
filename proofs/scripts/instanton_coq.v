Require Import Reals.

Section AtiyahSinger.

Variable A : Type. (* Gauge Field *)
Variable n_L n_R : nat. (* Zero modes *)
Variable Q_top : Z.

(* Atiyah-Singer Index Theorem for QCD Vacuum *)
Axiom index_theorem : Z.of_nat n_L - Z.of_nat n_R = Q_top.

(* Banks-Casher Relation *)
Variable chiral_condensate : R.
Variable spectral_density_zero : R.
Axiom banks_casher : chiral_condensate = - (PI * spectral_density_zero).

End AtiyahSinger.
