From Stdlib Require Import QArith.
Open Scope Q_scope.

Definition total_med (VCM VCr ell ls : Q) : Q :=
  VCM + VCr + ell + ls.

Lemma epsilonLL_gap_g9_f5_reduction :
  (-95) - (-58) == -37.
Proof. vm_compute; reflexivity. Qed.

Lemma epsilonLS_gap_g9_f5_reduction :
  (-66) - 66 == -132.
Proof. vm_compute; reflexivity. Qed.

Definition radial_med (m9 mJ : Q) : Q :=
  280 * (m9 / 2 - mJ / 2).

Lemma radial_med_positive_when_p32_decreases :
  radial_med 4 3 == 140.
Proof. vm_compute; reflexivity. Qed.

Lemma g9_total_jump_at_25half :
  2 + 1 == 3.
Proof. vm_compute; reflexivity. Qed.

Lemma highSpin_MED_model_exact :
  total_med (-40) 140 0 (-132) == -32.
Proof. vm_compute; reflexivity. Qed.

Lemma spinOrbit_radial_interference :
  140 + (-132) == 8.
Proof. vm_compute; reflexivity. Qed.
