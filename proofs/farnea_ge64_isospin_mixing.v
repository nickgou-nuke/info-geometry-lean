Require Import Coq.QArith.QArith.

Open Scope Q_scope.

Definition T3 (Z N : Q) : Q := (Z - N) / 2.
Definition mass_number (N Z : Q) : Q := N + Z.
Definition fusion_evaporation_mass (target projectile alpha_count : Q) : Q :=
  target + projectile - 4 * alpha_count.

Lemma Ge64_NZ : mass_number 32 32 == 64 /\ T3 32 32 == 0.
Proof. split; unfold mass_number, T3; field. Qed.

Lemma Ca40_S32_twoAlpha_to_Ge64 :
  fusion_evaporation_mass 40 32 2 == 64.
Proof. unfold fusion_evaporation_mass; field. Qed.

Definition large_delta : Q := -39 / 10.
Definition chi2_large : Q := 54 / 100.
Definition chi2_small : Q := 80 / 100.
Definition quadrupole_content (delta : Q) : Q := delta ^ 2 / (1 + delta ^ 2).

Lemma large_delta_statistically_favoured : chi2_large < chi2_small.
Proof. unfold chi2_large, chi2_small; vm_compute; reflexivity. Qed.

Lemma large_delta_quadrupole_content_exact :
  quadrupole_content large_delta == 1521 / 1621.
Proof. unfold quadrupole_content, large_delta; vm_compute; reflexivity. Qed.

Lemma large_delta_quadrupole_content_above_93_percent :
  93 / 100 < quadrupole_content large_delta.
Proof. unfold quadrupole_content, large_delta; vm_compute; reflexivity. Qed.

Definition tau9_upper_ps : Q := 4.
Definition tau7_ps : Q := 431 / 10.
Definition tau5_ps : Q := 242 / 10.
Definition lambda7_ps_inv : Q := 232 / 10000.

Lemma reported_lifetime_order : tau9_upper_ps < tau5_ps /\ tau5_ps < tau7_ps.
Proof. split; unfold tau9_upper_ps, tau5_ps, tau7_ps; vm_compute; reflexivity. Qed.

Lemma lambda7_reciprocal_window :
  43 < 1 / lambda7_ps_inv /\ 1 / lambda7_ps_inv < 432 / 10.
Proof. split; unfold lambda7_ps_inv; vm_compute; reflexivity. Qed.

Definition I1665 : Q := 567.
Definition I1048 : Q := 130.
Definition I747 : Q := 89.

Lemma branch_intensity_sum : I1665 + I1048 + I747 == 786.
Proof. unfold I1665, I1048, I747; field. Qed.

Lemma branch_1665_dominates : I1048 + I747 < I1665.
Proof. unfold I1665, I1048, I747; vm_compute; reflexivity. Qed.

Definition BE1_64Ge_Wu : Q := 247 / 1000000000.
Definition BM2_64Ge_Wu : Q := 606 / 100.
Definition BE1_66Ge_Wu : Q := 37 / 10000000.
Definition BM2_66Ge_Wu : Q := 39 / 10000.
Definition BM2_68Ge_Wu : Q := 71 / 100.

Lemma BE1_64_over_66_exact :
  BE1_64Ge_Wu / BE1_66Ge_Wu == 247 / 3700.
Proof. unfold BE1_64Ge_Wu, BE1_66Ge_Wu; field. Qed.

Lemma BE1_64_below_66 : BE1_64Ge_Wu < BE1_66Ge_Wu.
Proof. unfold BE1_64Ge_Wu, BE1_66Ge_Wu; vm_compute; reflexivity. Qed.

Lemma BM2_64_over_66_exact :
  BM2_64Ge_Wu / BM2_66Ge_Wu == 20200 / 13.
Proof. unfold BM2_64Ge_Wu, BM2_66Ge_Wu; field. Qed.

Lemma BM2_64_above_68 : BM2_68Ge_Wu < BM2_64Ge_Wu.
Proof. unfold BM2_68Ge_Wu, BM2_64Ge_Wu; vm_compute; reflexivity. Qed.

Definition BE2_64Ge_747_Wu : Q := 1.
Definition BE2_66Ge_886_Wu : Q := 4 / 10.

Lemma weak_E2_ratio :
  BE2_64Ge_747_Wu / BE2_66Ge_886_Wu == 5 / 2.
Proof. unfold BE2_64Ge_747_Wu, BE2_66Ge_886_Wu; field. Qed.

Definition alpha_difference (alpha_i alpha_f : Q) : Q := alpha_i - alpha_f.
Definition eq6_amplitude_scale (alpha_i alpha_f : Q) : Q :=
  (2 / 3) * (alpha_difference alpha_i alpha_f) ^ 2.
Definition eq7_BE1_64_from_66 (alpha2 BE1_66 : Q) : Q :=
  (8 / 3) * alpha2 * BE1_66.
Definition alpha2_from_BE1 (BE1_64 BE1_66 : Q) : Q :=
  (3 / 8) * (BE1_64 / BE1_66).
Definition alpha2_extracted : Q := alpha2_from_BE1 BE1_64Ge_Wu BE1_66Ge_Wu.

Lemma eq7_alpha_symmetric_mixing :
  eq6_amplitude_scale 1 (-1) == 8 / 3.
Proof. unfold eq6_amplitude_scale, alpha_difference; field. Qed.

Lemma alpha2_extracted_exact : alpha2_extracted == 741 / 29600.
Proof. unfold alpha2_extracted, alpha2_from_BE1, BE1_64Ge_Wu, BE1_66Ge_Wu; field. Qed.

Lemma alpha2_extracted_percent : 100 * alpha2_extracted == 741 / 296.
Proof. unfold alpha2_extracted, alpha2_from_BE1, BE1_64Ge_Wu, BE1_66Ge_Wu; field. Qed.

Lemma alpha2_reported_window : 24 / 1000 < alpha2_extracted /\ alpha2_extracted < 26 / 1000.
Proof.
  split; unfold alpha2_extracted, alpha2_from_BE1, BE1_64Ge_Wu, BE1_66Ge_Wu;
  vm_compute; reflexivity.
Qed.

Lemma eq7_reconstructs_BE1_64 :
  eq7_BE1_64_from_66 alpha2_extracted BE1_66Ge_Wu == BE1_64Ge_Wu.
Proof. unfold eq7_BE1_64_from_66, alpha2_extracted, alpha2_from_BE1, BE1_64Ge_Wu, BE1_66Ge_Wu; field. Qed.
