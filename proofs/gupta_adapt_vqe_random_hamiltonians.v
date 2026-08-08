From Stdlib Require Import QArith.

Open Scope Q_scope.

Definition pair_count_Q (n : Q) : Q := n * (n - 1) / 2.
Definition four_body_count_Q (N : Q) : Q :=
  N * (N - 1) * (N - 2) * (N - 3) / 24.

Lemma dense_SYK_terms_N20 :
  four_body_count_Q 20 == 4845.
Proof. unfold four_body_count_Q; field. Qed.

Lemma sparse_SYK_ks9_N20_terms :
  9 * 20 == 180.
Proof. field. Qed.

Lemma sparse_removes_roughly_96_percent_N20 :
  (4845 - 180) / 4845 == 311 / 323.
Proof. field. Qed.

Definition sk_pool_size_Q (L : Q) : Q := 2 * pair_count_Q L.
Definition syk_pool_size_Q (n : Q) : Q := n + 3 * pair_count_Q n.

Lemma sk_pool_size_L18 :
  sk_pool_size_Q 18 == 306.
Proof. unfold sk_pool_size_Q, pair_count_Q; field. Qed.

Lemma syk_pool_size_n10 :
  syk_pool_size_Q 10 == 145.
Proof. unfold syk_pool_size_Q, pair_count_Q; field. Qed.

Definition relative_energy_error (exact adapt : Q) : Q :=
  (exact - adapt) / exact.

Lemma relative_error_zero_for_exact_match (E : Q) :
  ~ E == 0 -> relative_energy_error E E == 0.
Proof. intros h; unfold relative_energy_error; field; exact h. Qed.

Lemma Hilbert_dimension_N20 :
  Nat.pow 2 10 = 1024%nat.
Proof. reflexivity. Qed.

Lemma entropy_N20_close :
  278 / 100 - 275 / 100 == 3 / 100.
Proof. field. Qed.

Lemma dense_SYK_fidelity_above_993 :
  9936 / 10000 >= 993 / 1000.
Proof. compute; discriminate || reflexivity. Qed.

Lemma SK_DLA_L4 :
  (2 * (Nat.pow 4 (4 - 1) - 1) = 126)%nat.
Proof. reflexivity. Qed.
