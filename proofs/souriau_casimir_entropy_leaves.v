From Stdlib Require Import QArith.

Open Scope Q_scope.

Definition isospin_casimir (I : Q) : Q := I * (I + 1).
Definition poincare_mass_casimir (mass_sq : Q) : Q := - mass_sq.
Definition dilation_spring_stiffness (C1 : Q) : Q := - C1.
Definition legendre_entropy (logZ pairing : Q) : Q := logZ + pairing.

Lemma isospin_half_casimir :
  isospin_casimir (1 / 2) == 3 / 4.
Proof. unfold isospin_casimir; field. Qed.

Lemma isospin_flip_tz_sum :
  -1 / 2 + 1 / 2 == 0.
Proof. field. Qed.

Lemma dilation_spring_stiffness_massSq :
  dilation_spring_stiffness (poincare_mass_casimir 67) == 67.
Proof. unfold dilation_spring_stiffness, poincare_mass_casimir; field. Qed.

Definition ivgmr_coefficient (A e R deltaE0 : Q) : Q :=
  ((A - 1) * e * e) / (4 * R * deltaE0).

Definition ivgmr_one_body_radial (ri R : Q) : Q := ri * ri * ri / (R * R).

Definition ivgmr_two_body_radial (ri rj R : Q) : Q :=
  ri * rj * rj / (R * R * R).

Definition induced_isoscalar_e1_kernel
    (A e R deltaE0 ri rj : Q) : Q :=
  ivgmr_coefficient A e R deltaE0 *
    (ivgmr_one_body_radial ri R + ivgmr_two_body_radial ri rj R).

Lemma A67_IVGMR_kernel_exact :
  induced_isoscalar_e1_kernel 67 1 1 20 1 1 == 33 / 20.
Proof.
  unfold induced_isoscalar_e1_kernel, ivgmr_coefficient,
    ivgmr_one_body_radial, ivgmr_two_body_radial.
  vm_compute.
  reflexivity.
Qed.

Definition entropy_from_casimirs (a b c C1 C2 : Q) : Q :=
  a * C1 + b * C2 + c.

Lemma same_casimir_same_entropy (a b c C1 C2 : Q) :
  entropy_from_casimirs a b c C1 C2 ==
    entropy_from_casimirs a b c C1 C2.
Proof. reflexivity. Qed.
