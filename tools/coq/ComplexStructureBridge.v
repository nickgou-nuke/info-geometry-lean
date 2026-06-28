(* Coq/Rocq Formalization: Finite Complex Structure Bridge *)

From Stdlib Require Import Reals Psatz.
Open Scope R_scope.

Section ComplexStructureBridge.

  Record HestenesSpinor : Type := {
    hs_scalar : R;
    hs_bivector : R
  }.

  Definition hestenes_one : HestenesSpinor :=
    {| hs_scalar := 1; hs_bivector := 0 |}.

  Definition hestenes_i : HestenesSpinor :=
    {| hs_scalar := 0; hs_bivector := 1 |}.

  Definition hestenes_mul (z1 z2 : HestenesSpinor) : HestenesSpinor :=
    {| hs_scalar := hs_scalar z1 * hs_scalar z2 - hs_bivector z1 * hs_bivector z2;
       hs_bivector := hs_scalar z1 * hs_bivector z2 + hs_bivector z1 * hs_scalar z2 |}.

  Lemma hestenes_i_squared :
    hestenes_mul hestenes_i hestenes_i =
    {| hs_scalar := -1; hs_bivector := 0 |}.
  Proof.
    unfold hestenes_mul, hestenes_i.
    simpl.
    f_equal; ring.
  Qed.

  Record C : Type := {
    Re : R;
    Im : R
  }.

  Definition Ceq (z w : C) : Prop := (Re z = Re w) /\
                                 (Im z = Im w).
  Infix "==" := Ceq (at level 70).

  Definition Cmake (x y : R) : C := {| Re := x; Im := y |}.

  Definition Cplus (z w : C) : C :=
    Cmake (Re z + Re w) (Im z + Im w).

  Definition Copp (z : C) : C :=
    Cmake (- Re z) (- Im z).

  Definition Cmult (z w : C) : C :=
    Cmake (Re z * Re w - Im z * Im w)
          (Re z * Im w + Im z * Re w).

  Definition Cscale (r : R) (z : C) : C :=
    Cmake (r * Re z) (r * Im z).

  Infix "+c" := Cplus (at level 50).
  Infix "*c" := Cmult (at level 40).

  Definition C0 : C := Cmake 0 0.
  Definition C1 : C := Cmake 1 0.
  Definition I : C := Cmake 0 1.

  Lemma Ceq_refl : forall z, z == z.
  Proof. intros z; split; reflexivity. Qed.

  Lemma complex_i_squared :
    (I *c I) == Cmake (-1) 0.
  Proof.
    unfold I, Cmult, Cmake, Ceq.
    simpl.
    split; ring.
  Qed.

  Definition hestenes_to_complex (z : HestenesSpinor) : C :=
    Cmake (hs_scalar z) (hs_bivector z).

  Definition complex_to_hestenes (z : C) : HestenesSpinor :=
    {| hs_scalar := Re z; hs_bivector := Im z |}.

  Theorem hestenes_complex_isomorphism :
    forall z1 z2 : HestenesSpinor,
      hestenes_to_complex (hestenes_mul z1 z2) ==
      (hestenes_to_complex z1 *c hestenes_to_complex z2).
  Proof.
    intros [a b] [c d]; split; simpl; ring.
  Qed.

  Theorem hestenes_complex_inverse :
    forall z : HestenesSpinor,
      complex_to_hestenes (hestenes_to_complex z) = z.
  Proof.
    intros [a b]; reflexivity.
  Qed.

  Record Cl11Element : Type := {
    cl_scalar : R;
    cl_e1 : R
  }.

  Definition cl11_one : Cl11Element :=
    {| cl_scalar := 1; cl_e1 := 0 |}.

  Definition cl11_e1 : Cl11Element :=
    {| cl_scalar := 0; cl_e1 := 1 |}.

  Definition cl11_mul (x1 x2 : Cl11Element) : Cl11Element :=
    {| cl_scalar := cl_scalar x1 * cl_scalar x2 - cl_e1 x1 * cl_e1 x2;
       cl_e1 := cl_scalar x1 * cl_e1 x2 + cl_e1 x1 * cl_scalar x2 |}.

  Lemma cl11_e1_squared :
    cl11_mul cl11_e1 cl11_e1 =
    {| cl_scalar := -1; cl_e1 := 0 |}.
  Proof.
    unfold cl11_mul, cl11_e1.
    simpl.
    f_equal; ring.
  Qed.

  Definition hestenes_to_cl11 (z : HestenesSpinor) : Cl11Element :=
    {| cl_scalar := hs_scalar z; cl_e1 := hs_bivector z |}.

  Definition cl11_to_hestenes (x : Cl11Element) : HestenesSpinor :=
    {| hs_scalar := cl_scalar x; hs_bivector := cl_e1 x |}.

  Theorem hestenes_cl11_isomorphism :
    forall z1 z2 : HestenesSpinor,
      hestenes_to_cl11 (hestenes_mul z1 z2) =
      cl11_mul (hestenes_to_cl11 z1) (hestenes_to_cl11 z2).
  Proof.
    intros [a b] [c d]; reflexivity.
  Qed.

  Definition tripotent (T : HestenesSpinor) : Prop :=
    hestenes_mul T (hestenes_mul T T) = T.

  Lemma tripotent_examples :
    (tripotent hestenes_one) /\
    (tripotent {| hs_scalar := 0; hs_bivector := 0 |}) /\
    (~ tripotent hestenes_i).
  Proof.
    split.
    - unfold tripotent, hestenes_one, hestenes_mul.
      simpl. f_equal; ring.
    - split.
      + unfold tripotent, hestenes_mul.
        simpl. f_equal; ring.
      + unfold tripotent, hestenes_i, hestenes_mul.
        simpl. intro H. inversion H. lra.
  Qed.

  Theorem finite_complex_structure_bridge_packet :
    (hestenes_mul hestenes_i hestenes_i = {| hs_scalar := -1; hs_bivector := 0 |}) /\
    ((I *c I) == Cmake (-1) 0) /\
    (cl11_mul cl11_e1 cl11_e1 = {| cl_scalar := -1; cl_e1 := 0 |}) /\
    (forall z1 z2, hestenes_to_complex (hestenes_mul z1 z2) ==
                   hestenes_to_complex z1 *c hestenes_to_complex z2) /\
    (forall z1 z2, hestenes_to_cl11 (hestenes_mul z1 z2) =
                   cl11_mul (hestenes_to_cl11 z1) (hestenes_to_cl11 z2)).
  Proof.
    split.
    - apply hestenes_i_squared.
    - split.
      + apply complex_i_squared.
      + split.
        * apply cl11_e1_squared.
        * split.
          { apply hestenes_complex_isomorphism. }
          { apply hestenes_cl11_isomorphism. }
  Qed.

  Definition mersenne (p : nat) : nat := 2 ^ p - 1.

  Lemma mersenne_decomposition_137 :
    (mersenne 2 + mersenne 3 + mersenne 7)%nat = 137%nat.
  Proof.
    reflexivity.
  Qed.

  Definition su3_dimension : nat := mersenne 2.

  Lemma su3_dim_eq_3 :
    su3_dimension = 3%nat.
  Proof.
    reflexivity.
  Qed.

End ComplexStructureBridge.

Print finite_complex_structure_bridge_packet.
