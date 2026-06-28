Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Reals.Reals.

(* 1. Defines Inductive Nucleon *)
Inductive Nucleon : Type :=
| Proton : Nucleon
| Neutron : Nucleon.

(* 2. Defines isospin projection T_z *)
Definition T_z (n : Nucleon) : Q :=
  match n with
  | Proton => (1#2)%Q
  | Neutron => (-(1)#2)%Q
  end.

(* 3. Defines a Record MirrorNucleus *)
Record MirrorNucleus := {
  A : nat;
  Z : nat;
  N : nat;
  is_mirror : A = (Z + N)%nat
}.

Open Scope Z_scope.

(* 4. Defines formulas for MED, CED, TED using integers (Z) *)
Definition MED (E_minus_Tz E_plus_Tz : Z) : Z :=
  E_minus_Tz - E_plus_Tz.

Definition CED (E_c_greater E_c_lesser : Z) : Z :=
  E_c_greater - E_c_lesser.

Definition TED (E_minus_1 E_plus_1 E_0 : Z) : Z :=
  E_minus_1 + E_plus_1 - 2 * E_0.

Close Scope Z_scope.
Open Scope R_scope.

(* 5. Defines effective charges e_pi, e_nu and transition strengths. *)
Record EffectiveCharges := {
  e_pi : R;
  e_nu : R
}.

Record TransitionMatrixElements := {
  M_p : R;
  M_n : R
}.

Definition TransitionStrength (M : TransitionMatrixElements) (e : EffectiveCharges) : R :=
  (M.(M_p) * e.(e_pi) + M.(M_n) * e.(e_nu))^2.

(* 6. Defines the Thomas-Ehrman shift phenomenon. *)
Record LevelShift := {
  energy_proton_rich : R;
  energy_neutron_rich : R;
  coulomb_expected_diff : R
}.

Definition ThomasEhrmanShift (lvl : LevelShift) : R :=
  lvl.(energy_proton_rich) - lvl.(energy_neutron_rich) - lvl.(coulomb_expected_diff).

Definition has_ThomasEhrmanShift (lvl : LevelShift) : Prop :=
  ThomasEhrmanShift lvl <> 0.

(* 7. Defines the symmetry energy correlation L. *)
Record EOSParameters := {
  S_0 : R;
  L   : R
}.

Definition symmetry_energy (eos : EOSParameters) (rho rho_0 : R) : R :=
  eos.(S_0) + eos.(L) / 3 * ((rho - rho_0) / rho_0).

Close Scope R_scope.
