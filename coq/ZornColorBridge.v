Inductive mersenne_mode : Type :=
| M2
| M3
| M7.

Definition mode_dimension (m : mersenne_mode) : nat :=
  match m with
  | M2 => 3
  | M3 => 7
  | M7 => 127
  end.

Definition coupling137 : nat := 137.

Record zorn_slot : Type := {
  slot_dim : nat;
  is_color : bool;
  is_anticolor : bool;
}.

Definition F (m : mersenne_mode) : zorn_slot :=
  match m with
  | M2 => {| slot_dim := 3; is_color := true; is_anticolor := false |}
  | M3 => {| slot_dim := 7; is_color := false; is_anticolor := false |}
  | M7 => {| slot_dim := 127; is_color := false; is_anticolor := false |}
  end.

Theorem mode_dimension_M2 : mode_dimension M2 = 3.
Proof. reflexivity. Qed.

Theorem mode_dimension_M3 : mode_dimension M3 = 7.
Proof. reflexivity. Qed.

Theorem mode_dimension_M7 : mode_dimension M7 = 127.
Proof. reflexivity. Qed.

Theorem coupling137_decomposition :
  coupling137 = mode_dimension M2 + mode_dimension M3 + mode_dimension M7.
Proof. reflexivity. Qed.

Theorem F_M2_slot_dim : slot_dim (F M2) = 3.
Proof. reflexivity. Qed.

Theorem F_M2_is_color : is_color (F M2) = true.
Proof. reflexivity. Qed.

(* Honest scope boundary: this file packages only the finite 3/7/127 bridge. *)
