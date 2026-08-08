Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Definition Point := (Z * Z)%type.

Fixpoint shoelace_helper (l : list Point) (p0 : Point) : Z :=
  match l with
  | nil => 0
  | p1 :: nil => let (x1, y1) := p1 in
                 let (x0, y0) := p0 in
                 (x1 * y0 - y1 * x0)
  | p1 :: (p2 :: _) as rest =>
      let (x1, y1) := p1 in
      let (x2, y2) := p2 in
      (x1 * y2 - y1 * x2) + shoelace_helper rest p0
  end.

Definition shoelace_formula (polygon : list Point) : Z :=
  match polygon with
  | nil => 0
  | p0 :: _ => shoelace_helper polygon p0
  end.
