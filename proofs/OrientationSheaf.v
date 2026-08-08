Require Import Coq.Init.Logic.
Require Import Coq.Sets.Ensembles.

Section OrientationSheaf.

  Variable M : Type. (* Pseudo-Riemannian manifold *)
  
  Inductive Orientation :=
    | Pos : Orientation
    | Neg : Orientation.

  Definition mul_ori (o1 o2 : Orientation) : Orientation :=
    match o1, o2 with
    | Pos, Pos => Pos
    | Neg, Neg => Pos
    | _, _ => Neg
    end.

  (* Local sections of the orientation sheaf *)
  Variable OpenSets : Ensemble M -> Prop.

  Record OrientationSection (U : Ensemble M) := {
    section_val : M -> Orientation;
    is_continuous : True 
  }.

  Definition total_orientation {U : Ensemble M} 
    (sigma_plus sigma_minus : OrientationSection U) : OrientationSection U.
  Proof.
    refine {|
      section_val := fun x => mul_ori (section_val U sigma_plus x) (section_val U sigma_minus x);
      is_continuous := I
    |}.
  Defined.

End OrientationSheaf.
