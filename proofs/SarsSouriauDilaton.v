From Coq Require Import ZArith List String Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive Concept := Souriau_Lie_Group_Thermodynamics | Sars_Weyl_Colimit | Entropic_Leaflet | Dilaton_Weyl_Gauge_Vector | Partition_Function_Normalization | Orthogonal_Entropy_Transport.
Inductive Edge := has_leaflet | tangent_reversible_flow | parameterizes_scale_orthogonal_to_leaves | normalizes_by_partition_function | generates_orthogonal_entropy_transport.

Definition edgeHolds (a : Concept) (e : Edge) (b : Concept) : bool :=
  match a,e,b with
  | Souriau_Lie_Group_Thermodynamics, has_leaflet, Entropic_Leaflet => true
  | Entropic_Leaflet, tangent_reversible_flow, Sars_Weyl_Colimit => true
  | Sars_Weyl_Colimit, parameterizes_scale_orthogonal_to_leaves, Souriau_Lie_Group_Thermodynamics => true
  | Partition_Function_Normalization, normalizes_by_partition_function, Dilaton_Weyl_Gauge_Vector => true
  | Dilaton_Weyl_Gauge_Vector, generates_orthogonal_entropy_transport, Orthogonal_Entropy_Transport => true
  | _,_,_ => false
  end.

Definition partition_rescale (Z rho w : Z) : Prop := Z*rho = w.
Definition dilaton_square_weyl_scale (phi scale : Z) : Prop := phi*phi = scale.
Definition entropy_production (S0 S1 : Z) : Z := Z.abs (S1-S0).

Theorem entropy_production_nonneg : forall S0 S1, 0 <= entropy_production S0 S1.
Proof. intros; unfold entropy_production; apply Z.abs_nonneg. Qed.

Theorem edge_kernel :
  edgeHolds Souriau_Lie_Group_Thermodynamics has_leaflet Entropic_Leaflet = true /\
  edgeHolds Entropic_Leaflet tangent_reversible_flow Sars_Weyl_Colimit = true /\
  edgeHolds Sars_Weyl_Colimit parameterizes_scale_orthogonal_to_leaves Souriau_Lie_Group_Thermodynamics = true /\
  edgeHolds Partition_Function_Normalization normalizes_by_partition_function Dilaton_Weyl_Gauge_Vector = true /\
  edgeHolds Dilaton_Weyl_Gauge_Vector generates_orthogonal_entropy_transport Orthogonal_Entropy_Transport = true.
Proof. compute; repeat split; reflexivity. Qed.

Theorem souriau_dilaton_kernel :
  (forall S0 S1, 0 <= entropy_production S0 S1) /\
  edgeHolds Souriau_Lie_Group_Thermodynamics has_leaflet Entropic_Leaflet = true /\
  edgeHolds Entropic_Leaflet tangent_reversible_flow Sars_Weyl_Colimit = true /\
  edgeHolds Sars_Weyl_Colimit parameterizes_scale_orthogonal_to_leaves Souriau_Lie_Group_Thermodynamics = true /\
  edgeHolds Dilaton_Weyl_Gauge_Vector generates_orthogonal_entropy_transport Orthogonal_Entropy_Transport = true.
Proof.
  repeat split;
  try apply entropy_production_nonneg;
  compute; reflexivity.
Qed.
