Require Import Coq.Init.Logic.

Parameter Manifold : Type.
Parameter K_Theory : Type.
Parameter Cohomology : Type.

Parameter torsion_class : Manifold -> K_Theory.
Parameter integral_cohomology_map : K_Theory -> Cohomology.

Definition mapped_torsion (M : Manifold) : Cohomology :=
  integral_cohomology_map (torsion_class M).

Theorem torsion_mapping : forall M : Manifold, mapped_torsion M = integral_cohomology_map (torsion_class M).
Proof.
  intros.
  reflexivity.
Qed.
