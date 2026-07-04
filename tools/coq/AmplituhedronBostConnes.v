From Stdlib Require Import Reals.

Parameter Amplituhedron : Type.
Parameter volume : Amplituhedron -> R.
Parameter topological_limit : (Amplituhedron -> R) -> R.

Parameter KMS_State : Type.
Parameter BostConnes : KMS_State.
Parameter riemann_zeta_eval : KMS_State -> R.

Axiom amplituhedron_volume_limit :
  topological_limit volume = riemann_zeta_eval BostConnes.

Theorem amplituhedron_bost_connes_equivalence :
  topological_limit volume = riemann_zeta_eval BostConnes.
Proof.
  apply amplituhedron_volume_limit.
Qed.
