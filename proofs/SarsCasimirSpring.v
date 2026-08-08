From Coq Require Import ZArith List String Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition casimir_on_shell (m : Z) : Z := - (m*m).
Definition stiffness_from_casimir (C : Z) : Z := -C.
Definition mass_stiffness (m : Z) : Z := m*m.
Definition spring_potential2_from_casimir (C lam : Z) : Z := -C * lam * lam.
Definition spring_potential2_mass (m lam : Z) : Z := m*m*lam*lam.
Definition restoring_force_from_casimir (C lam : Z) : Z := C*lam.
Definition restoring_force_mass (m lam : Z) : Z := -m*m*lam.
Definition dilation_casimir_bracket (C : Z) : Z := 2*C.

Inductive Concept := Poincare_Casimir_On_Shell | Mass_Shell_Coadjoint_Orbit | Souriau_Entropic_Leaf | Conformal_Dilation_Spring | Dilaton_Transverse_Flow | Compton_Equilibrium_Scale.
Inductive Edge := labels | identical_to | gives_stiffness | resists | crosses | restores_to.
Definition edgeHolds a e b :=
  match a,e,b with
  | Poincare_Casimir_On_Shell, labels, Mass_Shell_Coadjoint_Orbit => true
  | Mass_Shell_Coadjoint_Orbit, identical_to, Souriau_Entropic_Leaf => true
  | Poincare_Casimir_On_Shell, gives_stiffness, Conformal_Dilation_Spring => true
  | Conformal_Dilation_Spring, resists, Dilaton_Transverse_Flow => true
  | Dilaton_Transverse_Flow, crosses, Souriau_Entropic_Leaf => true
  | Conformal_Dilation_Spring, restores_to, Compton_Equilibrium_Scale => true
  | _,_,_ => false
  end.

Theorem casimir_spring_kernel :
  (forall m, stiffness_from_casimir (casimir_on_shell m) = mass_stiffness m) /\
  (forall m lam, spring_potential2_from_casimir (casimir_on_shell m) lam = spring_potential2_mass m lam) /\
  (forall m lam, restoring_force_from_casimir (casimir_on_shell m) lam = restoring_force_mass m lam) /\
  mass_stiffness 0 = 0 /\
  (forall m, 0 <= mass_stiffness m) /\
  (forall m lam, 0 <= spring_potential2_mass m lam) /\
  (forall m, spring_potential2_mass m 0 = 0) /\
  (forall C, dilation_casimir_bracket C = 2*C).
Proof.
  repeat split; intros; unfold stiffness_from_casimir, casimir_on_shell, mass_stiffness,
    spring_potential2_from_casimir, spring_potential2_mass, restoring_force_from_casimir,
    restoring_force_mass, dilation_casimir_bracket; try nia; reflexivity.
Qed.

Theorem casimir_spring_graph_kernel :
  edgeHolds Poincare_Casimir_On_Shell labels Mass_Shell_Coadjoint_Orbit = true /\
  edgeHolds Mass_Shell_Coadjoint_Orbit identical_to Souriau_Entropic_Leaf = true /\
  edgeHolds Poincare_Casimir_On_Shell gives_stiffness Conformal_Dilation_Spring = true /\
  edgeHolds Conformal_Dilation_Spring resists Dilaton_Transverse_Flow = true /\
  edgeHolds Dilaton_Transverse_Flow crosses Souriau_Entropic_Leaf = true /\
  edgeHolds Conformal_Dilation_Spring restores_to Compton_Equilibrium_Scale = true.
Proof. compute; repeat split; reflexivity. Qed.
