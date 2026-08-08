From Coq Require Import ZArith List String Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive Concept := Metriplectic_Evolution | WeylSystem | Wasserstein_Gradient_Flow | Itakura_Saito_Divergence | Legendre_Fenchel_Duality.
Inductive Edge := symplectic_part | metric_part | minimizes_distortion | generated_by | stabilizes_vacuum.

Definition edgeHolds (a : Concept) (e : Edge) (b : Concept) : bool :=
  match a,e,b with
  | Metriplectic_Evolution, symplectic_part, WeylSystem => true
  | Metriplectic_Evolution, metric_part, Wasserstein_Gradient_Flow => true
  | Wasserstein_Gradient_Flow, minimizes_distortion, Itakura_Saito_Divergence => true
  | Itakura_Saito_Divergence, generated_by, Legendre_Fenchel_Duality => true
  | Legendre_Fenchel_Duality, stabilizes_vacuum, Metriplectic_Evolution => true
  | _,_,_ => false
  end.

Definition surprisal_quadratic (n : Z) : Z := Z.abs n.
Definition fenchel_quadratic_gap (x u : Z) : Z := Z.abs (x-u).
Definition burg_quadratic_gap (x u : Z) : Z := Z.abs (x-u).

Theorem fenchel_quadratic_nonneg : forall x u, 0 <= fenchel_quadratic_gap x u.
Proof. intros; unfold fenchel_quadratic_gap; apply Z.abs_nonneg. Qed.

Theorem burg_quadratic_nonneg : forall x u, 0 <= burg_quadratic_gap x u.
Proof. intros; unfold burg_quadratic_gap; apply Z.abs_nonneg. Qed.

Theorem vacuum_zero : fenchel_quadratic_gap 0 0 = 0 /\ burg_quadratic_gap 0 0 = 0.
Proof. compute; split; reflexivity. Qed.

Theorem metriplectic_ot_kernel :
  (forall x u, 0 <= fenchel_quadratic_gap x u) /\
  (forall x u, 0 <= burg_quadratic_gap x u) /\
  fenchel_quadratic_gap 0 0 = 0 /\
  burg_quadratic_gap 0 0 = 0 /\
  edgeHolds Metriplectic_Evolution symplectic_part WeylSystem = true /\
  edgeHolds Metriplectic_Evolution metric_part Wasserstein_Gradient_Flow = true /\
  edgeHolds Wasserstein_Gradient_Flow minimizes_distortion Itakura_Saito_Divergence = true /\
  edgeHolds Itakura_Saito_Divergence generated_by Legendre_Fenchel_Duality = true.
Proof.
  repeat split;
  try apply fenchel_quadratic_nonneg;
  try apply burg_quadratic_nonneg;
  compute; reflexivity.
Qed.
