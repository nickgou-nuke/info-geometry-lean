From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Definition surprisal_quadratic (x : Z) : Z := x*x.
Definition weak_denominator_same : Z := 1.
Definition weak_denominator_orthogonal : Z := 0.
Definition weak_numerator_same (k0 : Z) : Z := k0.
Definition weak_value_same (k0 : Z) : Z := weak_numerator_same k0 / weak_denominator_same.
Inductive TraceStatus := NotTraceClassInInfiniteGNS.
Inductive MeasurementRegime := WeakCoupling.

Theorem surprisal_quadratic_nonneg : forall x, 0 <= surprisal_quadratic x.
Proof. intros; unfold surprisal_quadratic; nia. Qed.

Theorem surprisal_quadratic_zero : surprisal_quadratic 0 = 0.
Proof. compute; reflexivity. Qed.

Definition diag_quad (a b v0 v1 : Z) : Z := a*v0*v0 + b*v1*v1.

Theorem diag_quad_nonneg : forall a b v0 v1,
  0 <= a -> 0 <= b -> 0 <= diag_quad a b v0 v1.
Proof. intros; unfold diag_quad; nia. Qed.

Theorem weak_denominator_same_eq_1 : weak_denominator_same = 1.
Proof. compute; reflexivity. Qed.

Theorem weak_denominator_orthogonal_eq_0 : weak_denominator_orthogonal = 0.
Proof. compute; reflexivity. Qed.

Theorem weak_value_same_eq : forall k0, weak_value_same k0 = k0.
Proof. intro; unfold weak_value_same, weak_numerator_same, weak_denominator_same; rewrite Z.div_1_r; reflexivity. Qed.

Theorem modular_weak_value_kernel :
  (forall x, 0 <= surprisal_quadratic x) /\
  surprisal_quadratic 0 = 0 /\
  weak_denominator_same = 1 /\
  weak_denominator_orthogonal = 0 /\
  (forall k0, weak_value_same k0 = k0) /\
  TraceStatus /\ MeasurementRegime.
Proof.
  repeat split;
  try apply surprisal_quadratic_nonneg;
  try exact surprisal_quadratic_zero;
  try exact weak_denominator_same_eq_1;
  try exact weak_denominator_orthogonal_eq_0;
  try apply weak_value_same_eq;
  try exact NotTraceClassInInfiniteGNS;
  exact WeakCoupling.
Qed.
