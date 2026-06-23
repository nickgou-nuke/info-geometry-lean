Require Import Reals.

Local Open Scope R_scope.

(* The Legendre Model structure *)
Record LegendreModel : Type := {
  psi : R -> R;
  grad : R -> R;
  phi : R -> R;
  fenchelGap : R -> R -> R;
  
  fenchelGap_def : forall theta eta,
    fenchelGap theta eta = psi theta + phi eta - theta * eta;
  fenchelGap_eq_zero : forall theta eta,
    fenchelGap theta eta = 0 <-> eta = grad theta;
}.

(* Theorem 1: Fenchel Gap Zero Condition *)
Theorem fenchelGap_eq_zero_iff_contact (L : LegendreModel) (theta eta : R) :
  fenchelGap L theta eta = 0 <-> eta = grad L theta.
Proof.
  apply fenchelGap_eq_zero.
Qed.

(* Velocity and Trace representation *)
Record FluidVelocityContext : Type := {
  collapseToBaseVelocity : R -> R;
  trace : R -> R;
  
  collapse_linear : forall beta K,
    collapseToBaseVelocity (beta * K) = beta * collapseToBaseVelocity K;
  trace_linear : forall beta V,
    trace (beta * V) = beta * trace V;
}.

Theorem trace_madelung_velocity_eq (C : FluidVelocityContext) (beta K : R) :
  trace C (collapseToBaseVelocity C (beta * K)) = beta * trace C (collapseToBaseVelocity C K).
Proof.
  rewrite (collapse_linear C).
  rewrite (trace_linear C).
  reflexivity.
Qed.
