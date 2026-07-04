From Coq Require Import Reals.
From Coq Require Import Psatz.
Open Scope R_scope.

(* Axiomatic definitions for Ryu-Takayanagi Formalization *)
Parameter BulkSpace : Type.
Parameter BoundarySpace : Type.

Parameter BoundaryRegion : Type.
Parameter BulkSurface : Type.

Parameter EntanglementEntropy : BoundaryRegion -> R.
Parameter Area : BulkSurface -> R.
Parameter NewtonConstant : R.
Axiom G_N_pos : NewtonConstant > 0.

Parameter HomologousSurfaces : BoundaryRegion -> BulkSurface -> Prop.
Parameter IsMinimalSurface : BoundaryRegion -> BulkSurface -> Prop.

Axiom MinimalIsHomologous : forall (A : BoundaryRegion) (gamma : BulkSurface),
  IsMinimalSurface A gamma -> HomologousSurfaces A gamma.

Axiom RyuTakayanagiFormula : forall (A : BoundaryRegion) (gamma : BulkSurface),
  IsMinimalSurface A gamma ->
  EntanglementEntropy A = (Area gamma) / (4 * NewtonConstant).

Theorem RyuTakayanagi_AreaMapping :
  forall (A : BoundaryRegion) (gamma : BulkSurface),
    IsMinimalSurface A gamma ->
    Area gamma = 4 * NewtonConstant * EntanglementEntropy A.
Proof.
  intros A gamma Hmin.
  pose proof (RyuTakayanagiFormula A gamma Hmin) as H.
  pose proof G_N_pos as Hg.
  nra.
Qed.
