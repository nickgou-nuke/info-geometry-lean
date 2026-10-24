# Actual finite real Fock displacement norm: contract only

No implementation/build/live edits. Source DeBruijnRotorAlternationCycle SHA256
 a9b62319e89aa9f714606e3871a46298d45139b6d8b61755474455a4423a363a;
FiniteRealFockAdjoint SHA256
 f83ccc4ca27cfd634bb8d0122f033e13b29ea30729a3cca546b85e6890233b2c.
FiveStreamMaster and all foreign work remain untouched.

Use native FiniteFockCLMReflexivePair and FiniteRealFockAdjoint (transitively
already imported), original SpinorSpace(Vector n), local fockNormedAddCommGroup
and fockInnerProductSpace, D=fockIntActionCLM n i, C=fockExtActionCLM n i.
Only local notation Q=D*C and P=movingPolePlus c s D C; no new carrier or metric.
For arbitrary c s:Real with c*c+s*s=1, target for EVERY original spinor x:

    ‖(movingPolePlus c s D C - D*C) x‖ = |s| * ‖x‖.

Source route:
1. FiniteRealFockAdjoint.fock_extAction_intAction_inner (line76), with CLM apply
   readbacks, gives <Cx,y>=<x,Dy>. Real inner symmetry gives <Dx,y>=<x,Cy>.
2. Derive <D(Cx),y>=<x,D(Cy)> and <C(Dx),y>=<x,C(Dy)> by two applications.
   Derive symmetry of D+C by linearity. No assumed adjoint field or operator-star
   instance is needed.
3. movingPolePlus_eq (Stream5 line342) expresses P as
   c*c • DC + s*s • CD - c*s • (D+C). Real inner linearity gives symmetry of P,
   and subtraction gives <(P-Q)x,y>=<x,(P-Q)y>. This needs no circle constraint.
   Expose small reusable inner-law lemmas instead of a master conjunction.
4. fubini_study_chordal_metric (line567), first component, instantiated with
   fock_isDualSeedPair n i, and fock_coordinate_CLM_CAR give
   (P-Q)*(P-Q)=(s*s)•1. Extract the component; do not duplicate its ring proof.
5. With E=P-Q, derive norm-square by
   ‖Ex‖²=<Ex,Ex>=<x,E(Ex)>=<x,(s*s)•x>=(s*s)*‖x‖².
   Native real_inner_self_eq_norm_sq and real_inner_smul_right suffice.
   Nonnegativity of norms and |s|, plus |s|²=s², yield the norm equality.
   This works at s=0 and x=0, with no division, normalization of x, or nonzero input.

Optional SMALL next consequence, only if convenient: for hx: D(Cx)=x,
    ‖movingPolePlus c s D C x‖ = |c|*‖x‖.
Use symmetry/idempotence of P, symmetry of Q, and the SECOND component
Q*P*Q=(c*c)•Q to compute <x,Px>. This is projection norm of an initial-range
vector, not a new transition-probability/state definition. No optional result
is required for completion of the displacement task.

Scope: actual induced real Fock norm. The arbitrary-ring theorem alone establishes
no metric. No assertion identifying a globally defined projective Fubini–Study
metric, no new complexification/completion, and no claim of all-stream equivalence.
Pending separate authorization/serial QA for implementation.
