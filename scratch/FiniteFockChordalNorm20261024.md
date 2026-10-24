# Finite real Fock chordal norm consumer

Contract recorded before implementation. Candidate: FiniteFockChordalNorm20261024.lean.
Reuse scout contract FiniteFockChordalMetric20261024.md (Kepler); do not modify it.

Import native Clifford.FiniteFockCLMReflexivePair, whose dependency chain supplies
FiniteRealFockAdjoint, the real metric/CLMs, and Stream5 chordal algebra.
Carrier remains Clifford.SpinorSpace (ClNNNeutralChevalleyBridge.Vector n).
Activate only existing fockNormedAddCommGroup/fockInnerProductSpace locally.
D=fockIntActionCLM n i and C=fockExtActionCLM n i, i:Fin n.

Expose reverse inner adjointness of D,C from fock_extAction_intAction_inner plus
real_inner_comm; expose symmetry of DC, CD and D+C; use the actual
movingPolePlus_eq polynomial to obtain symmetry of the moving pole and its
displacement E=movingPolePlus c s D C-D*C. No symmetry conclusion is assumed.
These inner statements do not need c²+s²=1.

For c,s:real with c*c+s*s=1, use the first component of Stream5
movingPolePlus_chordal_square_and_compression (fock_isDualSeedPair n i) and native
fock_coordinate_CLM_CAR to obtain E*E=(s*s)•1. Do not reprove that ring identity.
Apply to actual x and use symmetry:
norm(Ex)^2 = inner x (E(Ex)) = (s*s)*norm(x)^2.
Nonnegativity and sq_abs then prove exactly norm(Ex)=abs(s)*norm(x).
No nonzero-vector premise, division, CompleteSpace, operator-star instance,
assumed bound/adjoint field, scalar proxy, or different Fock carrier.

This is an actual induced Fock norm equality, not a global projective
Fubini–Study metric identification. Optional initial-range/opnorm results are
excluded to keep the consumer narrow. No builds/tests/live-owner edits.
Independent AA and serialized QA required; source alone is not kernel evidence.
