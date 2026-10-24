# Centralizing increments v6 — exact raw tensor witnesses

New sandbox revision only. No builds/tests/live edits/gate changes.
V5 kernel pass is parent-reported; this refactoring is uncompiled.

Popper identifies atomic-operand matching and actual tensor-carrier coverage as
the outstanding T16 issue. V6 names precisely the matrices already used in v4/v5:
- tensorZZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ = tilt2 tensor tilt2;
- tensorOldSwitch on that same carrier = switch2 tensor identity.

Move the existing ((0,0),(1,0)) coordinate calculation into
 tensorZZ_scaled_noncommute (lam != 0).
Expose its scalar-1 consequence in atomic form:
 tensorZZ * tensorOldSwitch != tensorOldSwitch * tensorZZ.
No unrelated witness, alternate matrices, or surrogate carrier is added.

boundaryZZ is definitionally the same reindexed matrix as before. The native
boundaryZZ_not_commute_old_switch proof now transports the named scaled tensor
inequality by the same reindexAlgEquiv, reusing the calculation rather than
repeating it. Generic centralizing criteria, the MatrixStage2 witness, and the
Hamiltonian obstruction statements are unchanged. Only the old tensor matrix
expressions are named and their existing calculation factored into a helper.

All prior versions and foreign work preserved. Strict-gate acceptance and kernel
acceptance of this revision remain for independent AA/QA, not claimed here.
Scope: native A tensor I embedding, not an impossibility of vacuum-coupled models.
