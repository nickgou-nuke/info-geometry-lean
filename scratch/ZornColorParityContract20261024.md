# Native color parity contract

The submitted coordinate carrier is not adopted. Reuse `ZornVectorMatrix R`,
`L_map`, and `R_map` from `Algebra/ZornDerivationBridge.lean`.
The existing staged `Algebra/ZornLeftGrading.lean` proves the left E11 tangent
equation and the involution L(E11-E22), with signs (a,v,-w,-b).

New delta: prove the ordered product of three signed color commutators is this
left grading. For Q=L(U_i), Q*=L(-V_i), the commutator [Q*,Q] equals
L(U_i)L(V_i)-L(V_i)L(U_i). Prove its coordinate action, then its product.
Also refute the submitted right E22 projector tangent equation over the reals
by evaluating at E22. This is an operator identity on the native carrier.

The CAR bilinear gl(3) action and central odd bracket do not by themselves
establish gl(3|1), a super-Grassmannian functor, or an adjoint interpretation.
No new result structure, duplicate carrier, assumed closure, or proof holes.
All new proofs remain candidates until independent audit and locked Lean QA.
