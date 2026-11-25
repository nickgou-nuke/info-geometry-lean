Intake provenance: user message on 2026-11-25 in this task.
This file preserves the mathematical claim excerpts and the supplied conventions;
it is an intake record, not a claim that the supplied Lean compiled.

The user described the Courant–Drinfeld–Dirac capstone as "already the
foundational algebra of twistor plabic graphs and CPT-compliant Penrose spin
networks" and the two descriptions as "literally the same theorem viewed from
opposite ends".

Supplied definitions:
  B((u1,xi1),(u2,xi2)) = dot(u1,xi2) + dot(u2,xi1)
  L_plus(P)  = {(P xi, xi)}
  L_minus(P) = {(-P xi, xi)}
  J(u,xi) = (-u,xi)
  eps2 = [[0,1],[-1,0]]
  spinorBracket(a,b) = a0*b1 - a1*b0

Supplied claims:
  P^T = -P implies B(L_plus,L_plus) = B(L_minus,L_minus) = 0.
  B((P a,a),(-P b,b)) = 2 dot(P a,b).
  J^2 = identity and B(Jv,Jw) = -B(v,w).
  J exchanges L_plus and L_minus.
  Graph-fixed states are precisely (0,xi) with P xi = 0.
  Such states were interpreted as Casimir / Souriau entropy invariants.
  The supplied epsilon half-pairing was claimed to equal +spinorBracket.
  Delta13*Delta24 = Delta12*Delta34 + Delta14*Delta23.
  Addition and Q P Q^T preserve skewness and graph isotropy.
  Shared kernel directions survive addition.
  These matrix operations were described as network gluing/coarse-graining.

Supplied implementation pitfalls retained for traceability:
  hAdj used rw [dotProduct_comm, Matrix.dotProduct_mulVec,
               Matrix.vecMul_transpose].
  The epsilon identity used the positive sign and concluded by simp; ring.
  The rectangular congruence proof used unqualified neg_mul and mul_neg.
  The file was described as "Complete Native Mathlib4 Formalization" and
  "0 sorry" without a compiler receipt supplied in this message.

Correction: the half-pairing is -spinorBracket for the displayed epsilon.
Witness a=(1,0), b=(0,1): half-pairing=-1 and spinorBracket=+1.
The quadratic Plucker relation survives this correction.

The exact accepted scope and unproved interpretations are recorded in
THEOREM_CONTRACT.md. Verification results are recorded separately.
