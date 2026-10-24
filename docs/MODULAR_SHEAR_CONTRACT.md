# Parabolic shears and the integral modular group

## Source and dependency boundary

Intake: `Pasted text(20261024-084047).txt`.
Base: PR #205, `ea08baa1649c9eeaf45638d6e7edef2f971ad1be`.
This is an additive follow-up. Existing Moore-Penrose, support, Weyl-unit,
weighted-trace, and integral matrix definitions are reused unchanged.
The asserted unpublished Grassmannian module is not a dependency.

## Exact ring contract

For an arbitrary associative unital ring A, assume
`d*d=0`, `b*b=0`, `d*b*d=d`, and `b*d*b=b`.
No star or scalar algebra is required in the universal layer.
Set U=(1+d)(1-b), W=U(1+d), Delta=db+bd, and H=1-Delta.

The new ring results establish actual shear units, natural shear powers,
both inverse equations for U, the inverse sum U+U^{-1}=2H+Delta,
the exact ambient polynomial defect U^2-U+1=H, the braid relation,
and W^2=U^3=H-Delta. Thus W^4=1 and U^6=1.
These are annihilating-power equations; exact orders need further hypotheses.

The native `PresentedGroup` on two generators with relations s^4=1 and
s^2=u^3 maps by a native monoid homomorphism into A^units. Both defining
relations and both generator images are proved. The common square/cube
commutes with the two generator images. It is central in their generated
subgroup, not necessarily in the full ring.

The MP adapter obtains dual square-zero from the existing MP owner and
identifies the new triple unit with PR #205's `weylUnit`. No duplicate
inverse predicate or harmonic-support carrier is introduced.

## Integral specialization

Use native `Matrix.SpecialLinearGroup (Fin 2) Int`, with S equal to the
inverse of Mathlib's standard S and T equal to Mathlib's standard T.
Then L=S*T*S^{-1}, U=S*T^{-1}, T*L=U and T*L*T=S.
The existing `SpecialLinearGroup.SL2Z_generators` theorem is transported to
prove closure{S,U}=top. The presentation map onto SL(2,Int) is surjective.
No proof of injectivity of that presentation map is claimed here.
Exact least-positive-power witnesses give orders 4, 6 and 3 in this model.
Actual matrix traces and the prior weighted-trace boundary identities are
connected on the same 2-by-2 integer carrier.

## Explicit source corrections

1. With the supplied S=[[0,1],[-1,0]] and T=[[1,1],[0,1]], the supported
   omega is S*T, not S*T^{-1}. The latter equals U.
2. U^2=[[-1,1],[-1,0]]. The uploaded intermediate `h_L6_sq` uses the wrong
   diagonal support; the intermediate equality cannot be preserved.
3. The opposite products do not commute. (1-b)(1+d)=1-bd+d-b, whereas
   (1+d)(1-b)=1-db+d-b. Several prose support labels are interchanged.
4. A universal sixth-power law does not imply primitive order six. The zero
   pair yields the identity. Small-characteristic collapses are also allowed.
5. H-Delta is central relative to the generated shears, not an arbitrary
   ambient matrix algebra. A proper-support 3-by-3 counterexample is included.
6. The full ambient polynomial is U^2-U+1=H. On a proper harmonic complement
   U is the identity, so it is not an ambient root of Phi_6.
7. SL(2,Int) generation is a separate theorem, not a consequence of observing
   only the two power relations. The nilpotent matrices themselves are not
   elements of SL(2,Int); their shears are.
8. The finite-order integral double shear is not called loxodromic. No
   groupoid, analytic KMS dynamics, positivity or normalized state is built.

## Verification

Acceptance is determined by the dedicated `Modular shears (scoped)` run,
not by this document or claims of compilation in the intake. The workflow
uses PR #205's exact-pin source-closure runner and public Lean.collectAxioms
checker without changing the parent. Every new-module declaration, including
generated declarations, is audited against the foundational-axiom allowlist.
No unsafe/partial declaration or audit exemption is accepted.

This is not a full root-Lake or all-green repository check. The runtime here
has no Lean executable; remote compilation results must be reported explicitly.

Production import: `InfoGeometry.Canonical.PeirceModularBridge`.
Complete target: `InfoGeometry.Canonical.IntegralModularShears`.

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.IntegralModularShears
```
