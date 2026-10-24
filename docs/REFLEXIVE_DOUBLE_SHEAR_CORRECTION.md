# Double-shear square correction

The incoming Stream 4 text claims, for `Lambda=(1+d)(1-B)`,
`Lambda*Lambda = P0+d-B-B*d`. With the given conventions `Pplus=d*B` and
`Pminus=B*d`, this formula is false. The existing integral pair `matD,matB`
gives the square `[[-1,1],[-1,0]]`, whereas the claimed expression is
`[[0,1],[-1,-1]]`.

`Canonical/ReflexiveDoubleShear.lean` reuses the existing flow owner, Weyl
factorization, and complement annihilation. It proves over any ring:

`doubleShear d B * doubleShear d B = complement d B - d*B + d - B`.

It also proves that the pasted square formula holds iff `d*B=B*d`, under
the same reflexive square-zero hypotheses. The audit retains the concrete
negative witness on the owner's native integer matrices.

Semantic AA passed. Parent mixed build session 64079 compiled the shear
owner and audit successfully (`/tmp/jones-shear-build.log`); the overall
command failed on the separate Jones generator bridge. The two generic
theorems use only `propext`; the concrete refutation uses the three standard
axioms. Independent kernel QA session 42099 passed (8,954 jobs, exit 0),
with three axiom reports and two examples, zero own warnings, twelve dependency
warnings and two package warnings. The audit directly imports the existing
matrix witness owner and supplies its noncommutativity example; strict
screening now reports zero traps. Evidence: `/tmp/reflexive-double-shear-final-qa.log`.
Final disposition: accepted with limited algebraic scope. No full Stream 4,
exact finite-order, modular-group presentation, or Nambu theorem is certified
by this small correction.

The later rotor intake has a separate proof-scoping issue: a formula proved
at fixed `c,s` cannot be rewritten at `0,1`; a parameterized helper lemma is
needed. Its algebraic identities do not themselves formalize De Bruijn syntax,
continuity, or differentiation. No new parallel seed structure was added.

The current `DeBruijnRotorAlternationCycle.lean` owner has since been inspected:
its `movingPolePlus_eq` helper is parameterized and repairs that pasted scoping
error. This observation is not an independent certification of the full rotor stream.
