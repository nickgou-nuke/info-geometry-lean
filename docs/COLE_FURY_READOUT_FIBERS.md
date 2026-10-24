# Cole–Fury aggregate readout fibers: theorem contract

Owner: `OperatorAlgebra/ColeFuryEmbedding.lean`, with `quadrantReadout` on
`SplitOctonions.Multiplication.SplitOct` and the actual integer `Spin32Matrix`.
The owner proves noninjectivity through `kernelElement`; its multiplicativity
is restricted to `isAssociativeSubalgebra`. `ColeFuryCornerAmplification`
provides a different corner readout and its inclusion, not aggregate fibers.

Proposed replacement: equality of the two aggregate matrices iff the `a`, `b`,
`x0+x1+x2`, and `y0+y1+y2` coordinates agree. Read these at entries `(0,0)`,
`(16,16)`, `(0,16)`, `(16,0)`. Parameterize the invisible four coordinates by
`(0,0,-r-s,r,s,-t-u,t,u)`. Reconstruct any input from its canonical aggregate
representative and these four contrasts. This does not turn the readout into
an injective map or an unrestricted algebra homomorphism.

Source search for `quadrantReadout`, `embed`, `kernelElement`, and
`cornerReadout` found the owner and corner amplification as relevant consumers.
The theorem batch was subsequently compiled and independently accepted as recorded below.

Parent owner build session 50772 passed (3,097 jobs, exit 0), with zero own
warnings and two package warnings; `/tmp/cole-fury-fibers.log`. Semantic
review by Poincare passed. The companion audit contains two examples, a
noncommuting horizon witness and seven axiom requests. Independent QA session
95012 passed (3,098 jobs, exit 0), with all seven reports limited to standard
axioms, two examples passed, zero source warnings and two package notices.
Strict screening found zero traps. Evidence: `/tmp/cole-fury-fibers-qa.log`.
Final disposition: accepted with the stated additive/readout scope.
