# Exact two-probe fibers and three-probe reconstruction

The actual negative owner is
`Synthesis/SedenionSocleDirectSumSeparationBridge.two_probes_do_not_separate`.
Its carrier is the full real 3-by-3 matrix space and its probes are
`(0,1,1)`, `(1,1,0)`, and `(1,0,1)`. The existing nonzero witness has every
row equal to `(-1,1,-1)`.

`ThreeProbeReconstruction.lean` classifies the entire two-probe kernel:
every invisible row is uniquely `c i * (-1,1,-1)`. Applying this theorem to
`X-Y` gives the exact fibers of the two-probe observation map.
The three observed vectors `u,v,w` reconstruct each row as
`((v+w-u)/2, (u+v-w)/2, (u+w-v)/2)`. Readback proves injectivity for these
specific three probes on the unrestricted matrix carrier.

This does not assert that the probes reconstruct arbitrary sedenions or
derivations. The separate owner for coordinate probes and restricted
`so21LinearComb` families is not replaced. Bounded maintained source and
dependent searches found those results and the negative witness, but no
equivalent exact kernel/fiber criterion in the inspected results.

The companion audit reuses the owner's nonseparating matrix and requests
seven axiom reports. Semantic AA passed the kernel classification,
reconstruction, and fiber corollary. Strict screening passed.
The first parent audit (session 46551) failed
on a missing `noncomputable` marker for real division and unreduced tuple
projections in the injectivity proof. Both issues were repaired; no earlier
kernel or fiber lemma produced a compiler error. The corrected parent audit
passed: session 76349, `/tmp/three-probe-audit.log`, 3,136 jobs, exit 0.
All three examples and seven standard-axiom reports passed. Independent
kernel QA accepted this scope: session 33650, `/tmp/three-probe-qa.log`,
3,136 jobs, exit 0, seven standard-axiom reports and three examples.
There were zero own-source warnings, 29 dependency warnings and two package
notices; static screening found zero traps and scoped diff checks passed.
