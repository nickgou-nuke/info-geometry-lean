# Exact trace correction for the native parabolic sandwich

Use `Quantum.RelativeEntropyFlow.quantumShearSandwich` on its existing `M2C`
carrier, with `KanDecomposition.componentN δ = [[1,δ],[0,1]]`.
The existing owner proves a maximally-mixed trace of `3/2` at `δ=1`, and
separately proves similarity trace preservation. Preserve both results.

Contract: derive the arbitrary-matrix correction
`tr(NρNᴴ)-tr(ρ) = δρ10 + star(δ)ρ01 + normSq(δ)ρ11`.
Characterize trace preservation for a fixed input by vanishing of this
correction. Derive the maximally-mixed trace `1+normSq(δ)/2` and show universal
trace preservation iff `δ=0`. This is not a claim that every individual
input loses trace at a nonzero parameter: the correction can vanish.

Source/reference searches covered the sandwich and iteration definitions,
similarity trace theorems, the KAN generator, and maintained uses (aggregates).
No replacement carrier, entropy theorem, normalization, or CPTP assertion
is introduced. The determinant-one shear's symplectic preservation is a
different property and does not establish trace preservation of this map.

Parent locked verification passed (session 85996, 8949 jobs,
`/tmp/shear-sandwich-audit.log`): five new theorems, six axiom reports including
the original counterexample, and three examples. The axiom union is exactly
`[propext, Classical.choice, Quot.sound]`. There are zero own-source warnings,
22 dependency-source warnings, and two package notices. Independent semantic
review passed, strict screening found zero traps, and scoped diffs are clean.
Independent kernel QA passed (session 61967, 8949 jobs,
`/tmp/shear-sandwich-trace-qa.log`), confirming all six reports, three examples,
the same warning scope, zero strict-screen traps, and clean scoped diffs.
