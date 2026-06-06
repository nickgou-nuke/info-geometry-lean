# Cl(5,5) ambient osp(1|2) hard targets

Status: honest owner-side planning note

This note translates the current SymPy/Clifford discussion into exact Lean-sized
obligations for this repository. It is intentionally narrower than the physics
story: only algebraic claims that can become kernel-checked Lean theorems are
listed here.

## 0. Current repo-owned facts already available

The current repo already closes the following finite algebraic facts.

1. `InfoGeometry.Clifford.ConformalLift55`
   - `Cl55 := SplitBottClifford 5`
   - `conformalNullPair_exists : Nonempty ConformalNullPair`
   - with explicit `u v : Cl55` such that
     - `u ^ 2 = 0`
     - `v ^ 2 = 0`
     - `u * v + v * u = 1`

2. `InfoGeometry.Clifford.ConformalLieAlgebra55`
   - the commutator operator `adD`
   - grade eigenspaces `gradeSpace`
   - even-grade carrier `gradeSpaceEven`
   - the involution `thetaOpEven`
   - a five-graded inversion interface on the even Clifford subalgebra

3. `InfoGeometry.Algebra.OSp12`
   - an authentic 5-dimensional osp(1|2) owner surface with basis
     `H, Ep, Em, G1, G2`
   - structure constants matching the verified 2|1 matrix model

These facts do NOT yet supply a theorem that `Cl55` contains a concrete
5-dimensional osp(1|2) sub-superalgebra.

## 1. Honesty boundary

The claim we may safely target is:

- there exist five explicit elements of the ambient `Cl55` carrier whose
  induced superbracket closes with the authentic osp(1|2) table.

The claims we should NOT make until separately proved are:

- this realization is mathematically necessary for osp(1|2);
- the full physics/anomaly interpretation;
- conformal compactification or dilaton statements beyond the exact algebra used
  in the proof.

## 2. The missing object: explicit ambient generators

The next owner target is not a prose explanation but five explicit terms

- `Hc : Cl55`
- `Epc : Cl55`
- `Emc : Cl55`
- `G1c : Cl55`
- `G2c : Cl55`

plus an explicit parity convention and bracket operation.

Without these exact terms there is no Lean theorem to prove.

## 3. Required bracket choice

If the carrier remains the associative Clifford algebra itself, the induced
superbracket must be declared explicitly. The minimal honest choice is:

- even-even: commutator `x * y - y * x`
- even-odd: commutator `x * y - y * x`
- odd-odd: anticommutator `x * y + y * x`

This requires explicit parity theorems saying which generators are even and
which are odd in the repo's `CliffordAlgebra.evenOdd` grading.

## 4. Exact theorem obligations

A real ambient-Cl(5,5) osp(1|2) file should prove the following, in order.

### A. Parity placement

1. `Hc` is even.
2. `Epc` is even.
3. `Emc` is even.
4. `G1c` is odd.
5. `G2c` is odd.

These should be theorems about membership in the native Clifford grading, not
comments.

### B. Closure and table

Using the chosen superbracket:

1. `[Hc, Epc] = 2 • Epc`
2. `[Hc, Emc] = -2 • Emc`
3. `[Epc, Emc] = Hc`
4. `[Hc, G1c] = G1c`
5. `[Hc, G2c] = -G2c`
6. `[Epc, G2c] = G1c`
7. `[Emc, G1c] = G2c`
8. `[G1c, G1c] = 2 • Epc`
9. `[G2c, G2c] = -2 • Emc`
10. `[G1c, G2c] = -Hc`
11. `[G2c, G1c] = -Hc`

These are the exact SymPy-frozen relations for the authentic 5-dimensional
osp(1|2) convention currently used by `InfoGeometry.Algebra.OSp12`.

### C. Linear independence / non-collapse

1. `Hc, Epc, Emc, G1c, G2c` are linearly independent over `ℝ`.
2. Therefore their span is 5-dimensional.
3. In particular `Epc ≠ 0` and `Emc ≠ 0`, ruling out collapse to the old
   3-generator truncation.

### D. Sub-superalgebra closure

Let `S := span ℝ {Hc, Epc, Emc, G1c, G2c}`.

Prove:
- `S` is closed under the chosen superbracket.
- the induced even part of `S` is exactly `span {Hc, Epc, Emc}`.
- the induced odd part of `S` is exactly `span {G1c, G2c}`.

### E. Identification with the repo's authentic owner

Final target:
- construct a Lie-superalgebra isomorphism between the abstract owner in
  `InfoGeometry.Algebra.OSp12` and the ambient span `S`.

This is the theorem that turns the ambient Clifford story into a kernel-checked
mathematical fact.

## 5. What should NOT be first-class theorem targets yet

The following should remain out of scope until the algebraic embedding above is
fully closed.

1. anomaly-to-coordinate transmutation
2. dilaton interpretation
3. boundary regularization at infinity
4. compactification or bulk-boundary reconstruction claims
5. any statement that the ambient realization is "necessary"

If needed later, these must be decomposed into separate exact theorems over the
already-closed algebraic carrier.

## 6. Recommended file split

### File 1: ambient carrier facts

Keep using the current files for finite ambient facts:
- `InfoGeometry.Clifford.ConformalLift55`
- `InfoGeometry.Clifford.ConformalLieAlgebra55`

These are the source of the existing `Cl55`, null-pair, and grading surfaces.

### File 2: new ambient osp(1|2) owner target

Add a new file such as:
- `lean/InfoGeometry/Clifford/Cl55OSp12Ambient.lean`

This file should contain only:
- explicit generator definitions
- parity theorems
- bracket-table theorems
- linear-independence theorem
- closure of the 5-dimensional span

It should NOT contain physics prose beyond a short docstring honesty boundary.

### File 3: identification bridge

Add a second file such as:
- `lean/InfoGeometry/Clifford/Cl55OSp12Bridge.lean`

This file should prove the explicit identification with
`InfoGeometry.Algebra.OSp12`.

That keeps the development layered:
- ambient carrier
- explicit 5-generator closure
- abstract-owner identification

## 7. Recommended proof posture

The safe workflow for the new file is:

1. choose the exact five Clifford terms externally (SymPy or independent math);
2. freeze their exact signs and normalizations;
3. translate those exact terms into Lean definitions;
4. prove the bracket table directly in Lean;
5. only then state any geometric interpretation theorem.

If a candidate generator set does not produce nonzero `Epc` and `Emc` through
`[G1c, G1c]` and `[G2c, G2c]`, it is not an authentic osp(1|2) realization and
must not be promoted as such.

## 8. Immediate next decision

Before editing Lean, one exact choice must be supplied:

- either an explicit five-generator candidate inside `Cl55`, or
- a decision to realize osp(1|2) in a matrix/spinor algebra built from `Cl55`
  rather than in `Cl55` itself.

This distinction matters. A direct realization inside the associative Clifford
carrier is a stronger claim than a realization in an auxiliary endomorphism or
supermatrix algebra built from the Clifford carrier.
