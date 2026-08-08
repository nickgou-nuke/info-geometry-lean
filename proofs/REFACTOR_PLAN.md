# Refactor Plan: Holographic Quasicrystal Spin Geometry

Working title:

**Holographic Quasicrystal Spin Geometry: A Clifford--Cuntz--Krieger Framework for Boundary Defects and Cartan Soldering**

This plan records how the project should be rebuilt if started from scratch. The aim is to preserve the mathematical vision while improving theorem discipline, modularity, and publishability.

## 1. Define the central object first

Introduce a single core mathematical structure, tentatively:

\[
\mathcal H=(X,\sigma,\mathcal O_M,\Gamma,\mathcal C,D,J,\epsilon,\Delta,e,\omega).
\]

A **Holographic Quasicrystal Spin Geometry** should include:

- symbolic or quasicrystal boundary system `X`
- boundary dynamics/substitution `σ`
- Cuntz--Krieger algebra `O_M`
- projective wallpaper/crystal symmetry group `Γ`
- Clifford module `C`
- Dirac/Fredholm operator `D`
- Tomita/CPT/modular data `J`, `ε`, `Δ`
- Cartan soldering form `e`
- spin connection `ω`

Every major theorem should either define this object, construct an example of it, compute an invariant of it, or state a socket/interface for an interpretation not yet proved.

## 2. Separate the proof stack into layers

Suggested Lean/Python layout:

```text
proofs/core/
proofs/clifford/
proofs/cuntz_krieger/
proofs/quasicrystal/
proofs/topology/
proofs/cartan/
proofs/physics_sockets/
proofs/examples/
proofs/capstones/
witnesses/
```

The goal is to make dependencies structural rather than merely conceptual.

## 3. Replace duplication with imports

Many current Lean files independently redefine Pauli matrices, nilpotents, squashes, tetrads, and Bogoliubov frames. From scratch, define reusable modules:

```lean
Core.Pauli
Core.CliffordAtom
Core.Nilpotent
Core.Bogoliubov
Core.Tetrad
Core.Squash
Core.Golden
Core.Tripotent
```

Capstone files should import these modules instead of duplicating definitions.

## 4. Make theorem-honest sockets explicit interfaces

Instead of informal `Prop` fields appearing in many capstones, introduce named interfaces/classes:

```lean
class BoundaryToBulkFunctor where ...
class HasCuntzKriegerBoundary where ...
class HasCartanSoldering where ...
class HasThermodynamicEinsteinSocket where ...
class HasSplitOctonionGaugeSocket where ...
```

Then the final synthesis theorem becomes a composition of interfaces, not a giant proposition bundle.

## 5. Build canonical examples early

Implement three minimal examples and keep them continuously verified:

1. **Pauli--Minkowski model**
   - determinant equals Minkowski norm
   - spin congruence determinant law

2. **Fibonacci/Penrose substitution boundary**
   - inflation/golden trace identities
   - Cuntz--Krieger/K-theory toy computations

3. **Klein-glide exceptional defect model**
   - glide inversion relation
   - nilpotent exceptional point
   - non-doubling via nonorientable identification socket

## 6. Prioritize invariants over slogans

The strongest publishable version should foreground computable invariants:

- determinants
- traces
- characteristic polynomials
- K-theory cokernels
- winding numbers
- Fredholm indices
- braid words
- Clifford signatures
- anomaly balances
- fixed-point sets

Interpretive language should appear after the invariant statements, not before them.

## 7. Avoid overclaiming in code names

Prefer theorem names like:

```lean
theorem spin_det_minkowski
theorem bogoliubov_preserves_krein
theorem cl55_split_index_cancel
theorem goldenTrace_noncrystallographic
```

Avoid theorem names that sound like final physical proofs unless they are actually proved:

```lean
-- avoid for core files
universe_is_sealed
grand_unification
physics_is_complete
```

Grand synthesis names may remain in manuscript-facing capstones, but the proof stack should be sober and theorem-honest.

## 8. Maintain a theorem map

Create and maintain `THEOREM_MAP.md` with entries like:

```text
Claim 1. Pauli determinant gives Minkowski norm.
Lean: proofs/core/Pauli.lean::spin_det_minkowski
SymPy: witnesses/pauli_minkowski.py
Status: proved

Claim 2. Bogoliubov boost preserves Krein form.
Lean: proofs/core/Bogoliubov.lean::bogoliubov_preserves_krein
SymPy: witnesses/bogoliubov_krein.py
Status: proved

Claim 3. Boundary-to-bulk holographic interpretation.
Lean: proofs/physics_sockets/BoundaryToBulk.lean
Status: socket / conjectural interface
```

This separates proved mathematics from interpretation and makes the project easier to defend.

## 9. Use Lean and Python for complementary roles

Lean should own:

- definitions
- exact identities
- algebraic proofs
- structural interfaces
- theorem dependency discipline

Python/SymPy should own:

- explicit examples
- symbolic witnesses
- spectra and matrix computations
- invariant tables
- plots or numerical experiments
- counterexample searches

SymPy scripts should do more than print slogans: they should compute concrete witnesses.

## 10. Publication framing

The project should be framed as:

> A formal library for holographic quasicrystal spin geometry, with verified algebraic kernels and explicit conjectural physical interfaces.

Not as:

> A completed proof of the universe.

The former is mathematically serious, defensible, and publishable. The latter is rhetorically powerful but academically fragile.

## 11. Immediate next implementation steps

1. Create `proofs/core/Pauli.lean` and migrate the Pauli determinant/soldering lemmas.
2. Create `proofs/core/Bogoliubov.lean` and migrate Krein preservation.
3. Create `proofs/core/CliffordAtom.lean` and migrate the `Cl(1,1)` CPT atom.
4. Create `proofs/core/Nilpotent.lean` and migrate square-zero/tripotent lemmas.
5. Create `THEOREM_MAP.md` and classify every major claim as `proved`, `witnessed`, or `socket`.
6. Keep capstone theorem files, but rewrite them to import core modules.

The end state should be a clean library plus manuscript-facing synthesis files.
