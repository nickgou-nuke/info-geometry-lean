# Peirce channel defects and adjoint-pair nonvanishing

## Intake, branch, and scope

This follow-up starts from `main` at
`a392af178af1fe2bcba2ba39eb405700c6ee103c`. It is independent of PR #323's
tripotent flow extension. The uploaded source is preserved verbatim in
[`sources/peirce_defect_intake_20261112.txt`](sources/peirce_defect_intake_20261112.txt).
Its original name was `Pasted text(20261112-095814).txt`; its 27,678 bytes have
SHA256 `2313829fb9e179b94be11d62e58d0e7ee7f05e14dd72d5dfabf872d81547228d`.
The preserved text is research input, not a statement of accepted results.

The proposed additions concern arbitrary associative rings, proper star-ring
realizations, native C-star norm assumptions, and counterexamples in the full
real four-by-four matrix algebra. No characteristic restriction is imposed on
the ring-level channel identities. No continuum field theory, spectral gap,
bundle classification, or sporadic-group construction is inferred.

## Existing owners and the missing implications

| Existing owner | Reused content | New obligation |
| --- | --- | --- |
| `PeirceSpine.Basic` | Ordered corners, generators, commutator, corner normal form | Keep the ambient carrier noncommutative. |
| `PeirceSpine.Homogenized` | Four double-commutator channels, four Fourier channels, generator evaluations, two-sided expansion | Identify the existing Peirce maps with the more general endomorphism owner. |
| `SquareZeroPairSpectral.FourierCharacterDefect` | All four general defects, the exact `V^2` centralizer criterion for two channels | Transport these established theorems through the channel identifications, rather than re-proving the square-zero algebra. |
| `PeirceSpine.Bridge` | Corner and Laplacian identifications | Complete the channel dictionary used by the transported theorems. |
| `PeirceSpine.StarGrading` | `star_conePlus`, self-adjointness of the paired metric | Prove precisely when the paired metric vanishes. |
| `Canonical.TripotentMatrixExample` | Dense orthonormal frame, all sixteen matrix units, multiplication and star laws | Exhibit nonzero independent cones with zero overlap and a nonzero paired metric with a kernel. |
| `Core.IdempotentDefectIteration` and `PeirceSpine.DefectTower` | Orthogonal splitting at every finite iterate, ring-homomorphism transport | Reuse; do not introduce another defect-tower owner. |
| `PeirceSpine.Unipotent` | Ordered conjugations, idempotent chart formula, finite towers | Correct the intake's reversed conjugation in this contract. |
| `PeirceSpine.CyclotomicBridge` | Off-shell cyclotomic residuals, braiding, reflection squares | Distinguish the unit locus from the larger idempotent locus. |
| `PeirceSpine.TetraktysKleinActionBridge` | Sandwich maps identified with actual Klein automorphisms on `V = 1` | Reuse; do not reinterpret general polynomial channels as automorphisms. |

The search included declarations and consumers under both `lean/` and `src/`;
the additions target the canonical `lean/` owners. Historical aggregate files
and prose supplied navigation, not verification evidence.

## Exact channel contract

Write `V = genV P A C`, `Phi = genPhi P A C`, `J = genJ P A C`, and
`Sigma = genSig P A C`, with `P * P = P`. Let `H` denote the existing
`hProj` channels and `F` the corresponding existing `fourier` channels.
For arbitrary `X : B`, the proved identities are:

\[
\begin{aligned}
H_V(X)-F_V(X)&=3V[V,X]+[V,X]V,\\
H_\Phi(X)-F_\Phi(X)&=-[V^2,X],\\
H_J(X)-F_J(X)&=-[V^2,X],\\
H_\Sigma(X)-F_\Sigma(X)&=-[V,[V,X]].
\end{aligned}
\]

Every equality retains multiplication order. `Commute V X` is a sufficient
condition for all four differences to vanish. For the `Phi` and `J` channels,
the exact condition is `Commute X (V * V)`, proved as an equivalence. No
necessity of `Commute V X` is asserted for the mass or spin channel: a
commutator can be annihilated by other factors. The existing channels are not
redefined, and equality is not assumed on the entire ring.

The intake's unequal sandwich weighting has value `5 V^3` on `V` and
`V^2 * Phi` on `Phi`. The existing correctly weighted Fourier sum is

\[
F_V(X)=2\bigl(V^2X+V(\Phi X\Phi-JXJ)+\Sigma X\Sigma\bigr).
\]

On the centralizer this agrees with `H_V`; its value on `V` is `8 V^3`.
The coefficient two must multiply the entire sum.

## Adjoint-pair contract

In a ring with star, assume explicitly that
`star x * x = 0` implies `x = 0`. For `N * N = 0`, the theorem establishes

\[
NN^*+N^*N=0\quad\Longleftrightarrow\quad N=0.
\]

This is a zero criterion. It supplies neither an order nor a positive lower
bound. The native C-star norm identity discharges the explicit properness
hypothesis in the normed specialization. For a self-adjoint idempotent `P`,
`star_conePlus` identifies `coneMinus P (star A)` with
`star (conePlus P A)`, so the criterion applies to `genV P A (star A)`.
The nonvanishing hypothesis must concern the selected upper corner, not just
the full commutator `[P,A]`.

The ordered specialization separately proves nonnegativity using native
`StarOrderedRing`. It needs `star P = P` but does not need idempotence of `P`.

## Dependency structure

```mermaid
flowchart TD
  C["Peirce corner rules"] --> B["Channel identifications"]
  L["Existing Laplacian dictionary"] --> B
  B --> D["Transported Fourier defects"]
  F["Existing square-zero Fourier theorems"] --> D
  D --> W["Dense matrix discrepancy"]
  M["Dense frame multiplication"] --> W
```

The separate star chain is square-zero multiplication plus explicit star
properness, followed by the Gram-sum zero criterion and then its Peirce
specialization. Native C-star properness supplies the normed corollaries.
Star-order positivity is an independent branch. None of these edges points to
a spectral-gap or bundle-classification theorem.

## Corrections and unproved interpretations

| Intake claim | Correct scope or obstruction |
| --- | --- |
| `(1-N) P (1+N) = P-N` for the upper corner | It equals `P+N`; the existing `conjPlus = (1+N) P (1-N)` equals `P-N`. Order determines the sign. |
| `E12` and `E31` have both products zero | Their reverse product is `E32`. A valid example uses disjoint arrows in four dimensions. |
| Adjoint pairing and nonzero corner imply a spectral gap | They imply nonzero paired metric under the stated hypotheses. A nonzero positive matrix can have a kernel; coercivity requires additional assumptions. This does not rule out a gap above a specified ground-state subspace. |
| `[P,A] != 0` implies the selected paired metric is nonzero | A purely lower-corner `A` has nonzero commutator but zero upper corner. |
| `delta(V)=0` is the cyclotomic unit-shell condition | It only says `V^2=V`. The residual `omega^2-omegaBar=1-V` vanishes exactly at `V=1`. Equal reflection squares alone impose the weaker condition. |
| Algebraicity of `V` makes the defect iterates vanish | False: `delta(2)=2` in characteristic zero. Algebraicity gives relations, not eventual vanishing. |
| A global idempotent is a global gauge fixing | A global projection can represent a nontrivial vector bundle. It does not provide a section of the gauge-orbit projection. |
| Four integral generators form a free/Azumaya module in every realization | A generating bound is not freeness, linear independence, or the Azumaya property. The proposed `Phi,J,Sigma` basis may require inverses absent over the integers. |
| Split signature forbids every `S4` action or every Golay/Leech realization | Preservation of squares obstructs a particular permutation of named generators when `1 != -1`; it does not exclude every action, representation, tensor construction, or extension. |

For the topology distinction, Swan's original
[Vector Bundles and Projective Modules](https://wiki.math.ntnu.no/_media/ma8107/2014h/swan_-_vector_bundles_and_projective_modules.pdf)
constructs vector bundles as summands of trivial bundles and relates their
sections to projective modules. Singer's
[Some Remarks on the Gribov Ambiguity](https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-60/issue-1/Some-remarks-on-the-Gribov-ambiguity/cmp/1103904019.pdf)
concerns the obstruction to a global continuous gauge choice. These are
different constructions. No bundle-patching theorem is added by this change.

## Verification record

Independent semantic and infrastructure source review passed for all three
modules, this contract, and the scoped workflow. The staged proof gate passed.
The two proof-only name qualifications in the matrix module received a
separate independent review; no theorem statement or hypothesis changed.

**Scoped kernel verification passed** in
[run 43200522642](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43200522642).
It checked source head `e06b6e9d753aebc730861850524339bb4aeeb199` through PR merge
revision `42ddb1433f8d953fa9ea40c060600700a50f65f2`, using
`leanprover/lean4:v4.34.1` and the unchanged Mathlib pin
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

- All 38 modules in the selected project import closure compiled successfully.
- All 55 declarations owned by the three added modules, including generated
  auxiliaries, passed the native declaration audit. Dependencies were confined
  to `propext`, `Classical.choice`, and `Quot.sound`; unsafe and partial
  declarations are rejected by the checker.
- The three new modules emitted no warnings or errors. Warnings in imported,
  unchanged modules remain visible in the artifact.
- The downloaded artifact's digest was verified, and the recorded source
  hashes of all three new owners matched the reviewed local files.

The
[verification artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43200522642/artifacts/13934679253)
contains the source snapshot, per-module logs, declaration audit, and status
JSON. Its ZIP SHA256 is
`579a06caab430a4304e5fa1f858e8e2d01a3aad99b32458a7eee487166acf43f`.

| New owner | Verified source SHA256 |
| --- | --- |
| `PeirceSpine.HomogenizedFourierDefect` | `a116f561304336c31b0aefa8493cf77c77eca996b7830f941e252e63f4938518` |
| `PeirceSpine.StarMetricNondegeneracy` | `f3e669a11893211fb42a62560630e3f34444edc170d650dc7364dd6b54dc6893` |
| `Canonical.PeirceChannelCounterexamples` | `874df68e08e4aeb705194a6fa9f0a4dbc77c2c1a40d27d5a9556811b65e3a1e5` |

The successful CI command was:

```bash
python3 project/tools/quality/check_peirce_channel_defects.py \
  --mathlib-root pinned-mathlib --output verification
```

The first scoped run compiled 37 of 38 modules and failed at two ambiguous
`comm` simplifier arguments in the matrix examples. Fully qualifying those
arguments fixed the failure; the successful run above checked the repair and
then performed the declaration audit.

### Outstanding repository gates

This is selected-source verification, not a successful root Lake build or a
completed local pre-push gate for the Lean change.

- The initial local locked build exited with code 2 because another task held
  the shared build lock. A later invocation of the actual pre-push hook for
  the repair range also waited for that lock. Only that waiting invocation
  was cancelled (exit 130); no compiler was started by it, and no other
  compiler, lock, or cache was removed.
- The
  [root quality workflow](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43200522378)
  failed before Lean compilation because the checkout lacked
  `external_refs/homotopy-hypothesis-lean4`. Its post-build quality step was
  skipped.
- The
  [style workflow](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43200522673)
  failed on the existing case collision between
  `Physics/PellisFineStructure.lean` and `Physics/PellisfineStructure.lean`.

Those package paths and files are unchanged by this PR. The final reporting
commit changes only this contract; the verified Lean owners, dependency pins,
checker, and workflow remain byte-identical to the successful run. The PR is
available for review; this record does not certify repository-wide acceptance
or authorize a merge.
