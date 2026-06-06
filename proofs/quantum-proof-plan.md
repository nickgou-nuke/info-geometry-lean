# Quantum Proof Plan: Fibonacci Hexagon From U_q(sl(2))

This is the corrected repo-native digest of the fuller archive at
`/media/goutev/SP DS72/auto/proofs`.

Do not import the archive Lean files directly. Several are useful as design
notes, but the current repository owner files are stronger, namespaced, and
Lean-checked.

## Owner Files

| Layer | Owner file | Current role |
|---|---|---|
| Fibonacci fusion data | `lean/InfoGeometry/Fibonacci/FibAnyonThm1.lean` | Golden ratio identities and finite fusion dimension readout |
| Explicit F matrix | `lean/InfoGeometry/Fibonacci/FibAnyonThm2.lean` | `F * F = 1`, determinant `-1` |
| Explicit R matrix | `lean/InfoGeometry/Fibonacci/FibAnyonThm3.lean` | Primitive fifth-root convention and finite R-matrix facts |
| Matrix Yang-Baxter | `lean/InfoGeometry/Canonical/YangBaxterProof.lean` | Closed canonical braid relation `R * B * R = B * R * B` |
| Categorical matrix surface | `lean/InfoGeometry/Categorical/FibonacciBraiding.lean` | Theorem-only F/R/B surface over canonical finite matrices |
| Braided tower/cone surface | `lean/InfoGeometry/Categorical/FibonacciBraidedTowerCone.lean` | Mathlib `BraidedCategory` coherence plus Zorn, tower colimit, tri-facet, self-dual cone readout |

## Chapter Plan

```text
Ch1: U_q(sl(2)) as Hopf algebra
  -> Ch2: quasitriangular universal R-matrix
  -> Ch3: Yang-Baxter equation for universal R
  -> Ch4: Rep(U_q(sl(2))) is braided
  -> Ch5: root-of-unity truncation
  -> Ch6: semisimple quotient is Fibonacci MTC
  -> Ch7: explicit F/R matrices
  -> Ch8: hexagon/Yang-Baxter coherence
```

## Current Honest Status

| Chapter | Status in this repo |
|---|---|
| Ch1 | Not repo-native yet. The archive mentions ATLAS-style quantum group files, but this repo should not assume those APIs without a checked import path. |
| Ch2 | Not repo-native yet. Universal R-matrix/quasitriangularity must be built using actual mathlib/repo structures, not pseudo-fields. |
| Ch3 | Categorical Yang-Baxter is available through mathlib `BraidedCategory` coherence; universal-R Yang-Baxter remains future work. |
| Ch4 | General `BraidedCategory` coherence is used directly. A concrete `Rep(U_q(sl(2)))` braided instance is not yet formalized here. |
| Ch5 | Open debt: root-of-unity truncation and negligible/zero quantum-dimension quotient. |
| Ch6 | Open debt: semisimple quotient with exactly `1` and `tau`, fusion `tau tensor tau = 1 plus tau`. |
| Ch7 | Checked finite matrix facts exist for F/R and canonical Yang-Baxter. |
| Ch8 | Mathlib braided coherence is connected in `FibonacciBraidedTowerCone`; full Fibonacci MTC hexagon awaits Ch5-Ch6. |

## Archive Digestion

| Archive file | Decision |
|---|---|
| `FibAnyonThm1/2/3.lean` | Already represented by namespaced repo files. |
| `FibAnyonThm4.lean` | Rejected as direct import; it does not compile. Repo uses `Canonical/YangBaxterProof.lean`. |
| `FibAnyonThm5.lean` | Already represented after replacing hook-blocking `structure BraidGroup` with a theorem-safe matrix-family abbreviation. |
| `HexagonCocycle.lean` | Already represented after replacing hook-blocking `structure LegendreDuality` with a non-carrier abbreviation. |
| `fib_category.lean` | Rejected as direct import; F-matrix proofs fail under the repo toolchain. |
| `fibanyon_thm1_fusion.lean` | Compiles but is a tiny duplicate of `FibAnyonThm1`. |
| `fibanyon_thm2_fmatrix.lean` | Rejected as direct import; proof fails under the repo toolchain. |
| `fibanyon_thm3_rmatrix.lean` | Rejected as direct import; missing `pi` namespace and unfinished unitary proof. |
| `fibanyon_thm4_yangbaxter.lean` | Useful as a pointer to mathlib `BraidedCategory.hexagon_forward/reverse`; subsumed by `FibonacciBraidedTowerCone`. |
| `fibanyon_thm5_braidgroup.lean` | Compiles but only contains a toy `BraidGroup` alias and a `True` theorem. |
| `FormalTheoryQuantum.lean` | Useful as a roadmap for Ch1-Ch6, not as code. It contains pseudo tensor notation, unresolved `HopfAlgebra` usage, and `sorry`. |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.lake` | Archive-local build material; do not import. |

## Next Formalization Targets

1. Normalize the two root conventions:
   `exp(pi i / 5)` in the canonical Yang-Baxter owner and
   `exp(2 pi i / 5)` in the fifth-root R-matrix file.
2. Build the Fibonacci fusion semiring/Grothendieck readout using
   `Algebra/Grothendieck.lean`, not a new carrier wrapper.
3. Define the root-of-unity quantum dimension target and isolate the precise
   truncation theorem needed for Ch5.
4. State the semisimple quotient/MTC theorem for Ch6 as an explicit owner
   interface with hypotheses, then burn the hypotheses down constructively.
5. Only after Ch5-Ch6 are real, instantiate any concrete Fibonacci
   `BraidedCategory`; until then, use mathlib braided coherence as the
   categorical owner and finite matrices as checked instances.
