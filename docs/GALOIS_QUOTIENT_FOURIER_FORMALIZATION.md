# Galois actions, quotient variance, and dihedral Fourier blocks

## Intake and implementation contract

This extends the language-symmetry formalization at commit
`f977e663b00195e78aa2c9c6237bb4c458c22c24`. The source is the user attachment
`Pasted text(20261107-190730).txt`, received on 2026-11-07. Its SHA-256 is
`0ed44c8288e64cab1d103f19d97a2b4b5a0b884de935858fe851c296fe33b2d3`.

The contract has three branches: finite subgroup compression, cyclotomic Galois
actions, and dihedral representations. The synthesis proves compatibility
between them. A sequence of prose topics is not treated as a linear order on
mathematical objects.

Lean kernel validation, semantic review, and acceptance are separate checks.
The final validation record below describes the checked scope.

The four new mathematical modules contain 94 theorems and 22 definitions,
for 116 public declarations. The companion audit also covers all six public
declarations in the reused `FiniteMatrixNoncommutativeWitness` owner. That
existing file receives a proof-style lint repair and the standard source header;
its theorem statements remain unchanged.

## Subgroup averaging and quotient variance

`LanguageSymmetryQuotient.lean` uses Mathlib's `Representation.averageMap`.
For a representation restricted to a finite subgroup H, this is the normalized
sum of the subgroup actions. Invertibility of the subgroup cardinality in the
coefficient field is explicit. Idempotence is derived from the native projection
theorem, rather than supplied as an unexplained quotient-projector assumption.

For the native right regular action on real functions,

$$
(T_h f)(x)=f(xh),\qquad
P_H=|H|^{-1}\sum_{h\in H}T_h,
$$

the invariant function space is explicitly linearly equivalent to functions on
the quotient set. Normality is unnecessary for this function-space equivalence;
it is required for the native quotient-group representation.

A character is a function. Its operator realization is the multiplication map
\(D_\chi f(x)=\chi(x)f(x)\). The exact covariance law is

$$
T_hD_\chi=\chi(h)D_\chi T_h.
$$

Since the average absorbs every subgroup action on both sides, a character
nontrivial on H satisfies \(P_HD_\chi P_H=0\). A character trivial on H descends;
the multiplication operator is compatible with pullback along the native
quotient map and `QuotientGroup.lift`.

For a real sign character, \(D_\chi^2=1\). The existing binary logarithm formula
identifies the affine operator with multiplication by the actual function
\(\log(1+s\chi(x))\). In the positive range \(|s|<1\), its contrast is exactly
`Real.artanh s`.

The generic noncommutative theorem takes a real algebra A, an idempotent P, an
involution σ, and \(P\sigma P=0\). For \(L=u1+\delta\sigma\), it proves

$$
PLP=uP,\qquad PL^2P-(PLP)^2=\delta^2P.
$$

The existing `Core.PeirceCompressionDefect.compression_square_defect` identifies
the same quantity with the two complementary transfer factors. On the regular
function carrier, P is proved nonzero because it fixes the constant-one
function. Consequently, for the logarithmic coefficient, the defect is nonzero
if and only if s is nonzero. The synthesis instantiates this result with the
existing Walsh coordinate signs whenever H contains the corresponding bit flip.

The proof does not assume that the complementary diagonal block of σ vanishes.
A native three-by-three counterexample shows why that stronger assertion is
false: σ exchanges the first two coordinates and fixes the third, while P
selects the first coordinate.

## Galois frequency orbits and Ramanujan sums

`LanguageSymmetryGalois.lean` reuses
`Canonical.TwelveFoldCyclotomicNative` and Mathlib's actual cyclotomic Galois
equivalence. The generic carrier is a cyclotomic number field, not a list of
modular-arithmetic equalities presented as field automorphisms.

For the unit u corresponding to a Galois automorphism σ,

$$
\sigma(\zeta^{kx})=\zeta^{(uk)x}.
$$

Unit orbits on cyclic frequency indices are classified by exact additive order.
The shell of order d has cardinality φ(d), and the divisor-shell cardinalities
sum to N. For a primitive root, this is also a classification and count of the
distinct Galois-orbit values.

For a primitive complex root, the concrete harmonics are explicitly identified
with all complex additive characters. Reindexing Mathlib's character basis
therefore constructs a full basis of functions on `ZMod N`; its vectors satisfy
the existing circulant eigenvector theorem. This basis construction is separate
from the orbit-sum construction below.

The full unit-indexed sum is distinguished from its set of distinct values: when
x is not a unit, the sum can repeat orbit values according to their stabilizers.
The unit-indexed sum is identified with the field trace. Integrality of roots of
unity and integrally closedness of the integers supply integer-valuedness;
Galois invariance alone is not used to infer integrality.

The complex primitive-root sum is also related to the explicit Möbius formula

$$
c_N(x)=\sum_{d\mid\gcd(N,x)}d\,\mu(N/d).
$$

The route uses a partition of all Nth roots by exact order, finite character
orthogonality, and native Möbius inversion. The twelve-fold examples apply an
actual field automorphism associated to the unit five and reuse the existing
Klein-four Galois construction.

## Dihedral representations and their real form

`LanguageSymmetryDihedral.lean` constructs a native `DihedralGroup N` matrix
homomorphism from a character χ. In the paired-character coordinates,

$$
\rho(r_x)=\begin{pmatrix}\chi(x)&0\\0&\chi(-x)\end{pmatrix},
\qquad
\rho(s)=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

The actual native group multiplication establishes reflection inversion, the
rotation-order relation, and the ordered product of two reflections. Reflection
fails to commute with a rotation precisely when its two character values differ.
The associated paired native representation is irreducible exactly when χ is
distinct from its opposite. Self-inverse characters have an explicit proper
invariant line. In the complex frequency specialization, the constant and
order-two frequencies are therefore excluded from the irreducible
two-dimensional blocks.

The native action on cyclic vertices is constructed as a permutation-valued
group homomorphism. At N=3 it is proved injective, and the finite cardinality
calculation supplies the actual group equivalence
`dihedralThreeEquivPerm : DihedralGroup 3 ≃* Equiv.Perm (ZMod 3)`.

The real matrix representation uses the repository's existing Clifford matrix
generators. An explicit invertible complex change of basis intertwines this
real form with the paired-character representation. The finite Fourier block
uses the convention \(\sum_g f(g)\rho(g^{-1})\); its four real channels have
explicit coefficient sums, including the sign dictated by the inverse argument.
The irreducibility theorem applies to the paired representation. A separate
native real `Representation.IsIrreducible` theorem is not asserted.

The existing Peirce-spine owners supply the abstract rotor identities. Their
operator-valued square remains \(J^2=-V\). The native matrix specialization
proves V=1, rather than silently assuming that all Peirce corners are normalized.

The synthesis proves that entrywise Galois action permutes the frequency label
of these actual matrix representations. This is a field-automorphism statement;
it does not identify arbitrary Galois transformations with Euclidean isometries.

It also constructs a concrete quotient isomorphic to the dihedral group:
\((D_N\times\mathbb Z_2)/\ker(\mathrm{pr}_1)\cong D_N\). The explicit section
\(g\mapsto(g,1)\) supplies the native first-isomorphism construction, and a
compatibility theorem proves that its matrix action pulls back to the dihedral
action on the first factor. This establishes a dihedral quotient family, with
a nonabelian specialization at N=3. The cases N=1 and N=2 are abelian, and an
arbitrary quotient is not identified with a dihedral group.

## Scope corrections

- `PσP = 0` does not imply that σ has only off-diagonal Peirce blocks.
- Nonzero variance requires a nonzero coefficient and projector. Both conditions
  are handled explicitly; arbitrary-ring zero-divisor cases are not suppressed.
- The scalar `artanh` identity is not a construction or identification of a BKM
  metric.
- A Ramanujan sum is one invariant function, not a basis for an entire frequency
  shell.
- Galois action on complex characters is distinguished from action on real sine
  and cosine coordinates; the field element i may move too.
- Dihedral presentation relations alone do not prove an arbitrary `G/H` is
  isomorphic to `DihedralGroup N`.
- The implementation constructs and analyzes dihedral blocks. It does not claim
  a complete Peter–Weyl classification, Fourier inversion, or Plancherel theorem.
- No empirical language-model training claim follows from these finite results.

## Validation record

Validation was performed on 2026-11-07 with Lean `v4.34.1` (commit
`5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The root toolchain and dependency
pins are unchanged.

From the repository root with the pinned toolchain available:

```sh
python3 verification/language-symmetry/check.py build InfoGeometry.LLM.GaloisQuotientNonAbelianFourierAudit InfoGeometry.LLM.LanguageSymmetryRepresentationGeometryAudit --wfail
```

This command exited **0**, completing 8,947 jobs in the selected dependency
graph with no compiler warnings or errors. The two audits reported exactly
203 public declarations: 122 in the extension audit and 81 in the original
language-symmetry audit. Comparison with the source inventories found no
missing, extra, or duplicate audit entries. Their axiom union is exactly
`{propext, Classical.choice, Quot.sound}`. No `propext`-only claim is made.

Independent source review returned **PASS** for the frozen mathematical files.
Acceptance QA independently passed strict OpenGauss screening, strict refutation,
and the Gate 4 static review. The scoped semantic-content audit reported zero
findings, and the staged proof gate passed. These static results are separate
from Lean compilation and axiom inspection.

The optional semantic-vacuity scan with `--fail-on warning` exited **1** and
reported seven `trivial_surface` warnings. The raw warning result is retained;
it is not described as a clean scanner run. Independent reviewers accepted the
following short proofs after inspecting their actual statements and carriers:

| Declaration | Review disposition |
|---|---|
| `compression_affine` | Noncommutative distributivity with central scalar action and the explicit idempotence hypothesis. |
| `dihedralCharacterMatrix_r`, `dihedralCharacterMatrix_sr` | Evaluation rules for the constructed native matrix homomorphism. |
| `quotient_action_on_invariants` | Evaluation of the native quotient-group action on its invariant carrier. |
| `quotient_character_multiplier_compatible` | Compatibility of the actual quotient character multiplier with pullback. |
| `dihedralBinaryQuotientEquiv_mk` | Evaluation of the constructed quotient equivalence on representatives. |
| `dihedral_binary_quotient_matrix_action` | Compatibility of the matrix action with that quotient equivalence. |

No theorem was weakened or padded to change the heuristic result.

Separate non-authoring acceptance QA returned
**ACCEPTED_WITH_FOCUSED_VALIDATION_SCOPE**. It independently reran the focused
build and directly elaborated the extension audit with warnings treated as
errors:

```sh
python3 verification/language-symmetry/check.py env lean -DwarningAsError=true "$(pwd)/lean/InfoGeometry/LLM/GaloisQuotientNonAbelianFourierAudit.lean"
```

Both independent commands exited **0**. The direct audit finished at approximately
20:28 UTC and reported exactly 122 declarations, the same permitted axiom union,
and no Lean warnings or errors. All six reviewed source hashes were unchanged
before and after checking. All nine installed dependencies matched the root
and focused manifests and had clean tracked source trees.

### Integration boundary

The focused project reads the actual repository source files and uses the
maintained shared build lock. A fresh root-project integration attempt ran:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail InfoGeometry.LLM.GaloisQuotientNonAbelianFourierPoset
```

It exited **1** before theorem compilation because the configured optional local
package `external_refs/homotopy-hypothesis-lean4` is absent. This validation does
not certify the root default targets or the unrelated dependency subtree of
the broad `InfoGeometry.LLM` umbrella. The new umbrella import is included;
the pull request remains a draft at that integration boundary.

The session used a scratch-only process-path compatibility shim to redirect the
current process's numeric `/proc/.../exe` lookup to `/proc/self/exe`. It changes
no Lean proof or kernel API, and the pinned Lean/Lake binaries were unchanged.
A normal environment with the pinned toolchain does not need this workaround.

## Reviewed source fingerprints

The independent review and acceptance checks are tied to these SHA-256 values:

| Source | SHA-256 |
|---|---|
| `LanguageSymmetryGalois.lean` | `3ec4b8c460f06055f662583e2348c1940b2dbbced950b44d2e80888cc874ff56` |
| `LanguageSymmetryDihedral.lean` | `deb5bf73c3972185da8838f1ebbafe4e2aef9a50c76a96f50634a4dfd6511a75` |
| `LanguageSymmetryQuotient.lean` | `02b8d1e85365cb3912095f4c061f0abec92c150b47e4755e10abffd642409997` |
| `GaloisQuotientNonAbelianFourierPoset.lean` | `e23288700e9fea2f909c574ee07a8fd48d786714c75f38ab830be42567ac1f88` |
| `GaloisQuotientNonAbelianFourierAudit.lean` | `16499bb5029cba80f0ed8bdb4edc96b9843c29912a9d590d404489c7a22b29e9` |
| `FiniteMatrixNoncommutativeWitness.lean` | `f3f6aa453cc4391727fd978ae4f516054ad6d8ad5d2da36f86e817eecebe0057` |
