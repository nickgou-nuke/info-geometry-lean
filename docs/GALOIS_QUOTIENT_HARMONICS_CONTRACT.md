# Cyclotomic harmonics, dihedral blocks, and subgroup compression

## Intake and implementation baseline

The source is the user attachment `Pasted text(20261107-190608).txt`, received
2026-11-07: 32,914 bytes, SHA-256
`0ed44c8288e64cab1d103f19d97a2b4b5a0b884de935858fe851c296fe33b2d3`.
Its original bytes and extracted Lean block were frozen separately before
implementation. The supplied block contains three named theorems, despite its
claim of seven, and its prose makes stronger assertions than its declared types.

The extracted block was actually checked with Lean 4.34.1 and
`-DwarningAsError=true`. It exited with code 1: six unused-simplification
warnings promoted to errors, two invalid `calc` steps, and one unsolved goal.
The last three are proof failures, independently of the warning policy. Its
claim of a clean compilation and complete axiom audit therefore does not
certify that supplied module.

The implementation starts at `0eda6eda93a6e8e175cb4b85c0c0714c7ef115e3`
on `codex/finite-group-harmonics` (PR #297). This change is stacked on that PR
because the dihedral Fourier construction uses its actual finite group Fourier
owner. Lean remains `v4.34.1`; Mathlib remains
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Exact claim ledger

| Intake claim | Formal target or correction |
| --- | --- |
| Cyclotomic automorphisms permute Fourier frequencies | Construct the native cyclotomic additive character and prove covariance under `IsCyclotomicExtension.Rat.galEquivZMod`. |
| The twelvefold Galois group is Klein four | Reuse `TwelveFoldCyclotomicNative.cyclotomic12_galEquivUnits`, `cyclotomic12_gal_isKleinFour`, and the existing unit actions; numeral congruences alone do not construct this group. |
| Primitive-orbit sums are integers | Identify the actual sum over `(ZMod n)ˣ` with the field trace and prove integrality of that trace. Galois invariance alone only establishes membership in the fixed field. |
| One Ramanujan sum is a basis for an entire divisor shell | Not claimed. An orbit sum is one function; a shell with dimension greater than one requires additional independent vectors. |
| The displayed Möbius formula | Open in this change. Integer-valuedness and trace identification do not by themselves prove that closed formula. |
| Every opposite-frequency pair is irreducible | Prove the native two-dimensional representation criterion `k ≠ -k`; self-opposite frequencies are exceptional. |
| Two rotor identities construct a dihedral representation | Construct an actual monoid homomorphism on Mathlib's `DihedralGroup n` and prove its multiplication law. An abstract ring identity alone is insufficient. |
| A general quotient with rotation/reflection relations is dihedral | Not claimed. Relations supply a map from a presented group; identifying a quotient requires an isomorphism or equivalent additional data. |
| Four Peirce channels give a full matrix block | Prove all four entries and reconstruct a full complex two-by-two matrix in the existing spin-half coordinates. No replacement by scalar traces or diagonal surrogates. |
| Averaging is a quotient projector | Use native `Representation.averageMap` for the restricted right regular representation, derive idempotence, and identify its range with functions descending to the native coset quotient. |
| Macro/micro characters survive/disappear under compression | Prove the exact sandwich formula for the actual character multiplication operator; derive the two cases from restriction of the character to the subgroup. |
| Binary variance equals `b² P` | Derive the identity from the native average, an order-two character, and the existing ordered Peirce compression-defect theorem. |
| The logarithmic coefficient is `artanh s` | For `|s| < 1`, construct pointwise logarithm multiplication on `G → ℝ`, use the existing Walsh logarithm theorem and native `Real.artanh`, and derive its actual compressed variance. |
| The variance is always nonzero | Correct to an equivalence with `b ≠ 0` over a field; the actual averaging projection is proved nonzero. |
| `PσP = 0` implies both diagonal corners vanish | False. Supply a full real three-by-three matrix counterexample with an involution and a nonzero opposite corner. |
| `σ² = 1` truncates a Taylor series | False as stated: powers reduce modulo `t² - 1`, and `σ³ = σ` need not vanish. This is distinct from square-zero nilpotence. |
| Compression variance is a BKM metric or recovered linguistic information | Not asserted. This needs a separately constructed statistical model, metric, and interpretation bridge. |

## Owner-grounded contracts

### Cyclotomic harmonic orbits

Carrier: `CyclotomicField n ℚ`, with `n ≠ 0`, native additive characters on
`ZMod n`, native algebra automorphisms over `ℚ`, and units `(ZMod n)ˣ`.
For the native primitive root `ζ`, the harmonic is `χ (k * x)`.

Required implications:

1. The Galois automorphism corresponding to `u` sends the harmonic at `k` to
   the harmonic at `u * k`, with multiplication in `ZMod n`. The induced
   permutation preserves `addOrderOf k`, hence preserves exact-order shells.
2. The actual unit-indexed sum is the image of
   `Algebra.trace ℚ (CyclotomicField n ℚ) (χ x)`.
3. The root of unity is integral over `ℤ`; integrality passes to its powers and
   field trace; a rational element integral over `ℤ` is an integer.
4. Unit reindexing and Galois invariance follow for that same sum. The value
   at zero is the totient, and the native cyclotomic degree/totient divisor
   identity records a dimension count without asserting a new shell basis.
5. The existing unit-five automorphism at order twelve acts on the actual
   harmonics at frequencies one, five, three, and six.

Existing owners read: `Canonical.TwelveFoldCyclotomicNative`,
`Canonical.TwelveFoldArithmeticNative`, `Canonical.TwelveFoldGaloisCharacterSets`.
Native owners include `NumberTheory.NumberField.Cyclotomic.Galois`,
`NumberTheory.LegendreSymbol.AddCharacter`, and `RingTheory.Trace.Basic`.

### Dihedral Fourier blocks

Carrier: Mathlib's `DihedralGroup n`, `Matrix (Fin 2) (Fin 2) ℂ`, and the native
`Representation ℂ (DihedralGroup n) (Fin 2 → ℂ)`. For an additive character `χ`,
the two branches are

\[
\rho(r_i)=\begin{pmatrix}\chi(i)&0\\0&\chi(-i)\end{pmatrix},\qquad
\rho(sr_i)=\begin{pmatrix}0&\chi(-i)\\\chi(i)&0\end{pmatrix}.
\]

All four products follow the native dihedral multiplication convention.
Periodicity, reflection square, and reflection conjugation are consequences
of this actual homomorphism. Distinct opposite eigenvalues and the swapping
reflection imply no proper nonzero invariant subspace. Equal frequencies
preserve a proper line. For the standard cyclic character this yields the
exact irreducibility criterion `k ≠ -k`.

The finite Fourier coefficient uses the existing forward convention
`Σ g, f g • ρ g`; convolution is
`(f * h)(x) = Σ y, f y * h (y⁻¹ * x)`.
The proved multiplication order is `F(f * h) = F(f) * F(h)`.
The inverse-argument convention belongs to the existing opposite-algebra
owner and reverses the order. This module does not construct a complete
irreducible dual, prove Peter–Weyl inversion, or identify an arbitrary quotient
with a dihedral group.

Existing owners read: `Algebra.FiniteGroupFourier`,
`Algebra.NoncommutativePlaneWaveKernel`, `Algebra.FiniteSpinAlgebra`,
`Core.PeirceMatrixRepresentation`, and `Core.QuartetIndependence`.
The existing `Canonical.SixStateD6C2S3.d3PermutationEquiv` already owns a genuine
order-six dihedral/permutation equivalence; it is not duplicated here.

### Subgroup compression and variance

Carrier: a field `k`, a group `G`, a finite subgroup `H`, and
`Invertible (Fintype.card H : k)`. Only `H` must be finite. Endomorphisms act on
the full function space `G → k`, with actual composition as multiplication.

The projector is native `Representation.averageMap` of
`TannakaDuality.FiniteGroup.rightRegular` restricted through `H.subtype`:

\[
(P_H f)(x)=|H|^{-1}\sum_{h\in H} f(xh).
\]

Native projection theorems establish its idempotence and invariant image.
The image is identified with pullbacks of functions on the native coset
quotient. Normality is required for group quotient character descent, not
for the averaging map or the underlying coset-space statement.

For a native character `χ : G →* k`, its multiplication operator is
`LinearMap.mulLeft k (χ : G → k)`. The sandwich formula gives zero precisely
in the nontrivial-restriction case used here, and unchanged action when the
restriction to `H` is trivial. For a binary character and `L = a • 1 + b • Mχ`,
the micro case gives

\[
P_H L P_H=aP_H,\qquad
P_H L^2P_H-(P_HLP_H)^2=b^2P_H.
\]

The average fixes the constant-one function, so it is nonzero. Over the field,
the displayed defect is nonzero if and only if `b ≠ 0`. The coefficients in
this core statement are algebraic parameters; it does not silently supply
hypotheses for a BKM metric.

Existing owners read: `Core.PeirceCompressionDefect`,
`OperatorAlgebra.PeirceCompressionCurvature`,
`OperatorAlgebra.PeirceCompressedGramPositivity`, and the native Mathlib
`RepresentationTheory.Invariants` and `RepresentationTheory.Tannaka`.
The ordered defect theorem is reused, rather than reintroduced as an axiom.

### Pointwise logarithm compression

A separate higher-level bridge on `G → ℝ` constructs the multiplication map
for the actual function `x ↦ Real.log (1 + s * χ x)`, with `|s| < 1` and a
binary real character. It reuses
`LLM.WalshCharacterGeometry.log_one_add_mul_of_sq_eq_one` and native
`Real.artanh_eq_half_log` to identify its coefficients as
`Real.log (1 - s²) / 2` and `Real.artanh s`. When the character is nontrivial
on the finite subgroup (`∃ h : H, χ h ≠ 1`), the subgroup compression results
yield the first moment and the exact defect `(Real.artanh s)² • P_H`.
Native `Real.tanh_artanh` identifies nonzero defect with `s ≠ 0` under these
same hypotheses. A character trivial on the subgroup is not covered by that
nonzero-defect assertion.
This is pointwise logarithm multiplication, not an arbitrary noncommutative
operator logarithm or an identification with a BKM metric.

### A failed one-corner implication

The counterexample uses full real matrices

\[
P=\operatorname{diag}(1,0,0),\qquad
\sigma=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix}.
\]

It proves `P² = P`, `σ² = 1`, and `PσP = 0`, while the `(2,2)` entry of
`(1-P)σ(1-P)` is one. It also proves actual noncommutativity `Pσ ≠ σP` by
comparing their `(0,1)` entries, one and zero respectively. Therefore `σ` is
not the sum of its two off-diagonal corners. This does not contradict the
compression-variance identity, which
does not require that stronger off-diagonal hypothesis.

## Dependency structure and acceptance

The three constructions have independent premises. They are not a single
causal theorem inferred from similar terminology. Their proved dependencies
are respectively cyclotomic automorphism → harmonic action → trace/integrality;
native dihedral multiplication → matrix representation → irreducibility and
Fourier blocks; and subgroup representation → averaging projection → character
compression → ordered variance. The final logarithm bridge uses both the
existing Walsh identity and the new subgroup compression owner.

Generation, semantic review, and acceptance are assigned to separate roles.
Acceptance must include fresh compilation of the exact selected source closure,
warnings-as-errors for new owners, a prohibited-proof scan, declaration type
and value axiom audits, and execution of the repository's actual commit and
push gates. Permitted foundational axioms are `propext`, `Classical.choice`,
and `Quot.sound`; this is not a claim of a `[propext]`-only development.

### Observed validation, 2026-11-07

Initial independent acceptance rebuilt the complete selected repository-source
closure: **17 modules, exit 0**, using Lean 4.34.1 and the Mathlib revision
recorded above. Every compiler invocation used `-DwarningAsError=true`. All
five new owner logs were empty. The existing `SixStateSpectralBridge` dependency
emitted two informational tactic suggestions, not warnings or errors.

The actual staged commit gate then required an explicit noncommutativity
witness in the counterexample owner (OpenGauss T16). The repair adds only the
seven-line proof `rankOneProjection_swapWithFixedAxis_noncommute`, with the
existing declarations, imports, and header unchanged. A separate independent
delta acceptance freshly compiled that exact changed owner with warnings as
errors, audited all of its 11 constants, and reconciled the unchanged hashes
of the other 16 closure modules and both umbrella files. The updated owner
SHA-256 is `ed9a9070fd6197a53f3a92bb41554f48fd4de006b5a60eebc384cd5a69475a23`.
The original acceptance evidence was preserved. This is a fresh 17-module
baseline plus a checked single-owner replacement, not a claim that all 17
modules were rebuilt again after the repair.

The maintained `tools/quality/check_operator_geometry.py` was invoked with
`--mathlib` pointing to that exact pinned checkout, `--lean` pointing to a
wrapper executing `lean -DwarningAsError=true`, a fresh `--work-dir`, and these
five `--target` arguments for the baseline:

- `InfoGeometry.Arithmetic.CyclotomicHarmonicOrbits`
- `InfoGeometry.Algebra.DihedralFourierBlocks`
- `InfoGeometry.Algebra.SubgroupCompressionVariance`
- `InfoGeometry.Algebra.OneCornerCounterexample`
- `InfoGeometry.LLM.SubgroupLogCompression`

The independent delta run used the same maintained checker with only
`InfoGeometry.Algebra.OneCornerCounterexample` as its target and a separate
fresh output directory. Both runs exited 0.

The native Lean audits select declarations by actual owner module, including
generated and private declarations, and inspect both type and value dependencies
transitively. Replacing the old counterexample records with its fresh complete
audit leaves 116 unchanged records and 11 freshly checked records:

| Owner | Audited declarations |
| --- | ---: |
| `Arithmetic.CyclotomicHarmonicOrbits` | 32 |
| `Algebra.DihedralFourierBlocks` | 37 |
| `Algebra.SubgroupCompressionVariance` | 35 |
| `Algebra.OneCornerCounterexample` | 11 |
| `LLM.SubgroupLogCompression` | 12 |
| **Total** | **127** |

The final audited inventory contains 95 theorem constants and 32 definition
constants, including Lean-generated declarations. The source contains 68
named theorems and 12 named definitions. All 127 constants have both type and
value available. The union of actual declaration, type-dependency, and
value-dependency axiom sets is exactly
`{propext, Classical.choice, Quot.sound}`. No local axiom, unsafe or partial
declaration, `sorry`, `admit`, or `native_decide` was accepted. The four untouched
owner hashes and all baseline evidence matched; the changed owner matched its
new frozen hash throughout delta acceptance.

The current five-source/prohibited-proof scan and the ten explicit
umbrella-import checks passed. These import checks verify presence and
uniqueness, not compilation of the two full umbrella modules. The maintained
semantic-vacuity gate exited 0 with no errors and the same three soft
`trivial_surface` warnings: `pairedMatrix_r`, `pairedMatrix_sr`, and
`pairedRepresentation_apply`. Semantic review confirmed that these are public
definitional evaluation/adaptor equations; the substantive homomorphism,
irreducibility, and Fourier proofs are separate declarations.

An actual maintained root-package build was also attempted before the
single-theorem repair:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail \
  InfoGeometry.Arithmetic.CyclotomicHarmonicOrbits \
  InfoGeometry.Algebra.DihedralFourierBlocks \
  InfoGeometry.Algebra.SubgroupCompressionVariance \
  InfoGeometry.Algebra.OneCornerCounterexample \
  InfoGeometry.LLM.SubgroupLogCompression
```

It exited **1** during dependency resolution, before owner compilation, because
the inherited local package `external_refs/homotopy-hypothesis-lean4`
(`HomotopyHypothesis`) is absent. That unchanged local-path manifest entry has
no repository URL or immutable revision from which this change could restore
it. No placeholder package was created and no dependency pin was changed.
Thus the selected native-source closure is verified by the composed evidence
above, while a green root-package build and full umbrella compilation remain
unverified. The change is prepared for a draft review PR; the final actual
commit/push-hook outcomes are reported with that PR after they run.
