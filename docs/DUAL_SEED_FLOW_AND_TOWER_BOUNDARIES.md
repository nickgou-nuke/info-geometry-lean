# Dual-seed flows, graded tails, and modular boundaries

## Intake and provenance

This extension follows the Bulgarian attachment
`Pasted text(20261110-093644).txt` supplied on 2026-11-10, SHA256
`614daea5d6927c26220ca1ecd1c1acacb204ac9e5d48ffbb79197c3698d30503`.
The implementation starts from PR #304's published source tree
`7283335edbb2711d41dc2aac46938e516a2921fb`, commit
`8d5139f76343b3d4e5a73fea40d1692f894fdf83`.

The intake combines source/sink boosts, a common commutant, graded Clifford
head/tail limits, Tomita modular theory, KMS temperature, conformal inversion,
Radon–Nikodym derivatives, and entropy gradients. Similar terminology does
not establish maps between these constructions.

## Ground-truth contract

Use the existing `IsDualSeedPair d b` in an arbitrary associative ring:
`d*d=0`, `b*b=0`, `d*b*d=d`, `b*d*b=b`. Let the existing aliases denote
`p=db`, `q=bd`, `r=1-p-q`, and `H=p-q`. The common commutant is the native
`Subalgebra.centralizer R {d,b}`. The existing projection is
`Φ(a)=p*a*p+b*a*d+r*a*r`.

The implementation targets are:

1. Polynomial naturality of `Φ` under native algebra homomorphisms and
   invariance under reciprocal rescaling of the seeds. These need no seed
   equations.
2. Strict containment `C({d,b}) < C({H})` when `d ≠ 0`, witnessed by `p`.
3. In a complete normed real algebra, identify the actual native exponential
   `exp(t • H)` with `r + exp(t) • p + exp(-t) • q`.
4. Reuse the existing `ConcreteSplitCartan.splitCartanHom` unit to obtain the exact
   weights `exp(2*t)` and `exp(-2*t)` on the two seeds, pointwise fixation of
   the common commutant, and invariance of `Φ` under this boost.
5. Distinguish the directional projection's behavior under parabolic shear
   and under simultaneous anticommutation. For elements anticommuting with
   both seeds, the parity correction is `Φ(a)=a*(H+r)`.

The attachment's parameter is recovered by setting `t=θ/2`. No new law-bearing
packet, surrogate scalar algebra, or assumed invariance field is introduced.
The analytical hypotheses belong only to actual exponential results.

## Implemented statements and dependency order

`Core/DualSeedCentralizer.lean` first proves polynomial naturality and
reciprocal normalization of the existing linear map. It also evaluates the
projection on the negative pole and on `H`. These evaluations give

```text
Φ((1+s*d)*b*(1-s*d)) = s*(p+q).
```

Thus this directional projection need not be preserved by a parabolic shear.
For any element satisfying `a*d=-(d*a)` and `a*b=-(b*a)`, the same owner proves
`Φ(a)=a*superInvolution d b=a*(H+r)`. Together with the existing range theorem,
this places the parity-corrected element in the ordinary common commutant.
This is a general algebraic implication; the patch does not construct a new
Clifford tower or identify an entire infinite commutant.

`Canonical/JointCentralizerGeometry.lean` proves the native subalgebra
inclusion `C({d,b}) ≤ C({H})` without seed equations and its strictness under
`IsDualSeedPair d b` and `d≠0`. The positive pole witnesses strictness via
`pd=d` and `dp=0`. Unlike the earlier separation using `H` itself, this does
not require `2*d≠0`.

`Canonical/JointCentralizerDynamics.lean` uses a complete normed real algebra:

| Declaration | Exact result |
| --- | --- |
| `exp_phasePolarization` | `NormedSpace.exp (t • H) = completedBlock d b (Real.exp t) 0 0 (Real.exp (-t))`. |
| `splitCartanHom_eq_diagonalUnit` | The existing actual exponential unit equals the existing reciprocal completed diagonal unit. |
| `splitCartan_conjugates_seed` | `U(t)*d*U(t)⁻¹ = exp(2*t) • d`. |
| `splitCartan_conjugates_partner` | `U(t)*b*U(t)⁻¹ = exp(-(2*t)) • b`. |
| `splitCartan_fixes_jointCentralizer` | `U(t)*a*U(t)⁻¹=a` for every `a∈C({d,b})`; no seed equations are needed for this implication. |
| `centralizerProjection_splitCartan` | `Φ(U(t)*a*U(t)⁻¹)=Φ(a)` on every ambient element. |

Here `U(t)` is notation for the value of the existing `splitCartanHom`, not a
new definition. The exponential proof transports the three spectral factors
through Mathlib's `SemiconjBy.exp_right`, using `Hp=p`, `Hq=-q`, `Hr=0`, and
`p+q+r=1`. Projection invariance then uses the native conjugation algebra
equivalence, polynomial naturality, reciprocal seed rescaling, and fixation
of the projection's image. The proof does not assume that `U(t)` centralizes
the seeds.

`Canonical/JointCentralizerDynamicsAudit.lean` uses the already existing dense
noncommuting real `3×3` pair. It provides closed witnesses for strict
centralizer inclusion and parabolic noninvariance. For the actual completed
blocks with weights `(2,1/2)` and `(1/2,2)`, it proves determinant one,
nontrivial action on the seed, and failure to preserve the matrix adjoint.
The reciprocal blocks are mutual inverses by the existing
`completed_diagonal_inverse` and the scalar equation `2*(1/2)=1`.

The computed determinant concerns this `3×3` matrix acting on `ℝ³`. No
Jacobian of the conjugation action or Radon–Nikodym derivative is constructed
by the numerical witness. Likewise, failure of Hilbert-adjoint
preservation rules out an automatic identification of this real similarity
with a Hilbert-star modular automorphism flow; a different representation or
imaginary-time relation would require a separate theorem.

## Claim ledger

| Intake claim | Exact boundary |
| --- | --- |
| The common commutant centralizes the commutator | Valid for chosen elements `d,b`; it follows from polynomial commutation without seed equations. |
| The boost fixes the common commutant | Valid pointwise when the exponential or algebraic inverse is defined. |
| The commutator generates the common-centralizer kernel | False in general: `H` need not commute with the seeds. |
| The common commutant is the whole boost-fixed algebra | False in general: `p` commutes with `H`, but `pd=d` and `dp=0` when `d≠0`. |
| The boost exchanges source and sink | Its adjoint action scales the two directions oppositely. A Weyl element supplies a different, exchanging action. |
| Hyperbolic and parabolic flows are the same | `H` gives scaling; a square-zero seed gives `1+s*d`. The existing unipotent and torus owners distinguish them. |
| The entire Clifford tail centralizes an odd head | The actual Clifford head/tail tensor product is graded. Odd elements supercommute with a minus sign; an ordinary commutant needs a parity correction. |
| A Clifford signature forces a Krein representation | An involution and representation metric must be specified. The quadratic signature alone does not establish this necessity. |
| Tomita conjugation is a Krein fundamental symmetry | Standard modular conjugation is antiunitary and conjugate-linear; a Krein fundamental symmetry is linear. An explicit realification/intertwining is missing. |
| States are ideals | States are positive normalized functionals. GNS associates a left null ideal; the ideal does not in general recover the functional. |
| The tower determines a type III factor | Requires a completion, state, GNS representation, and weak closure; the algebraic tower alone does not select the type. |
| `β = log(λ)*d_H` universally | No dynamics normalization or self-similar/KMS construction is supplied. For `0<λ<1` and `d_H>0`, the displayed value is negative. |
| Inversions are strict contractions | A nontrivial involution cannot be a strict contraction globally. A restricted iterated-function system needs its own contraction and separation proofs. |
| `-log Jac` universally generates the boost | A nontrivial volume-preserving boost has determinant/Jacobian one. A specific action and reference measure are indispensable. |
| Modular time supplies entropy dissipation | Modular dynamics preserves its defining state. Reduced dynamics or another dissipative construction is additional data. |
| A Krein gradient maximizes entropy increase | A gradient is normal to level sets by its defining pairing. An indefinite metric does not supply the sign needed for increase. |
| The commutant is an Apollonian radical axis | Still requires a particular geometric realization and a compatibility theorem. |

## Bounded owner search and reuse

The search inspected actual definitions, hypotheses, proofs, imports and
consumers. This is not a fresh repository-wide declaration-DAG audit.

| Owner | Relevant source-backed content |
| --- | --- |
| `Core/DualSeedPeirce`, `Core/DualSeedCartan` | Existing reflexive square-zero pair, Peirce multiplication table, and native `sl₂` relations. |
| `Core/DualSeedCentralizer` | Existing native linear projection and its exact common-commutant range. |
| `Core/PeirceRotor`, `Core/PeirceBilateralAction` | Completed blocks, harmonic annihilation, reciprocal diagonal units and bilateral maps. |
| `Lie/ConcreteSplitCartan` | Actual native exponential units and their one-parameter group law; the group construction does not require `H²=1`. |
| `Canonical/ReflexiveNilpotentFlows`, `ReflexiveFlowUnits`, `ReflexiveParabolicUnits` | Actual noncommutative torus, Weyl and unipotent laws. |
| `Canonical/TransportLieDerivative` | Actual Banach-algebra exponential conjugation and its commutator derivative. |
| Mathlib normed-algebra exponential | `SemiconjBy.exp_right`, `Commute.exp_right`, and scalar algebra-map compatibility. |
| `Canonical/SplitCliffordFiniteHeadTail`, `SplitCliffordHeadTailTower`, `SplitCliffordHeadTailParity` | Genuine graded finite factorization, full-algebra transition compatibility, algebraic direct-limit equivalence and supercommutation. |
| `Canonical/GrowingOnsiteMatrixHamiltonian` | Genuine ordinary matrix-tail embedding and `concreteStep_commutes_tail`; distinct from a raw odd Clifford tail. |
| `Canonical/FiniteSeedRepresentedAnalyticKMS` | Existing represented finite-seed positive state and analytic KMS strip results for `β>0`. |
| `Canonical/FiniteSeedGibbsTomitaClosability` | Derived finite-stage faithfulness/closability and actual Hilbert-completion constructions. |
| `Canonical/FilteredGNSCofinalTail` | Cofinal-index Hilbert colimit equivalence; this is not a tensor-complement algebra identification. |
| `OperatorAlgebra/SpatialDerivativeLogarithmicVariation` | Noncommutative logarithmic derivatives; reduction to `-K'` requires tangent commutation. |
| `Canonical/RadonNikodymSurprisalJacobianBridge` | Retired scalar compatibility surface; its header explicitly excludes a constructed flow Jacobian/Radon–Nikodym derivative. |
| `Thermodynamics/SouriauFoliation` | Witness-gated leaf readouts and preservation; not a derived dissipative Krein gradient. |

The strong positive-state and analytic KMS owners must not be downgraded to
the weaker weighted-trace or conditional Tomita interfaces. Conversely, their
actual hypotheses do not prove the attachment's type III/fractal claims.

The focused analytic owner imports the existing split-Cartan unit rather than
the larger transport/Clifford tower. It proves equality with the existing
completed diagonal unit. The retained residual term is essential because
`H²=p+q` need not equal the ambient identity. The tower and KMS owners above
were inspected as source; they are not included in this extension's compiled
dependency closure or claimed as newly verified results.

## Primary mathematical references

- Fumio Hiai, *Concise lectures on selected topics of von Neumann algebras*,
  https://arxiv.org/abs/2004.02383, §§1.5–1.6 and Proposition 2.16 — modular
  conventions, state centralizers, and the state dependence of infinite
  tensor-product factor types. The state centralizer is a fixed-point algebra;
  it is not generally the algebraic center.
- Marius Ionescu and Alex Kumjian, *Hausdorff Measures and KMS States*,
  https://arxiv.org/abs/1002.0790, Introduction and Theorem 3.4 — a specified
  local-scaling construction linking Hausdorff measures and KMS states.
  In the self-similar example with the open set condition, choosing energies
  `E_j=-log r_j` aligns `sum r_j^d=1` with `sum exp(-β*E_j)=1`, giving `β=d`
  for that normalization. It does not supply a universal `β=log(λ)*d_H` law.

## Verification record

The independent mathematical review accepted the full source and the
one-import follow-up. The independent execution verifier checked the exact
source with Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No toolchain or dependency pin changed.

The first QA run rebuilt all **40 repository modules** in the selected import
closure with no incremental reuse. All five target files compiled without
warnings and separately passed actual `lean -DwarningAsError=true`
elaboration. The native audit enumerated **63 declarations**, including
private/generated declarations, with only `propext`, `Classical.choice`, and
`Quot.sound`.

That first run was **not accepted**: the strict static gate required a direct
carrier-matched noncommutativity witness import in the new dense audit file.
The existing `FiniteMatrixNoncommutativity` owner was already in the transitive
closure through `RealCartanWitnesses`. The repair added precisely that direct
import. Independent review confirmed that removing this line reproduces the
original audited file byte-for-byte, including every statement and proof.

The separate QA supplement reused the 39 unchanged, hash-matched compiled
modules, rebuilt the repaired audit, reran the full 63-declaration native
audit, and repeated the repaired file's Werror check. These checks passed.
The strict screen/refute commands and static Gate 4 then passed for all five
targets. This is **a fresh 40-module run followed by an independently checked
one-import repair**, not a claim that the final snapshot was rebuilt entirely
without reuse. The rejected first-run evidence is retained separately from
the accepted supplement in `scratch/dual-seed-flow-qa` and
`scratch/dual-seed-flow-qa-supplement`.

| Selected module | Audited declarations | Final warnings |
| --- | ---: | ---: |
| `Core.DualSeedCentralizer` | 30 | 0 |
| `Canonical.JointCentralizerGeometry` | 14 | 0 |
| `Canonical.JointCentralizerGeometryAudit` | 2 | 0 |
| `Canonical.JointCentralizerDynamics` | 12 | 0 |
| `Canonical.JointCentralizerDynamicsAudit` | 5 | 0 |

The unchanged imported owners emitted 41 warnings: `MoorePenrose` 14,
`PeirceDecomposition` 1, `JordanPeirceDecomposition` 2, `JordanAssociator` 7,
and `HestenesKreinOperatorCalculus` 17. Their source hashes were checked
against the recorded repository head. Target warning-free status is not a
claim that all imported historical sources are warning-free.

The vacuity heuristic retained the earlier `dualSeed_trace_zero` regex
signal. Independent inspection confirmed that the proof uses `h.pd.symm`
and `h.dp`; the regex inspects only its first proof line. The finding is
classified rather than suppressed. The other four targets had no findings.
Static Gate 4 reports `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`; the separate
Lean elaborations and native axiom audit provide the kernel evidence.

The updated workflow parsed as YAML, all five Bash run blocks passed
`bash -n`, and all three embedded Python blocks parsed with `ast.parse`.
These are syntax checks, not a claim that hosted GitHub Actions ran.

### Reproduction commands

The initial exact-source check was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root .lake/packages/mathlib --output scratch/dual-seed-flow-qa \
  --target InfoGeometry.Core.DualSeedCentralizer \
  --target InfoGeometry.Canonical.JointCentralizerGeometry \
  --target InfoGeometry.Canonical.JointCentralizerGeometryAudit \
  --target InfoGeometry.Canonical.JointCentralizerDynamics \
  --target InfoGeometry.Canonical.JointCentralizerDynamicsAudit
```

The supplement used a separate copy of those artifacts, the same five
targets, `--output scratch/dual-seed-flow-qa-supplement`, and `--incremental`.
The checker enforces exact source/artifact hashes and holds the shared build
lock. Werror checks used the corresponding copied sources and recorded
`LEAN_PATH`, also under the shared build lock. The static commands were:

```bash
dual_seed_targets=(
  lean/InfoGeometry/Core/DualSeedCentralizer.lean
  lean/InfoGeometry/Canonical/JointCentralizerGeometry.lean
  lean/InfoGeometry/Canonical/JointCentralizerGeometryAudit.lean
  lean/InfoGeometry/Canonical/JointCentralizerDynamics.lean
  lean/InfoGeometry/Canonical/JointCentralizerDynamicsAudit.lean
)
python3 tools/infra/opengauss_screener.py --strict "${dual_seed_targets[@]}"
python3 tools/infra/opengauss_cli.py refute "${dual_seed_targets[@]}" --strict
python3 tools/infra/opengauss_cli.py review "${dual_seed_targets[@]}" --gate GATE_4
```

The actual scoped root-package attempt was:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Core.DualSeedCentralizer \
  InfoGeometry.Canonical.JointCentralizerGeometry \
  InfoGeometry.Canonical.JointCentralizerGeometryAudit \
  InfoGeometry.Canonical.JointCentralizerDynamics \
  InfoGeometry.Canonical.JointCentralizerDynamicsAudit
```

It exited 1 before elaboration because the declared path dependency
`external_refs/homotopy-hypothesis-lean4` is absent. The selected source
closure is accepted at its stated scope; the root package is not certified.

### Pre-push result and draft publication

The installed pre-commit hook passed for mathematical extension commit
`d25cac2c3fd6dea7a8f3cd476cb311022b64612b`. The installed pre-push hook was
then run with that exact local commit and the existing published branch head
`8d5139f76343b3d4e5a73fea40d1692f894fdf83` as the comparison base. It exited 1.
The observed failures were the same root boundaries as in the initial draft:

1. The locked Lake invocation stopped before elaboration because
   `external_refs/homotopy-hypothesis-lean4` is missing.
2. The semantic scan of **26,989** files in `lean/` reported the two existing
   `True`/`trivial` findings in `Physics/NuclearColimit.lean`, namely
   `colimit_pairing_compat` and `colimit_pairing_compat_trivial`.

The latter file is byte-identical to both the original `main` base and the
previous published PR head, with SHA256
`294541eb235d232b4ea132190efdc1dbb2f9a6743bc75d7e8885c4edc41aaf73`.
It is outside the verified 40-module closure. The gate's debt scan of the
four changed Lean files found zero gaps, and the tracked-scope and quarantine
audits passed. The exact ref-update input, exit status and log digest are in
`scratch/dual-seed-flow-publication/pre-push-result.json`; the observed log is
`scratch/dual-seed-flow-publication/pre-push.log`.

The documentation follow-up records this outcome without changing any Lean
source or workflow. PR #304 remains a draft under the user's explicit
publication authorization for this work despite the documented existing gate
failures. Selected-source acceptance and publication do not turn the failed
root gate into a successful build.

### Final reviewed Lean source hashes

| File | SHA256 |
| --- | --- |
| `Core/DualSeedCentralizer.lean` | `9090c4f47ee96db3367d1566cc55fb3315ff0e512f91d93f51a0db5aa0bd3dd7` |
| `Canonical/JointCentralizerGeometry.lean` | `90e0cc315ccadfc418d7f832eee3161339de5b983f60c75a6a5ac62e4a0eda10` |
| `Canonical/JointCentralizerGeometryAudit.lean` | `3801d51cd2eda25489cd940c23c9b3c135b50e56f0826b7620a9026faf003406` |
| `Canonical/JointCentralizerDynamics.lean` | `6831d17843c4771632b936761089a99b49f40462310b8aa47637a6ffb7706d56` |
| `Canonical/JointCentralizerDynamicsAudit.lean` | `068c775f623c645f2bdeebb33c03882d1828a494303eb78d71a211ef7935b940` |
