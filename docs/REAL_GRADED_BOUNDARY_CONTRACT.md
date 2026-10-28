# Real graded boundary compilation

## Source, reuse and branch ownership

This package extracts the four uploads without promoting their physical labels:

| Source | SHA-256 |
|---|---|
| Pasted text(20261028-120949).txt | 70a02c2bfae6f92aa8a21c60738777361541a52ec546ad8770474ffda75323af |
| Pasted text (2)(20261028-121051).txt | da48160c8e6e84b3ba8696a97520282e8b4fd8e604346d215f8ea03d37602180 |
| Pasted text (3)(8).txt | 9accca3218bb34d7bbc033e6c0c6ed17ad9718b526cd2e2d835c139d9974c308 |
| Pasted text (4)(2).txt | c9ea1b3660df958f1492aa1bb7aa48a1a59abb84439546bd958ba1180cfe8c85 |

The dependency is PR #250 at f550271b141afb44c0ff52fec81eb1552a45ebca.
Its actual LieJordanEndomorphisms and PeirceLieJordanResolution owners are reused,
not copied. This branch does not alter that parent or PRs #227/#248/#255/#256.
The parent is a draft; only the selected imported owners are checked here,
not its whole branch. No merge is performed.

Source searches also inspected Core.IdempotentCartan, Core.PeirceGrading,
Core.PeirceDecomposition, Algebra.IdempotentProjector,
Canonical.ChiralSuperderivationColimit, Core.DiracPeirceSuperalgebra and
OperatorAlgebra.InnerConjugation. The existing Boolean-tagged superderivation
already has a parity-flipped square theorem. The addition here is an untagged
endomorphism on the full algebra, a concrete Peirce grading, a native short
complex, and a proved positive-pairing adjoint. No graph service was queried;
no declaration-DAG freshness is claimed.

## Source corrections (not silent replacements)

1. The first upload's prose says the Jordan boundary squares to zero on every
   matrix. Its actual code proves mixed Lie/Jordan cancellation instead.
   With L_q(x)=qx-xq and J_q(x)=qx+xq:
   L_q^2=J_(q^2)-2(x -> qxq), J_q^2=J_(q^2)+2(x -> qxq).
   Thus q^2=0 does not make either ordinary action square-zero. The mixed
   compositions L_q J_q and J_q L_q do equal L_(q^2).
2. The second upload's mixed difference is false:
   L_a J_b-L_b J_a = J_(ab-ba)+2(x -> axb-bxa).
   The actual operator commutator L_a J_b-J_b L_a=J_(ab-ba) is already in #250.
   These have different second terms; no factor has been dropped here.
3. The source's mixed sum equals L_(ab+ba), as stated. It is not automatically
   the positive Hodge Laplacian. The adjoint construction below is distinct.
4. The trace identity for axb+bxa holds for every matrix x, not just even ones.
   Positivity is proved under b=a^T; trace preservation is proved under
   ab+ba=I. These are explicit sufficient hypotheses of the stated theorems.
   The implementation proves positivity preservation, not a complete-positivity
   amplification theorem and not a normalized channel without hypotheses.
5. The last two uploads supply valid algebraic reciprocal-derivation and
   quadratic conservation identities. An ad_P two-cycle is not a periodic
   real-time oscillator. In particular a real evolution j'=e,e'=j is hyperbolic.
   No frequency, spacetime signature, spin, mass or particle identification is
   inferred from the ring identities. The square operator need not be scalar or
   central in the ambient matrix algebra, so no automatic Cl(1,1) representation
   over the original scalar field is asserted.
6. The advertised two-line normalizer is not proved a complete Knuth--Bendix
   procedure. Each concrete theorem is individually checked by Lean. We do not
   claim that every identity in the input has already been kernel verified.

## Native carrier and exact operator contracts

All general operators live in Module.End R A, where R is a commutative scalar
ring and A is an arbitrary associative R-algebra. A is not assumed commutative.
The metric carrier is Matrix n n real for arbitrary finite n. The explicit
regressions use Matrix (Fin 4) (Fin 4) real.
No complexification, diagonalization or simultaneous commutativity is used.

The actual maps L_q and J_q are inherited from #250. sandwichOp is ordered
left/right composition, and crossTransport(a,b)(x)=axb+bxa.
LieJordanBoundaryComposition proves both mixed sums, the corrected difference,
both pure sums, and their two- and four-fold combinations as endomorphism
identities. The existing lie_lie and lie_jordan laws are not duplicated.

For an involutive algebra automorphism theta and theta(q)=-q, define
  d_q(x)=qx-theta(x)q,
  c_q(x)=qx+theta(x)q.
Then d_q obeys the twisted Leibniz law on all elements, reverses parity, and
satisfies d_q^2=L_(q^2). If q^2=0, its native range lies in its kernel and
ShortComplex (ModuleCat R) is constructed with both differentials d_q.
The concrete theta is the scalar-compatible upgrade of the existing
IdempotentCartan.reflectionConj, with S=2P-I and theta(x)=SxS.
For q=P a (I-P), oddness and q^2=0 are derived, not supplied separately.

Two minus actions satisfy {d_q,d_r}=L_(qr+rq). In contrast
{d_q,c_r}=J_(qr+rq). For real self-adjoint P, r=q^T gives the actual
Frobenius adjoint:
  tr((d_q x)^T y)=tr(x^T c_(q^T) y).
Consequently the adjoint Laplacian is
  D=d_q c_(q^T)+c_(q^T) d_q=J_(qq^T+q^Tq),
with exact nonnegative energy
  tr(x^T D x)=tr((d_q x)^T d_q x)+tr((c_(q^T) x)^T c_(q^T) x).
Its actual native kernel is ker(d_q) inf ker(c_(q^T)).
No manifold differential forms, de Rham comparison, completed Hilbert space,
or full Hodge decomposition/isomorphism with homology is asserted.

PeirceBoundaryDynamics retains ad_P^3=ad_P as an endomorphism identity, the
unscaled corner recovery, conditional Leibniz conservation equivalences, and
weighted noncommutative commutators. The symmetric product centralizes the two
square-zero generators, not every ambient operator.

## Regressions and dependency poset

The support is nondiagonal and orthogonal. The forward and reverse arrows have
all entries nonzero, are genuinely noncommuting, and couple two internal modes.
They provide counterexamples to the Jordan-square, Lie-square and cross-swapped
mixed-difference claims, and to positivity for an independently signed reverse
arrow. The corrected global differential is both nonzero and square-zero.
These are full matrix calculations, not scalar representations of an operator.

PeirceBoundaryOrder constructs a finite native PartialOrder by inclusion of
explicit prerequisite sets. The differential and metric-adjoint stages are
incomparable prerequisites of the energy/kernel result. Composition identities
and the global differential are separate descendants of the operator layer.
This is a sufficient stage dependency specification, not the extracted full
declaration graph or a claim of minimal proof dependencies. The energy/kernel
identities themselves do not require q^2=0; nilpotence additionally makes the
construction a genuine differential complex.

## Verification: passed on exact sources

- PR: #260, stacked on #250 at the base identified above; no merge.
- Successful workflow: https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40693263918
- Kernel job: `122833252556`.
- Checked source head: `dc6d04d4a1e8f976962c9f8f2d5634b29573532d`.
- Checked PR merge snapshot: `3fc2cc61d2b5ac0fe3f6a68b2d11f40bec1b5d7e`.
  GitHub compare reports no file changes relative to the source head.
- Official Lean `4.34.1`, executable commit
  `5045d0056413266e57c625dcd7c365b10e377c52`.
- Unchanged Mathlib pin: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All **12 repository modules** in the selected import closure compiled from
  their actual source bytes under the shared serial build lock.
- Six new modules contain **80 named theorem/lemma declarations**: **78 public**
  and **two private proof lemmas**. The two reused owners contain another 34,
  so the checked eight-owner surface contains **114 named theorems/lemmas**.
- Native public `Lean.collectAxioms` inspection passed on **278 owned declarations**,
  including definitions, private helpers, and generated declarations. Every one
  of the 114 named theorems/lemmas occurs in the inspected set. This is not a
  count of 278 theorems. The exact axiom union is `propext`, `Classical.choice`,
  `Quot.sound`; no `sorryAx` or custom axiom. Unsafe/partial declarations are
  rejected by the checker.
- Every new module compiler log is empty: **zero errors and zero warnings**.
  The unchanged parent owners have **nine inherited linter warnings**: four
  unused simp arguments in LieJordanEndomorphisms, and four deprecated `if_pos`/
  `if_neg` uses plus one unused simp argument in PeirceLieJordanResolution.
- Static scanning of the six new source owners found no explicit proof holes,
  axioms, unsafe/partial declarations or native_decide. Their required headers
  are intact. Git whitespace checking passed.
- The semantic-vacuity lexical gate read all six selected files, with **zero
  errors and eight advisory warnings**. All eight were reviewed: five are
  definitional apply/readback lemmas, one evaluates crossTransport at the unit,
  and two specialize the differential to actual sign eigenspaces. None is an
  assumed conclusion or replacement of the operator carrier. No gate setting,
  suppression or exemption was added. This check is heuristic, not a semantic proof.

The artifact `real-graded-boundary-verification`, ID `12818595930`, contains
exact checked sources, the generated native declaration audit, compiler logs,
Lean version, source hashes, status and lexical report. Its downloaded ZIP
SHA-256 matches GitHub's published digest:

`6694a2c9d2bc65591c249717d5e0d345bb84705fd1b41807e8a9cd819d70a964`

All 12 extracted source hashes match the manifest. The supplementary local
exact-rational calculation also checked the complete 16x16 differential and
codifferential matrices and the counterexample entries; it is not proof authority.
The final evidence update changes this document only, leaving the checked Lean
sources and verification machinery unchanged.

### Exact checked source hashes

| Module | SHA-256 |
|---|---|
| `InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms` | `e448973da9b859295ed1a6539733a8cd6e775df2f1594d91a18e6262fd086488` |
| `InfoGeometry.Algebra.FiniteSpinAlgebra` | `5e253fd5adfe3b75df510d8319f7cc05f9cedf609edd8958279e895768b10e26` |
| `InfoGeometry.Algebra.IdempotentProjector` | `56eaf80ce2db517999a78643bf2cf8f45f669d99dcbbdd53c931e2bae69b038d` |
| `InfoGeometry.Algebra.PeirceLieJordanResolution` | `6e893a08f8d33322c13c9c68db038a6c0159086f1516bb535a48257aebc1aee7` |
| `InfoGeometry.OperatorAlgebra.LieJordanBoundaryComposition` | `e3c53bf60407cd7eb37dbaf1e82d3a9cd83cd09de1f40b99f2cdc8d8b7098e0f` |
| `InfoGeometry.Core.PeirceDecomposition` | `0ef61b4bcb868ad97ed6d6d832fae3de88e0d4d7b9f32e81fc69816e9f2ab813` |
| `InfoGeometry.Core.IdempotentCartan` | `774fcd4b531dbedd62fdf3ae21a5e56840ed83d55f9ed5a4b17607fb690aba82` |
| `InfoGeometry.OperatorAlgebra.PeirceGradedDifferential` | `22799852f3ea1a83f32bc59bee31e3a8e4d79e44cdaffb69eadaae191edd0729` |
| `InfoGeometry.OperatorAlgebra.PeirceBoundaryDynamics` | `e102cd9b4505b3195d50d204dbb742db07ea410b7c7869d56abaf2dadf8344de` |
| `InfoGeometry.OperatorAlgebra.PeirceBoundaryMetric` | `a83f365e9260c8f3d7190e2e8b1e78f14207eaa1a3cee9bf3898462d14ea7391` |
| `InfoGeometry.OperatorAlgebra.PeirceBoundaryWitness` | `cff9562c442802e3e1a3658dac057602b0711216bf96a166e9bd9153c64a3eb8` |
| `InfoGeometry.OperatorAlgebra.PeirceBoundaryOrder` | `f6341c115e8cb76661ac46046902bd3defddf099c7eedd0006ef03c64d4584b9` |

### Reproduction and boundaries

With the checked repository revision, the declared Lean toolchain and a Mathlib
checkout at the exact pin:

```sh
python3 tools/quality/check_peirce_boundaries.py \
  --mathlib-root /path/to/pinned-mathlib --output verification-boundary
```

There is no local Lean executable in the authoring container. The proof authority
reported here is the completed GitHub Actions kernel run and its inspected
artifact, not a local compile or an independent human/agent acceptance review.
Root toolchain, Lake manifest, dependency pins and other PR branches are unchanged.
This is not a full root Lake build or an all-green-CI claim: the unrelated Sorry
Gate and thesis/blueprint/docs workflows failed on the checked source commit.
No physics identification, completed operator space, global de Rham theorem,
full Hodge decomposition or homology comparison is asserted.
