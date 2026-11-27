# Real phase observable uncertainty: theorem contract

## Provenance and restoration scope

This change restores three proof owners from [PR #372](https://github.com/nickgou-nuke/info-geometry-lean/pull/372),
at its published head `fd4a9f929a99b17adaeb6f8a3d2aa78141285324`.
The PR was closed without a GitHub merge. Its
[closing comment](https://github.com/nickgou-nuke/info-geometry-lean/pull/372#issuecomment-7153014535)
reports integration into local main through `2b3ddd701`.
The three owners are absent from the audited published-main snapshot
`fe24e350b08fdea04f74c0748ef9fd9417c47529`; this focused restoration makes them available there.
The [earlier focused check](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44053076793)
is historical evidence for the source revision. Validation against the current base is recorded below.

| Restored path | Main declarations |
|---|---|
| `lean/InfoGeometry/Krein/InternalPhaseGram.lean` | `phase_pair_neg_swap`, `phase_pair_self_zero`, `inner_sq_add_phase_inner_sq_le` |
| `lean/InfoGeometry/Krein/PhaseLinearObservableCommutator.lean` | `centeredVector`, `twice_centered_phase_pair_eq_commutator`, `commutator_linearCombinations` |
| `lean/InfoGeometry/Canonical/PhaseObservableUncertainty.lean` | `centered_robertson_schrodinger`, `centered_robertson`, `centered_norm_sq_eq_second_moment_sub_mean_sq` |

The existing `Canonical/OperatorialUncertainty.lean` forwards its two public Gram
lemmas to `InternalPhaseGram`, preserving their signatures and downstream channel
theorems. It imports `PhaseObservableUncertainty`, exposing the new result through
the existing canonical umbrella without adding a second proof of the Gram bound.

## Carrier, phase, and adjoint

The carrier is `DoubledSpace E = WithLp 2 (E × E)` over `ℝ`, with the positive Hilbert product
$\langle(x,\xi),(y,\eta)\rangle=\langle x,y\rangle+\langle\xi,\eta\rangle$.
`InternalPhaseGram` requires a real inner-product space; the observable owners also require completeness.
The existing `complex_i` is the real continuous linear map
$I_{op}(x,\xi)=(-\xi,x)$, built as `modular_j.comp spectral_epsilon`.
`InfoGeometry.Krein.complex_i_sq`, supplied by `DoubledSpace.lean`, establishes
$I_{op}^{2}=-\mathrm{id}$, and `complex_i_norm` establishes $\|I_{op}u\|=\|u\|$.
The restored owners introduce no complex scalar unit.

All norms, covariances, and `IsSelfAdjoint` hypotheses use the positive Hilbert structure.
The existing Krein adjoint is separately `doubledKreinAdjoint A = ε ∘ A† ∘ ε`.
Krein self-adjointness alone does not discharge a Hilbert self-adjointness hypothesis.

## Gram bound and ordered commutator

For arbitrary doubled vectors, the first owner proves the two-component Bessel bound

$$
\langle u,v\rangle^2+\langle I_{op}u,v\rangle^2
\leq\|u\|^2\|v\|^2.
$$

Let `A B : DoubledEnd E`, so both are bounded real continuous linear endomorphisms.
The commutator bridge assumes `IsSelfAdjoint A`, `IsSelfAdjoint B`,
`A.comp Iop = Iop.comp A`, and `B.comp Iop = Iop.comp B`.
Each observable preserves the phase; the two observables may fail to commute with each other.
For arbitrary real shifts $a,b$, set $u=A\psi-a\psi$, $v=B\psi-b\psi$.
With the ordered commutator $[A,B]=A\circ B-B\circ A$, the bridge proves

$$
2\langle I_{op}u,v\rangle=\langle I_{op}\psi,[A,B]\psi\rangle.
$$

`centered_robertson_schrodinger` combines these two proved results:

$$
\langle u,v\rangle^2+\frac14\langle I_{op}\psi,[A,B]\psi\rangle^2
\leq\|u\|^2\|v\|^2.
$$

`centered_robertson` drops the nonnegative covariance square.
Neither bound assumes state normalization, a canonical commutation relation, or an uncertainty inequality.

## Normalization, variance, and changes of observable coordinates

For $\langle\psi,\psi\rangle=1$ and the actual mean $a=\langle\psi,A\psi\rangle$,
`centered_norm_sq_eq_second_moment_sub_mean_sq` proves
$\|A\psi-a\psi\|^2=\langle\psi,A^2\psi\rangle-a^2$.
With the corresponding mean for $B$, these are variances and $\langle u,v\rangle$ is covariance.
For arbitrary shifts or an unnormalized state, the bounds retain their stated fluctuation-norm meaning.

For finite observable families and real coefficients, `commutator_linearCombinations` proves

$$
\left[\sum_i r_i A_i,\sum_j s_j B_j\right]
=\sum_i\sum_j r_i s_j(A_i\circ B_j-B_j\circ A_i).
$$

This algebraic identity retains both operator orders and requires no self-adjointness or mutual commutativity.

## Validation of this restoration

Run from the repository root with the pinned Mathlib checkout at `../mathlib`:

```sh
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root ../mathlib --output /tmp/real-phase-uncertainty \
  --target InfoGeometry.Krein.InternalPhaseGram \
  --target InfoGeometry.Krein.PhaseLinearObservableCommutator \
  --target InfoGeometry.Canonical.PhaseObservableUncertainty
python3 tools/quality/semantic_vacuity_gate.py \
  lean/InfoGeometry/Krein/InternalPhaseGram.lean \
  lean/InfoGeometry/Krein/PhaseLinearObservableCommutator.lean \
  lean/InfoGeometry/Canonical/PhaseObservableUncertainty.lean --fail-on warning
git diff --check
```

Fresh local validation on 2026-11-26 used the three restored owners on base
`fe24e350b08fdea04f74c0748ef9fd9417c47529`, Lean `4.34.1` (compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`), and the unchanged Mathlib pin
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

- All 11 modules in the exact repository source closure compiled.
- All 44 declarations owned by the selected modules were audited: 16 in
  `InternalPhaseGram`, 16 in `PhaseLinearObservableCommutator`, and 12 in
  `PhaseObservableUncertainty`.
- Their transitive axiom dependencies were limited to `propext`,
  `Classical.choice`, and `Quot.sound`.
- The staged proof gate passed. Strict placeholder and semantic-vacuity scans
  passed for all four changed Lean files, including the existing forwarding owner.
- Each restored owner produced zero warnings. Existing dependencies produced
  five warnings in total; this is not a warning-free closure claim.

The [focused workflow](../.github/workflows/phase-observable-uncertainty.yml)
repeats this check on the actual workflow revision and retains the report,
source hashes, generated declaration audit, and logs as
`phase-observable-uncertainty-evidence`.

The changed `Canonical/OperatorialUncertainty.lean` integration is outside that
focused certificate. Its existing dependency chain imports the external
`Architect` package, which the copied-source checker does not support. The
root Lake configuration also references the absent `external_refs/atlas-lean`
and `external_refs/homotopy-hypothesis-lean4` path packages. The native four-target build and the unmodified pre-push gate were both run;
both exited with code 1 at the missing `HomotopyHypothesis` package, before
compiling the changed canonical integration. The pre-push gate's incremental
axiom/debt, semantic-content, and tracked-scope scans passed for all four
changed Lean files. The PR remains a draft while the native integration gate
is blocked. The focused success does not assert that the wider gate passed.
No dependency pins, proof gates, or verifier implementations are changed.

## Next analytic connection

A concrete real Clifford continuous-wavelet theorem still needs a constructed analysis map,
its positive-norm admissibility/tightness identity, and derivative and integration-by-parts results
on an explicit domain with finite moments. This restoration provides the bounded-observable core;
it does not claim that continuous-wavelet construction or an unbounded position/momentum realization.
