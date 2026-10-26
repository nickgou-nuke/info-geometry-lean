# Sulfur-37 configuration mixing: theorem contract

Source: L. Zago et al., *Mixing between single-particle and intruder
configurations towards the N=20 Island of Inversion: lifetime measurements
in 37S*, EPJ Web of Conferences 378, 01050 (2026),
https://doi.org/10.1051/epjconf/202637801050, pp. 1-4.
The supplied PDF is the intake source. It reports preliminary analysis,
not final new lifetimes, reduced transition strengths, or a mixing fraction.
PDF SHA-256: `c4d4ceec60f2d90a11ffdcf67f6fcbdcff24d9b3d38d7a6d16b0d7de589b4b7c`.

## Physical scope

Configuration mixing is restricted to a fixed angular-momentum and spatial-
parity sector. The 2023-keV 7/2-minus to 646-keV 3/2-minus E2 transition
connects different sectors; those two levels are not the mixing pair.
The real two-channel final-state model below is an explicit truncation,
not a derivation of the nuclear shell model or an experimental fit.
The initial and final coordinate spaces of a transition matrix may represent
different spin sectors, despite sharing the same mathematical carrier.

The reported 134(3) ps for the 646-keV level is a HALF-LIFE (p. 3),
so its mean lifetime is T_half / log(2). The 1992-keV gamma line from
2638 to 646 keV is distinct from the 1992-keV intruder level (Fig. 1).
No experimental uncertainty is converted into an exact physical premise.

## Existing owners and source-confirmed boundary

At base commit 2d3a6ed286fde7098d152b83c9c75580b98865d0:

* `Physics/SolovievFiniteSecularEigenproblem.lean` defines `Carrier = Fin 2 → ℝ`,
  the symmetric `blockHamiltonian eQ eP v`, and
  `block_eigenpair_iff`: its eigenpair equation is precisely the two coordinate
  linear equations. The determinant, secular roots, and eigenvector existence
  already have owners; they are not reimplemented here.
* `Physics/SolovievTransitionStrength.lean` defines
  `amplitude O initial final = dotProduct final (O.mulVec initial)` and
  `strength O initial final = amplitude O initial final ^ 2`.
  `amplitude_entries` exposes its four matrix entries.
* `Topology/KatzSarnakRandomMatrixBridge.lean` defines
  `rotationMatrix c s = !![c, -s; s, c]` and proves transpose/inverse and
  determinant laws under `c^2+s^2=1`. Only these finite algebraic declarations
  are reused; no arithmetic/random-matrix interpretation is imported as fact.
* `proofs/SarkarTwoLevelIsospinMixing.lean` contains rational energy/gap
  identities but not the operator transition-strength inference developed here.
* `Nuclear/NuclearGammaSpectroscopy.lean` covers inertia, pairing, and chiral
  degeneracy. `OperatorAlgebra/TKKHamiltonian.lean` has simplified lifetime
  readouts without branching and radiative constants; those definitions do
  not constitute the physical inference needed here.

Search: GitHub queries and local source searches for configuration/intruder,
mixing, amplitude/strength, branching, lifetime, rotation, and direct consumers;
`context_preflight.py` also scanned executable, entrypoint, graph, and external
surfaces. No generated declaration graph/index is present in this checkout.
These are bounded source observations, not repository-wide absence claims.

## Ordered mathematical claims

1. Existing rotation and block carriers → an explicit rotated Hamiltonian
   and its two normalized-coordinate eigenvectors.
2. Existing amplitude → mixed-final-state amplitude and interference identity.
3. Orthogonal final-state mixing → conservation of summed strengths.
4. Zero normal amplitude plus nonzero intruder amplitude → recovery of the
   squared intruder coefficient from a strength ratio.
5. Explicit operator families → non-identifiability when unmixed matrix
   elements are unknown, even if both final-state strengths are supplied.
6. Finite nonnegative decay-channel rates → total rate, mean lifetime,
   half-life, normalized branch fractions, and recovery of a partial rate.
7. An EXPLICIT pure-E2 rate-law hypothesis → recovery of reduced B(E2)
   with its positive energy-dependent radiative constant. Real matrix strength
   is divided by `2J_initial+1` before applying that physical hypothesis.
8. Two explicit E2 rate laws plus the amplitude assumptions → intruder
   weight from the ratio of energy-corrected radiative partial rates.

Gamma fractions here use all de-excitation in the denominator. A transition
branch that includes internal conversion requires the factor `1+alpha`;
gamma-only relative intensities are not automatically either branch fraction.
Different photon energies require separate fifth-power corrections before
using the strength sum rule. Vanishing normal amplitude is a model assumption,
not a generic E2 selection rule and not a conclusion of the paper.
Lifetime formulas have physical meaning only at positive total rate. Lean's
totalized division gives zero at zero rate; this is not an infinite-lifetime claim.

## Open boundary

No complex-phase inference, shell-model diagonalization, AGATA/SPIDER detector
response, RDDS/DSAM lineshape analysis, feeding correction, posterior fit,
measured intruder fraction, torsion, or exceptional-algebra identification.
The finite operator and rate-law consequences are the intended theorem scope.

## Validation

Status: `[kernel_verified]` finite algebra and `[bucket_2_conditional]`
physical rate-law consequences; `[accepted_limited_scope]` semantic review.

* Lean 4.34.1, mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`,
  exactly matching the repository pins.
* A separate Lake project imports the actual checkout's source directory and
  the exact pinned mathlib checkout. It does not copy or rewrite the Lean owners.
  `flock /tmp/info-geometry-build.lock lake build
  InfoGeometry.Physics.NuclearDecayInference` passed (8929 jobs), including
  both new modules and their repository-owned imports.
* All 23 new theorems inspected with `#print axioms`; only `propext`,
  `Classical.choice`, and `Quot.sound` occur. No placeholders or custom axioms.
* `git diff --cached --check` and `proof_proxy_staged_gate.py` passed.
* Vacuity linter: decay module 0; configuration module 0.25 solely for its
  heuristic `nlinarith` flag. Independent review resolved this flag: the
  proofs establish polynomial identities and nonnegative-square bounds from
  satisfiable normalization premises, with no circular theorem assumptions.
* No warnings in the new files. One inherited deprecated-import warning in
  `Topology/KatzSarnakRandomMatrixBridge.lean` remains unchanged.
* Separate semantic audit and acceptance roles reviewed the source, paper,
  proof boundary, and build/axiom evidence.

The repository-root command
`python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock
InfoGeometry.Physics.NuclearDecayInference` was also attempted. It stopped
before checking the target because `external_refs/atlas-lean` is absent in
this checkout. This is NOT a successful full-repository build.

The isolated verification project's configuration is:

```toml
name = "sulfurmixingcheck"
[[require]]
name = "mathlib"
path = ".lake/packages/mathlib"
[[lean_lib]]
name = "InfoGeometry"
srcDir = "../mixing-repo/lean"
```

In the sandbox the stock Lean executable additionally required a `readlink`
compatibility shim mapping its own `/proc/<pid>/exe` to `/proc/self/exe`.
No kernel, toolchain source, repository dependency pins, or original owners
were modified.

Verified Lean source SHA-256:

* `NuclearConfigurationMixing.lean`:
  `e4242ad08712372f0bae87c2e0d5476de3229712c6a6aa441c3971e26cc7c7b8`
* `NuclearDecayInference.lean`:
  `e4c1c1a8b9dbb9a955ec863da121bc568b58144a942a5ccd949aa25e329779e7`
