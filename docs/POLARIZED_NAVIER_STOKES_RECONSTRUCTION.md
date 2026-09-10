# Polarized shear, rotation, and the fluid proof boundary

This reconstruction follows the accessible Lean owners and the user's stated
association stream. The linked Google AI Studio prompt was not readable in this
session; this document does not claim to reproduce its transcript or its order
of associations. “Archetype” denotes an organizing structural role here, not a
mathematical axiom or an assertion about Jung's historical theory.

The source baseline is `nickgou-nuke/info-geometry-lean` at
`ec7c289661eb1cd45b2afcd886847ca992318de5`. The external comparison is
`openai/NavierStokesAndEuler` at `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`.
Their Lean toolchains differ: the owned repository specifies v4.28.1, with
Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`; the external repository
specifies v4.34.0-rc2. This change does not alter either dependency pin.

The canonical mathematical chain is:

| Structural role | Precise carrier or operation | Source / extension |
|---|---|---|
| Two regularizations | Moore–Penrose range projector `P = a b` and readout `Q = a c` | Existing `Canonical/MoorePenrose`, `Canonical/Singular` |
| Mismatch | `N = P Q - Q P` | Existing `EinsteinAnomaly` |
| Directed transfer | `P N = N`, `N P = 0`, hence `P N (1-P) = N` | New `SquareZeroStrainRotation` |
| Nilpotent shear | `P Q = Q`, `N = Q (1-P)`, `N² = 0` | New algebraic core |
| Adjoint pairing | `S = (N+N*)/2`, `W = (N-N*)/2` | Existing `strainRate`, `vorticity` |
| Split Clifford relation | `S² = -W²`, `S W = -W S` | New core and `AnomalyStrainRotation` |
| Real two-sheet frame | Native `CliffordAlgebra q11`, its matrix representation, and existing Peirce projectors | Existing `Clifford/Cl11Matrix`, `KreinDoubledCartanPeirceBridge` |
| Regime discriminant | `L = s J1 + w Eminus`, `L² = (s²-w²) I` | New `PolarizedShearSpinFrame` |
| Controlled finite evolution | Positive adapted energy for `abs s < w`; damping gives `E' = -2 nu E` | New frame and evolution modules |
| Actual fluid polarization | Transverse curl symbol and moving orthonormal frames | External OpenAI source; further adapter required |

The algebraic core is nonvacuous. With real matrices

```text
A = [[1,1],[0,0]], B_MP = [[1/2,0],[1/2,0]], B_D = A,
```

the actual repository Moore–Penrose and index-one Drazin predicates hold.
The anomaly is `N = [[0,1],[0,0]]`, which is nonzero. Its normalized symmetric
and skew parts satisfy the split Clifford generator laws. The spectral
projector `Q = A` is not self-adjoint. Imposing that additional property would
force this anomaly to vanish, as the new core proves. Thus extracting the
skew part preserves a meaningful component, while asserting that the entire
anomaly is already skew discards this nonzero example.

The old `backwardWave` has a separate defect: it applies `id-epsilon` after
embedding into the positive sheet. It consequently vanishes for every input,
and its `twinWaveHelicity` readout is zero. The new
`NavierStokesPolarizedTransfers` records that diagnosis and supplies faithful
mixed-corner transfers on the existing `DoubledSpace E`:

```text
upward u (x,y)   = (u y,0)
downward v (x,y) = (0,v x)
```

Each directed transfer squares to zero. Their opposite-direction compositions
retain `u v` and `v u` on the respective sheets. The paired generator has
diagonal square `diag(-u v,-v u)`. These are operator composition theorems;
they do not identify the old proxy with the physical helicity integral.

The finite frame gives an exact stability statement with explicit hypotheses.
For constant real `s,w,nu`, set

```text
L = [[0,s+w],[s-w,0]],
E(x) = (w-s) x_0² + (w+s) x_1²,
x' = L x - nu x.
```

If `abs s < w`, the energy controls both coordinates:

```text
(w-abs s)(x_0²+x_1²) <= E(x) <= (w+abs s)(x_0²+x_1²).
```

The derivative identity is valid for every supplied differentiable trajectory
satisfying that ODE. The evolution module derives the integrating-factor law

```text
E(x(t)) = exp(-2 nu (t-t0)) E(x(t0)),
```

and, when `nu >= 0` and `t >= t0`, a coordinate bound with factor
`(w+abs s)/(w-abs s)`. The theorem quantifies over a supplied trajectory; it
does not assert existence or continuation of a fluid solution. A changing
`s` or `w` adds derivatives of the energy weights, so this bound must not be
applied unchanged to time-dependent parameters. Its coercivity degenerates at
`w=abs s`. No theorem in this change makes a flow cross into the elliptic
regime or maintains a uniform gap for the fluid equation.

`PolarizedShearSpinSolution` additionally constructs explicit globally defined
finite trajectories for every initial vector using
`exp(-nu*t) (cos(k*t) I + sin(k*t)/k L)`, where `k=sqrt(w²-s²)`.
The positive-frequency existence lemma and `exists_bounded_solution` remove
the supplied-global-trajectory premise for this finite constant-coefficient
model. They do not supply a corresponding trajectory for the fluid PDE.

The nonzero anomaly example itself has `s=w=1/2`, on the nilpotent boundary
where the positive-energy hypothesis fails. The stable family is a related
parameter family; the current theorems do not turn that anomaly into an
elliptic generator. Scalar damping is an independent parameter, not a
derived fluid viscosity term.

A frame conjugation alone cannot change a square-plus-one generator into a
square-minus-one generator: algebra isomorphisms preserve squares. The actual
discriminant or the evolution law must change. Likewise, two real coordinate
sheets, two helicity eigenspaces, particle-hole conjugation, and a spacetime
spin double cover are distinct constructions until their intertwining maps
are supplied. The word “spin” in the new finite module refers to its Clifford
rotation generator; it makes no spin-quantization claim.

The OpenAI source offers concrete subsequent interfaces. In
[`NavierStokes/CurlGeometry.lean`](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/NavierStokes/CurlGeometry.lean),
`tangent_double_cross` and `curl_symbol_transverse` imply that for a real unit
normal `n`, the operator `J_n a = n cross a` has square `-I` on the transverse
plane. After complexification, `H_n = i J_n` has square `I`, with helicity
projectors `(I+H_n)/2` and `(I-H_n)/2`. This is the exact proposed Fourier
polarization adapter; it has not been added as an incompatible import here.
The factor `i` comes from complexification, not from converting a real
hyperbolic generator by conjugation.

[`Euler/PacketMovingFrame.lean`](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/Euler/PacketMovingFrame.lean)
contains actual moving-frame orthonormality and skew frame-rate results.
Its `normalizedFrame_skew` identifies the angular-velocity matrix from the
normalized ray and velocity ODEs; `Euler/PacketMovingRay.lean` derives the
corresponding moving-coordinate equation. `Euler/ParentPacketStrainEvolution.lean`
contains `Parent.strain_time` and `Parent.strain_within`, with the actual law
`M' = -M composed M - H`. Those differential statements are the appropriate
next targets for an adapter.

The external terminal declarations
`NavierStokes.Comparator.navier_stokes_breakdown_R3` and
`NavierStokes.Comparator.navier_stokes_breakdown_periodic`, in
[`NavierStokes/ComparatorSolution.lean`](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/NavierStokes/ComparatorSolution.lean),
assert the forced breakdown alternatives C/D for every positive viscosity.
`Euler.exists_compact_smooth_euler_singularity`, in `Euler/Solution.lean`,
asserts the unforced Euler conclusion. These are implemented terminal proofs,
not merely the propositions introduced in `ProblemStatement.lean`.
The external tree contains 2,486 Lean files. Its metadata reports only the
three standard axioms, and its two independent Comparator challenge files
contain four intentional `sorry` reference placeholders; those reference
files are not imported by the terminal proofs. This session inspected source
interfaces but did not rebuild or independently certify that entire proof
development.

The owned `Cl11HestenesKreinTwoSheetBridge` and `Cl11TwoSheetPeirceCorners`
already transport projectors, sheet exchange, and corner multiplication
through the categorical stage system. An algebraic colimit does not by itself
supply a uniform coercive norm, nonlinear evolution, or a compatible fluid
differential operator. Those constructions and estimates remain required for
a continuum conclusion. The inspected Aharonov–Bohm and vortex modules supply
finite phase/winding identities and witness interfaces; they do not close that
fluid estimate or prove that a Navier–Stokes singularity becomes a vortex.

The complete owned repository tree was inventoried. Topic-selected source
files and their relevant imports were fetched and searched locally because the
connected code-search index for the owned repository returned no matches even
for known declarations. The search
record distinguishes source inspection from kernel verification; no claim is
made that every proof body in the repository was audited.

The seven new owner modules compile without warnings using native Lean
4.28.0 and the pinned Mathlib sources/cache. The source dependency closure,
including the axiom diagnostic, contains 63 modules. All 60 new theorem axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`; none
contains `sorryAx`. The repository's staged proof-proxy gate and exact SymPy
witness pass. This is a narrow check, not a repository-wide build or a check
under the repository's declared v4.28.1 compiler, which rejected the pinned
cache's v4.28.0 olean headers. The accompanying draft pull request records the
check procedure and the pending declared-toolchain gate. `proofs/PolarizedShearSpinAudit.lean` checks axiom dependencies of
the new theorem surface. Its `.sp` companion is an exact symbolic witness,
not a substitute for Lean elaboration and kernel checking.
