# Central Lie defects and Rindler torsion

Source: user intake of 2026-10-26, proposing that a scalar matrix Lie defect
should be connected to `Geometry/RindlerCartanFrame.lean` and interpreted as
torsion of accelerated nucleons. Base inspected: `2d3a6ed286fde7098d152b83c9c75580b98865d0`.

## Atomic claims and scope

- `[conditional]` For a real matrix-valued linear lift, a scalar bracket
  defect equals minus the normalized trace evaluated on the source bracket.
- `[locally_provable]` This is the native low-degree CE differential with
  trivial scalar coefficients; its next differential is zero.
- `[locally_provable]` Subtracting the normalized trace gives a Lie
  homomorphism when the original defect is scalar.
- `[source_backed]` The existing Rindler Lorentz connection is flat and
  torsion-free, even for nonzero acceleration.
- `[open_debt]` Neither this algebraic splitting nor a discrete sign
  multiplier implies spacetime torsion or nuclear dynamics.

The user names `scalar_defect_is_coboundary`, `tracePotential`,
`traceCoboundary`, and `observableDerivative` were not located in the checked
`lean/` and `proofs/` source. The supplied `FunctorialCocycleCalculus.lean`
link concerns group cohomology; it does not establish these Lie declarations.

## Owner contract

`RindlerCartanFrame` owns `Tangent := ℝ × ℝ`, `area`,
`dCoframeTime`, `connectionForm a v = (a * v.1) • J1`, and
`metricMatrix = -Eplus`. Its statements include
`cartan_time_torsion_zero : dCoframeTime a x + timeConnectionTerm a = 0`
and `rindler_connection_flat : curvatureTX a p = 0`.
`RindlerLapseCalculus` owns `lapse a x = 1 + a*x` and its derivative.
`Cl11Matrix` owns `Eminus`, `Eplus`, and `J1`.
`TorsionStructure.cartanTorsionCoeff` owns the finite coefficient Cartan
formula; it uses an explicit wedge over two direction slots.
`DerivationDifferentialForms` already uses Mathlib's native CE maps. Reuse
those Mathlib maps directly for trivial scalar coefficients, without imposing
its separate faithful derivation-action carrier on an arbitrary Lie algebra.

New algebraic carrier: `L →ₗ[ℝ] Matrix n n ℝ`, with finite nonempty `n`.
The defect is `[A x,A y] - A [x,y]`. The scalar cochain takes values in
`TrivialLieModule ℝ L ℝ`; the sign is `dθ(x,y) = -θ([x,y])`.
The target Lie structure is Mathlib's associative commutator instance.

New geometric carrier: actual two-slot, vector-valued Cartan expression on
the existing coordinate Rindler coframe `e(v) = (N*v.t,v.x)`.
The explicit Clifford map is `γ(v) = v.0*Eminus + v.1*Eplus`.
For `q(v) = (a+kt)*v.t + kx*v.x`, the spin lift is
`B(v) = -(q(v)/2)*J1 + μ(v)*I`. Prove, rather than assume,
`[B(v),γ(w)] = γ((q(v)*J1) w)`.
This is the concrete spin-to-vector compatibility map that permits scalar
invisibility to descend to Cartan torsion. It is not an identification of
an arbitrary four-dimensional spin model with this two-dimensional chart.
The spin encoding is injective. The implementation also checks
`Tr(B(v)) = 2*μ(v)` and that subtracting `Tr(B(v))/2` times the identity
returns exactly the lift with `μ = 0`.

Causal dependency order:
trace cyclicity → scalar defect coefficient → native CE coboundary →
trace-free Lie lift; separately, Clifford commutator compatibility →
spin/vector Cartan compatibility → Rindler contorsion coefficients.
No dependency from a group multiplier or acceleration to contorsion is asserted.

Expected coordinate result is
`T(v,w) = (kt, -N*kx) * area(v,w)`.
On `N ≠ 0`, this vanishes identically iff `kt = 0` and `kx = 0`.
The domain restriction is essential for interpreting `e` as a coframe.

## Verification record

Disposition: `[kernel_verified]` for the two source modules in an isolated
Lake harness; `[accepted_limited_scope]` for the finite/coordinate claims
above. Repository-root package validation remains infrastructure-blocked.

- Independent semantic audit and independent final QA passed.
- Lean `4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, exactly the repository pin.
- `lake build InfoGeometry.Algebra.MatrixLieCentralDefect
  InfoGeometry.Geometry.RindlerSpinTorsion` passed in the isolated harness
  (8953 jobs), importing the actual repository source files and dependencies.
- Independent `#check` and `#print axioms` passed for all 23 new theorems and
  `normalizedLieHom`. Every audited declaration uses exactly the standard
  foundations `[propext, Classical.choice, Quot.sound]`; no custom or sorry axioms.
- No new-source warnings; 25 pre-existing dependency warnings were replayed.
- Both vacuity lint scores were zero with no findings. Placeholder scan,
  `proof_proxy_staged_gate.py`, and `git diff --cached --check` passed.
- The prescribed repository-root locked build exited before compilation:
  `Atlas: package directory not found: external_refs/atlas-lean`.
  No whole-repository build or test-suite success is claimed.
- No toolchain, manifest, or dependency source/pin was changed.

The harness has a local path requirement for the exact pinned Mathlib checkout
and an `InfoGeometry` library with `srcDir` pointing to the repository's `lean`
directory. All build and probe commands were serialized under
`/tmp/info-geometry-build.lock`. The execution environment required a runtime
path shim mapping its own `/proc/<pid>/exe` lookup to `/proc/self/exe`; it does
not modify Lean, proof elaboration, or the kernel.

Source SHA-256:

- `Algebra/MatrixLieCentralDefect.lean`:
  `6761c218471c912d26b07ff7aebd68fc62d0df9619742407ec763f8546166a0b`
- `Geometry/RindlerSpinTorsion.lean`:
  `76999f77612460d022d873ec8773dcffc1804773640f53f439cb1345d85ca00a`
