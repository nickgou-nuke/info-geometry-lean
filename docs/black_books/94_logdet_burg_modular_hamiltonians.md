# Log-Det Potentials, Burg Divergence, and Modular Hamiltonians

This chapter records the finite SPD owner lane now attached to the canonical
surface, together with the operator/modular lift map.

## 0. Merge-Safe Abstract

Starting from the scalar convex kernel `f(λ) = λ - log λ - 1`, the Burg/Stein
log-det divergence on `S_{++}^n` is obtained by spectral calculus on the
relative spectrum of `Q⁻¹P`. This divergence is congruence-invariant and
spectrally reducible, and its second-order expansion induces the same local
Riemannian metric as affine-invariant geometry on the SPD cone, but it is not
the affine-invariant geodesic distance itself. In the noncommutative lift, the
finite-dimensional density-ratio intuition is replaced by the relative modular
operator (the noncommutative Radon-Nikodym object), expectations are realized
as state/weight pairings (e.g. natural-cone vector expectation in standard
form), and the classical chain rule is replaced by the Connes cocycle identity.
In finite-dimensional commuting lanes, Araki relative entropy collapses to the
usual density-matrix formula.

## I. SPD Burg/Stein Owner Lane

New owner anchors:

- `REPO_THEOREM`
  [BurgStein.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Jordan/BurgStein.lean)
  - `burgKernel`
  - `burgKernel_nonneg`
  - `steinLoss`
  - `steinLoss_self`
  - `steinLoss_eq_trace_add_barrier_diff_sub_dim`

Definition now present on `SPD`:
`steinLoss(X,Y) = tr(Y⁻¹X) - log det(Y⁻¹X) - n`.

The scalar convex atom is also explicit:
`burgKernel(λ) = λ - log λ - 1`, with nonnegativity on `λ > 0`.

Spectral normal form for the SPD relative spectrum (`λᵢ = eig(Q⁻¹P)`):
`D_Stein(P|Q) = tr(PQ⁻¹) - log det(PQ⁻¹) - n = Σᵢ (λᵢ - log λᵢ - 1)`.

Precision guardrail on geometry:

- Burg/Stein is congruence-invariant and spectrally reducible.
- Burg/Stein is not the AIRM geodesic distance.
- The AIRM geodesic distance is `||log(Q⁻¹ᐟ² P Q⁻¹ᐟ²)||_F`.
- The bridge to AIRM is local/Hessian: same second-order metric
  `½ tr(dP P⁻¹ dP P⁻¹)`.

## II. Canonical Facade Integration

- `REPO_THEOREM`
  [Canonical/LogDet.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/LogDet.lean)
  now exports the new Burg/Stein owners alongside existing log-det owners.

This keeps the SPD log-det lane and the existing determinant/log-volume lane on
the same canonical import surface.

## III. Modular Lift Anchors

The noncommutative lift remains on these owner surfaces:

- `REPO_THEOREM`
  [RelativeModularOperator.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean)
- `REPO_THEOREM`
  [RelativeModularHamiltonian.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean)
- `REPO_THEOREM`
  [RNDeterminantConnesChainBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean)
- `INTERFACE_READY`
  [PedersenTakesakiRNInterface.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/PedersenTakesakiRNInterface.lean)

Standard-form hypotheses used by the dictionary below:

- normal faithful states (or weights) in standard form,
- unique natural-cone vector representatives for those states,
- relative Tomita operator whose polar decomposition yields the relative
  modular operator `Δ`.

## IV. The "First Quantization" Dictionary

To safely map classical information geometry into operator-algebra lanes, the
direction is strict: log-det does not generalize upward into Type III; it is
the abelian shadow of modular theory.

Canonical Type III guardrail:

- In Type III, only `Δ` and `log Δ` are canonical.
- Determinant/trace scalarizations are representation-dependent shadows.

The corrected dictionary is:

- classical density-ratio intuition `p/q` -> relative modular operator
  `Δ_{ψ|φ}` (the noncommutative Radon-Nikodym object; primary object),
- surprisal `-log(p/q)` -> modular Hamiltonian `K_{ψ|φ} = -log Δ_{ψ|φ}`
  (derived via functional calculus),
- expectation `∫ p(·)` -> state/weight pairing (GNS; natural-cone language
  only after choosing a standard-form representation),
- chain rule -> Connes cocycle identity (multiplicative, time-parameterized);
  additive structure is recovered from logarithmic generators where defined.

This keeps cocycle and generator lanes distinct and prevents finite
trace/determinant formulas from being treated as Type III roots.

## V. Three-Tier Scalarization Hierarchy

1. Type III root lane: no trace and no determinant; geometry is carried by `Δ`
   and `-log Δ`.
2. Semifinite/Type II lane: with a faithful normal semifinite trace `τ`,
   scalarization appears as `τ(log Δ)`.
3. Classical/finite abelian shadow: commuting spectral collapse recovers
   log-det potentials such as Burg/Stein.

## VI. Δ-First Rule

Interpretation remains ordered:

1. multiplicative owner (`Δ`/cocycles),
2. additive generator (`-log Δ` lane),
3. scalar shadows (trace/log-det/Burg/entropy readouts).

## VII. Commuting Sanity Check

Commuting collapse closes the classical-to-modular loop explicitly:

- SPD lane: if `P` and `Q` commute, spectral calculus reduces Burg/Stein to
  `Σ f(λᵢ)` with `f(λ)=λ-log λ-1`.
- Operator lane: in finite-dimensional commuting lanes, Araki relative entropy
  reduces to the usual density-matrix expression.

## VIII. Support Handling: Canonical vs Repo-Translated

Canonical modular-theory statement (Type III root):

- support is handled spectrally, via `s(Δ) = 1_(0,∞)(Δ)`,
- `K = -log Δ` is a support-restricted functional-calculus object on
  `s(Δ)H`,
- `log Δ` is defined spectrally (not via pseudo-inverse inversion).

Repo-translated doubled-carrier statement (owner architecture):

- the support/defect split is routed through the owned Drazin/Moore-Penrose
  projector package on doubled real carriers,
- Drazin projector lane (`P_D = Δ * Δᴰ`) realizes the spectral regular sector,
- Moore-Penrose projector lane (`P_MP = Δ⁺ * Δ`) realizes the metric/self-adjoint
  support sector,
- the metric/spectral mismatch and anomaly lanes are explicit and theorem-bearing
  in:
  [MoorePenrose.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/MoorePenrose.lean),
  [CertifiedInverseKernel.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean),
  [DrazinKreinCompatibility.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinKreinCompatibility.lean).

Operational invariant:

- the projectors do not define `log`; they realize support restriction for the
  spectral logarithm in the doubled algebra,
- projector mismatch (`P_D - P_MP`) tracks spectral-vs-metric support divergence,
- commutator anomaly (`[P_D, P_MP]`) is the chiral anomaly lane.

Guardrail:

- this repo lane is a conservative translation layer and must not be read as
  replacing the canonical Type III support-projection ontology.

## IX. Boundary (Not Yet Owner-Complete)

- spectral-eigenvalue normal form theorem
  `steinLoss = Σ_i (λ_i - log λ_i - 1)` as an owner theorem surface;
- explicit Gaussian KL covariance decomposition theorem on the SPD owner lane;
- full affiliated-operator Pedersen-Takesaki/Vaes existence/uniqueness owner
  stack in Type III generality.

So the finite SPD Burg/Stein lane is now owner-compiled, while the full
infinite-dimensional spectral/operator endpoints remain on the active frontier.
