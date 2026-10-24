# Native para-Kähler / metriplectic completion contract

## Scope and conventions

Work on the existing algebraic phase space `E × Module.Dual ℝ E`, and its
existing five-dimensional specialization `Clifford55.V55`. This task is not a
construction of a global supermanifold, connection holonomy or physical CPT.

Owners inspected:
- `NeutralPhaseSpaceCore`: `B(X,Y)=ξ(y)+η(x)`, `K(x,ξ)=(x,-ξ)`,
  `ω(X,Y)=η(x)-ξ(y)`. `canonicalNeutralBilin_nondegenerate` assumes
  `Module.Projective ℝ E`.
- `PhaseSpaceGeneralizedMetric`: `MetricDatum.gFlat : E ≃ₗ[ℝ] E*`, symmetric;
  the zero-B-field polarization is `S(x,ξ)=(gFlat.symm ξ,gFlat x)`;
  its generalized metric is `H(X,Y)=B(X,SY)`.
- `Cl55NeutralHyperbolicIsometry.neutralToV55` maps `(x,ξ)` to
  `((x+dualToV5 ξ)/2,(x-dualToV5 ξ)/2)` and preserves `q(X)=ξ(x)`.
- `Cl55PureSpinorParaGrassmannianBridge.neutralParaMetric = -B`.
  Consequently the chosen para convention is `ω(X,Y)=(-B)(X,KY)`.
- `ParaKahler55SUSYClosure.paraKahlerK` swaps the diagonal five-slots;
  its existing quadratic theorem proves anti-invariance, not preservation.
- `GenericMetriplecticFlow.System`: `L` skew, `M` symmetric/nonnegative,
  `L dS=0`, `M dH=0`, and `flow=L dH+M dS`.

## Source-confirmed work to complement

1. Prove nondegeneracy of the actual neutral skew form, not only skewness.
2. Prove the zero-B-field generalized-metric polarization anticommutes with K,
   supplies an operator complex structure and its reflected twin, and is positive
   when the base metric is positive. Reuse the owner data, not another carrier.
3. Instantiate the base metric by the existing `dualToV5.symm`; explicitly
   intertwine K and S with the native diagonal `(5,5)` operations and fix all
   factors/signs in the metric and skew-form transport.
4. Construct metriplectic operators from nondegenerate skew and positive forms
   using Mathlib `BilinForm.toDual`, linear maps and dual maps. Reduction maps
   must enforce the two Casimir equations; positivity is not inferred from B.
5. Prove the obstruction: an injective reversible operator forces `dS=0`.
   Thus the full symplectic inverse cannot give nonzero entropy production under
   the GENERIC entropy-Casimir law. Any construction must expose this restriction.
6. For the existing negative-vector real split-Pin lift, prove positive-metric
   preservation and transport of the para structure. Explicitly refute fixed
   symplectic invariance; the one-pair reflection is not globally antisymplectic
   either. This is fiber algebra, not affine deck descent.

## Search and consumers

Searched repo-owned `lean/` and `proofs/` for the named operators, `toDual`,
nondegeneracy, generalized metrics, dual-map reductions and metriplectic
systems. Inspected `PolarizedBoundaryInvolutions`, `FiniteParaKahler`,
`ParaHessianMetriplecticCompatibility`, `GenericMetriplecticTransportClosure`,
and the actual imported form/isometry owners. The old misleading theorem name
`paraKahlerK_preserves_Q55` has no use in the searched Lean sources; rename it to
state anti-isometry. Existing positive generalized metrics are reused.

## Excluded claims

No identification of K with Pin reflection; no claim of absolute canonical
polarization; no positive Fisher/BKM identification with the indefinite metric;
no Poisson Jacobi theorem for arbitrary state-dependent reduction; no analytic
flow existence, sheaf descent, global super-Grassmannian, CPT or continuum claim.
Verification requires locked Lean builds, transitive axiom replay and source-drift
checks. Existing unrelated staged work and dependency pins remain untouched.

## Additional user-supplied cyclotomic report

The user supplied a historical report claiming principal bundles, cotangent
bundles, minimality of the cubic, Phi_2 for the grading, and Spin/Pin orientability
in `Canonical/GrassmannianBundleCyclotomicOrientability.lean`. On inspection the
current file already had corrected scope in its header and substantive unit-orbit,
active-support and counterexample declarations. Those existing corrections are
not attributed to this task. This task aligns the remaining stale section and
witness comments, preserves all declarations, and includes the entire current
owner in fresh verification. Its import is in `Canonical/All.lean:2334`, not
necessarily the root `All.lean` cited by the pasted report.
