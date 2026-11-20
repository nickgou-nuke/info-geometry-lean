# Holonomy of the real information Carnot cycle

Task date: 2026-11-18, Europe/Sofia. This extends accepted PR408 source
`c4d12dcea71455c2ad0885f90a36e4362d80cacb`, tree
`40ff0f6dc60c5d4c9097859bd8d782c16552f063`. The initiating follow-up is
preserved in `docs/intake/carnot-holonomy-20261118/prompt.txt` and its manifest.

## Claim and construction contract

The word holonomy requires a base, fiber, and connection. The existing Carnot
cycle has two distinct projections. Its density curve exactly retraces, while
its Hamiltonian control changes scale. The extension formalizes that distinction
on the full real matrix algebra; no commutation premise is imposed on the hot
Hamiltonian endpoints or arbitrary operator directions.

| Claim | Exact carrier and native construction | Scope |
| --- | --- | --- |
| Cold density is reversed hot density | Existing matrix affine Hamiltonians and actual Gibbs `state` | Algebraic identity for every real parameter, `c ≠ 0` |
| Four-stroke density loop | Native `Path` objects from the actual hot/cold Gibbs curves and reciprocal-scale controls | Nonempty finite matrix dimension, self-adjoint endpoints, `c > 0` |
| Density transport cancels | A path-sensitive transport into an arbitrary Group, with constant, reverse and concatenate laws | Conditional universal connection law; no ordinary homotopy-invariance or flatness premise |
| Matrix work form | `Base = Mat × Mat`; native continuous bilinear `α_(ρ,H)(R,A) = Tr(ρ*A)` | Full ambient real matrix controls |
| Differential and curvature | Actual Fréchet derivative of `α`, alternated to `dα(v,w) = Tr(v.1*w.2 - w.1*v.2)` | Derived from native differentiation, not stored as a structure field |
| Work connection | On `Base × ℝ`, `Θ_(x,w)(v,z) = z - α_x(v)`; vertical reproduction and fiber-translation invariance | Explicit connection form on a trivial additive real bundle |
| Horizontal lift | Integrate the actual pulled-back matrix work current and prove its derivative by native FTC | Requires the actual base derivative and continuous current |
| Closed full-base cycle | Native affine and scale `Path` objects with endpoints in `Mat × Mat` | Both density and Hamiltonian match at every junction and at return |
| Carnot work holonomy | Compose the four affine translations obtained from the actual stroke integrals | Translation by work-on `-cycleWork`; work output has the opposite sign |

The connection is not promoted to a bundled Mathlib principal-bundle object.
Its actual connection form, derivative, vertical and translation laws, horizontal
lifts and affine transport are constructed. The generic density transport theorem
does not construct an Uhlmann connection or solve a non-Abelian transport ODE.
The cycle transport is the composition of its four constructed horizontal stroke
transports; no globally smooth concatenation or transport functional on arbitrary
continuous paths is asserted.

The new owners are `Thermo.RealMatrixCarnotStateLoop`,
`Thermo.RealMatrixWorkConnection`, and `Thermo.RealMatrixCarnotHolonomy`.
The first proves exact density retracing and conditional group-valued cancellation.
The second constructs the actual matrix connection, curvature and horizontal lifts.
The third supplies the closed full-base path, discharges the lift premises for the
actual strokes, and derives the work-translation and entropy-area readbacks.

## Path identity and transport convention

For the existing hot Hamiltonian `Hh(t) = H₀ + t(H₁-H₀)`, the cold path is
`Hc(t) = c H₁ + t(c H₀-c H₁) = c Hh(1-t)`. Consequently

```
state (β/c) (Hc(t)) = state β (Hh(1-t)).
```

The scale-stroke density paths are constant. Thus the actual four-stroke native
path is hot, constant, reversed hot, constant. The native group-valued transport
uses the repository's row-action order `τ(p.trans q) = τ(p) * τ(q)`. Reversal
gives the inverse, so the product cancels without commuting group elements.
The loop is not asserted to equal a constant parameterized path. A null-homotopy
alone would not force trivial holonomy for a curved connection; no such argument
or ordinary fundamental-groupoid factorization is used.

This cancellation concerns geometric transport depending only on the density
path. It says nothing about a physical dynamical phase depending on Hamiltonian
and elapsed time, or about additional unrecorded orbit controls.

## Work geometry and signs

Let `x=(ρ,H)` and `v=(R,A)`. Work done on the system has one-form

```
α_x(v) = Tr(ρ*A).
dα(v,w) = Tr(R_v*A_w - R_w*A_v).
Θ_(x,w)(v,z) = z - α_x(v).
```

The additive principal-connection curvature with this sign is `-dα`. A horizontal
lift has `w' = Tr(ρ H')`. The integral therefore shifts `w` by total work-on,
which is `-cycleWork` under the established Carnot convention.

The alternating pairing is not the trace of a commutator. Noncommuting real
matrix directions are retained and explicitly exhibited, but noncommutativity
is not required for Abelian work curvature to be nonzero. The curvature witness
is an ambient symmetric, trace-zero density direction paired with a symmetric
Hamiltonian direction; it is not asserted to be a complete Gibbs-submanifold
tangent pair or a particular finite-temperature engine example.

On the reversible thermodynamic description, `δWon = dU - T dS`; a closed-cycle
work-output shift is `(Th-Tc) ΔS`. The extension derives the cycle endpoint
formula from the actual matrix stroke integrals. A general differential-form
pullback theorem to a Souriau coadjoint manifold and a general Stokes theorem
for that manifold remain separate obligations.

The algebraic integral readback requires `β ≠ 0` and `c ≠ 0`, nonempty finite
matrix dimension, and self-adjoint Hamiltonian endpoints. The physical positive
work conclusion additionally uses `β > 0`, `0 < c < 1`, and positive entropy
increase on the hot stroke. No commutation hypothesis is used.

## Existing owners inspected and reused

| Existing owner | Source-backed content | Reuse or boundary |
| --- | --- | --- |
| `Thermo.RealMatrixCarnot` | Actual affine Gibbs isotherms, scale controls, continuous currents and native integral budgets | Reused directly; existing definitions and proofs retained |
| `Thermo.RealMatrixGibbs` | Actual full real Gibbs construction and continuous trace | Reused for the work form |
| `Recovered.SplitQuaternionMatricesRecovered` | Closed real split-quaternion matrix identities | Reuse existing symmetric noncommuting generators for the curvature witness |
| `Canonical.OperatorContentNetwork.PathTransport` | Ordered full-matrix transport on native quiver paths and endpoint gauge covariance | Its row-action convention is retained; finite labels are not identified with analytic transport |
| `OperatorAlgebra.DerivationGaugeTransport` | Actual algebraic covariant derivative, CE curvature and gauge law | Source precedent; no existing path ODE construction is inferred |
| `Canonical.FrechetCECovariantConnection` | Continuous adjoint covariant derivative and CE-curvature compatibility | Distinct from the additive work connection and its path integral |
| `Algebraic.CartanSouriauAffineCocycle` and `Algebraic.CartanSouriauCocycleGibbsCharacter` | Supplied affine symmetry cocycle, action laws and twisted Gibbs multiplier | Group cocycles are not automatically cycle holonomy |
| `Canonical.UhlmannBuresHolonomy` | Anomaly-based regular-lane curvature shadow and inertial vanishing | No purification parallel transport is supplied by this owner |
| `Canonical.SouriauBerryPhaseMonodromyBridge` | Arithmetic of a defined `2πw` readout | No winding or phase is derived from a path |
| `Canonical.RealBerryRotorBridge` | Regularized Stokes equality supplied in a field | Not used as a constructed Stokes theorem |
| `Canonical.SouriauGeometricQuantizationConnection` | Real symplectic-plane coefficients and coordinate curvature normalization | It explicitly does not construct a line-bundle connection |

Search covered related owners, alternate names, declarations, imports and
consumers. The navigation preflight reported no installed declaration-DAG index
or manifest. This is a bounded source audit; fresh graph coverage is not claimed.

## Open implications

An actual Uhlmann connection requires a purification amplitude, horizontality,
the Sylvester equation and its solvability, and a parallel-transport construction.
A real implementation can use transpose and an internal phase structure without
introducing an external scalar imaginary unit. None of these analytic claims is
deduced from the existing anomaly-curvature shadow.

Souriau's affine moment-map cocycle is a symmetry obstruction. Identifying it
with a holonomy requires a specified extension or bundle and connection.
Entropy invariance on an orbit does not identify an entire entropy level set
with one orbit. No Goldstone spectrum, spacetime causal propagator, NESS entropy
balance or Gromov--Witten partition identification follows from these results.

## Primary mathematical references

- Charles-Michel Marle, *From Tools in Symplectic and Poisson Geometry to
  Souriau's Theories of Statistical Mechanics and Thermodynamics*,
  [arXiv:1608.00103](https://arxiv.org/abs/1608.00103), especially 7.2.4–7.2.10:
  momentum-map shifts, affine coadjoint transformation, entropy invariance,
  and the Lie-algebra cocycle. The present scalar-temperature matrix cycle does
  not instantiate the full Lie-algebra-valued temperature construction.
- Armin Uhlmann, *Parallel transport and “quantum holonomy” along density
  operators*, Reports on Mathematical Physics 24 (1986), 229–240,
  [doi:10.1016/0034-4877(86)90055-8](https://doi.org/10.1016/0034-4877(86)90055-8):
  purification parallelity is a separate construction from the additive work
  connection used here.

Native acceptance is recorded separately in the holonomy validation record and
the current PR validation section.
