# Two-boundary weak functionals and static property separation

## Scope

This extension reconstructs the exact finite mathematics common to the supplied
TSVF, weak-value, Cheshire-property, topology, thermofield, and operator-current
language. It is stacked on the boundary-conditioning work of PR #148 and reuses
its guarded two-level weak-value owner. It deliberately does not identify the
following distinct objects:

- a pre/post-selected quantum transition functional;
- a positive Doob-conditioned stochastic process;
- a local current satisfying a continuity equation;
- an orientation-reversing topological gluing;
- a Tomita antiunitary or a Pin structure;
- a thermofield purification;
- a non-Hermitian quantum-clock effective Hamiltonian.

The new theorem owners contain no paper-specific Hamiltonian, spatial wave
packet, measurement pointer, field-energy density, or radiation calculation.
Consequently their strongest honest conclusion is static weak-property
separation plus functorial readout of any independently proved operator balance
law.

## Repository archetypes already present

The repository already contained most of the algebraic roles, but on separate
carriers.

1. `SarsModularWeakValue.lean` defines an `Option Complex` weak ratio for a
   fixed two-level system. The ratio is `none` at zero overlap.
2. PR #148 adds exact probe linearity, post-selection ray invariance, a Pauli
   amplification example, and the associated post-selection success cost.
3. `FiniteMatrixElementDuality.lean` treats fixed finite matrix elements and
   their covariance.
4. `FiniteHestenesHilbertSchmidtStandardForm.lean` constructs a genuine
   conjugate-linear Tomita map and proves its antiunitarity; it also identifies
   the commutant of left matrix actions with right matrix actions.
5. `ThermofieldDoubleStateBridge.lean` proves that squared finite TFD
   coefficients are Boltzmann weights. It does not define opposite subsystem
   entropy-production laws.
6. `KleinBottleSymmetry.lean`, `KleinBottleCobordism.lean`, and
   `PinO55GlideReflection.lean` own independent cross-cap, glide, and Pin
   relations. None derives a Klein-bottle quotient from a pair of boundary
   vectors.
7. The bipolar/Apollonius branches own a locally flat Cartan connection with
   nontrivial central contour holonomy. Those theorems do not supply the
   microscopic Aharonov--Bohm dynamics of a charged particle.

The missing local owner was therefore not another topology or thermofield
construction. It was a dimension-independent, proof-carrying regular boundary
pair and its native linear functional on finite endomorphisms.

## 1. The exact two-boundary carrier

For a finite index type `ι`, set

```text
V_ι = ι → ℂ,
End_ι = Module.End ℂ V_ι.
```

The finite Dirac pairing is

```text
pairing(post, pre) = sum_i conjugate(post_i) pre_i.
```

A regular boundary pair is

```text
p = (pre, post, pairing(post,pre) ≠ 0).
```

The nonzero-overlap premise is carried in the type. Thus the weak functional is
total on its declared domain:

```text
W_p(A) = pairing(post, A pre) / pairing(post, pre).
```

`FiniteTwoBoundaryWeakFunctional.lean` proves that `W_p` is a native complex
linear map

```lean
weakValueLinear p : Module.End ℂ V_ι →ₗ[ℂ] ℂ.
```

It also proves

```text
W_p(0)=0,
W_p(I)=1,
W_p(A+B)=W_p(A)+W_p(B),
W_p(cA)=c W_p(A).
```

Nonzero rescaling of either boundary representative leaves every weak value
unchanged. This is the exact projective content of the two-vector formula. It
is not a quotient topology on time and does not introduce interaction between
the boundary data.

The new owner specializes back to the existing `SarsModularWeakValue` formula
on `Fin 2` and proves exact equality with the value inside its guarded
`Option`.

## 2. Operator balance laws descend; currents do not appear automatically

Linearity yields the generic theorem

```text
A₁ - A₀ = incoming - outgoing
    implies
W_p(A₁)-W_p(A₀)=W_p(incoming)-W_p(outgoing).
```

If both endpoint density weak values vanish, the incoming and outgoing weak
fluxes are equal. This is the correct theorem boundary for the conservation
language.

The theorem does not construct `A₀`, `A₁`, `incoming`, or `outgoing`. In a
physical transport model they must arise from a Hamiltonian and a local
operator continuity equation. A static pair of weak values cannot by itself
distinguish transport from interference, nor can it establish an empty
spacetime corridor.

## 3. Explicit path-times-spin separation witness

`WeakPropertySeparation.lean` uses the four-coordinate carrier with basis

```text
left-up, left-down, corridor-up, corridor-down.
```

Choose the unnormalized ray representatives

```text
pre  = (1,0,1, 1),
post = (1,0,1,-1).
```

Their overlap is one. Define

```text
P_corridor = diag(0,0,1, 1),
S_corridor = diag(0,0,1,-1).
```

The source proves

```text
P_corridor² = P_corridor,
P_corridor S_corridor = S_corridor,
S_corridor P_corridor = S_corridor,
S_corridor² = P_corridor.
```

The exact weak readouts are

```text
W(P_corridor)=0,
W(S_corridor)=2.
```

This is a finite, explicit realization of the algebraic Cheshire pattern:
destructive interference cancels the unsigned support readout while preserving
a signed property readout in the same support sector.

It additionally proves

```text
W(S_corridor²)=0 ≠ 4=W(S_corridor)².
```

Hence the weak functional is not an algebra character and should not be
mistaken for a positive probability state. The value `2` is anomalous relative
to the eigenvalues `{-1,0,1}` of the displayed signed operator, but the source
does not infer a measurement-pointer distribution from that fact.

## 4. Corrections to the supplied physical superposition

### Angular-momentum flow

The cited angular-momentum paper describes a region with *vanishingly small*
probability of particles or fields, not an exactly empty region in the abstract.
The present Lean witness has an exactly zero weak projector readout, but it is
an independent finite algebraic example and is not advertised as a
formalization of that experiment.

A theorem of angular-momentum transport needs all of the following additional
objects:

```text
spatial/graph regions,
time evolution or a Hamiltonian,
local density operators,
local angular-momentum-current operators,
an operator continuity equation,
pre- and post-selected trajectories,
a quantitative small-probability estimate.
```

The generic weak balance theorem can consume such a continuity equation after
it is constructed.

### TSVF versus a Klein bottle

Two boundary vectors and their transition functional do not determine a
Klein-bottle quotient. A Klein bottle requires an explicit orientation-reversing
gluing or glide relation. An antiunitary map is linear-algebraic data; a
cross-cap is quotient-topological data. The repository already owns both kinds
of archetype independently and does not identify them here.

A Pin-minus or Kramers sign likewise requires a specified Pin structure or
antiunitary square law. It is not a consequence of pre/post-selection alone.

### Thermofield doubling

A TFD vector lives in a tensor product and its reduced weights can be Gibbs
weights. This does not imply opposite time derivatives of subsystem entropy.
For a globally pure closed state the two reduced density matrices have the
same nonzero spectrum, hence equal von Neumann entropies at each time; a claim
about opposite entropy-production arrows requires a separately defined open or
coarse-grained dynamics.

### Non-inertial quantum clocks

The cited clock work derives an effective non-Hermitian generator through
operator ordering/noncommutation in a relational clock construction. It does
not supply a universal additive term `-i a hbar/(2c)`, and it does not identify
that term with the Unruh temperature. No such equation is introduced here.

### Aharonov--Bohm acceleration

The acceleration-without-radiation result is a separate dynamical statement
about a specifically engineered quantum evolution. It is not obtained from a
weak-value ratio, a central spin holonomy, or a finite routing link alone.
The repository's existing contour and vortex owners remain theorem-safe
algebraic/topological interfaces rather than a substitute radiation model.

## Public entry points

```lean
import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
import InfoGeometry.Streaming.WeakPropertySeparation
import InfoGeometry.Streaming.TwoBoundaryWeakPristineChain
```

The focused audit is

```text
lean/InfoGeometry/Streaming/TwoBoundaryWeakAudit.lean
```

and the local verification command is

```text
bash scripts/check_two_boundary_weak.sh
```

## Exact next frontier

The nearest physical development should not add more metaphoric identifications.
It should construct one finite dynamical interferometer or graph model with:

1. a unitary step or Hamiltonian;
2. explicit region projectors;
3. a local conserved-property density;
4. edge-current operators;
5. a proved operator continuity equation;
6. a regular pre/post pair;
7. the resulting weak density and weak current readouts.

Only that theorem can justify the phrase “property transport through a region”
in this codebase. A subsequent and separate topology theorem may then compare a
specified orientation-reversing boundary gluing with an existing Klein-bottle
carrier. Neither bridge is inserted as an assumption in this extension.
