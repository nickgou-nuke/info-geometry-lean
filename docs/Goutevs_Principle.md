# Goutev’s Principle

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

## A Manifesto on the Absolute Relativity of Measurement

## Status

This note states a guiding principle of the repository and of the broader
physics-of-information program developed here. It is not a proof source.
It is a conceptual and structural declaration intended to orient both formal
development and interpretation.

## Core Claim

**There is no measurement in isolation. Every measurement is a comparison.**

A measurement does not reveal an absolutely meaningful scalar magnitude existing
independently of all context. It reveals a relation between the measured object
and a reference configuration, background, calibration state, ensemble, or
comparison class.

What is physically meaningful is therefore not an isolated value, but a
**relational invariant**.

## Name

We call this:

# **Goutev’s Principle of the Absolute Relativity of Measurement**

The phrase “absolute relativity” is deliberate. The claim is not merely that
some measurements are relative, nor merely that practical experiments require
calibration. The claim is stronger:

- all measurement is intrinsically relative;
- any appearance of absoluteness is a representational convenience;
- the physical content lies only in the comparison structure.

## Short Form

**Measurement is projective; observables are relational invariants.**

## Slogan Form

**No measurement stands alone. Only relations, contrasts, and ratios carry
physical meaning.**

## Operational Form

Every real experiment compares one thing with another.

A meter compares a length with a standard length.
A clock compares a process with a standard process.
A spectrometer compares signal with calibration.
A probability estimate compares frequencies or weights within an ensemble.
A quantum observable compares amplitudes, phases, or expectation values relative
to a state, basis, preparation, or reference operator.

Therefore:

> there is no physically meaningful reading without a reference,
> whether that reference is explicit or hidden.

The mythology of an “absolute value” enters only when the reference structure is
suppressed from the description.

## Formal Statement

A measurement does not determine a primitive scalar value with standalone
physical meaning. It determines only a relational quantity between objects,
states, or representations.

Accordingly, if two descriptions differ only by a common positive rescaling of
the compared magnitudes, then they encode the same physical content.

This means that the correct mathematical habitat of measurement is not, in the
first instance, an affine space of absolute values, but a **projective space of
rays**, equivalence classes, relative densities, and comparison functionals.

## Axioms

### Axiom 1. Relationality

No measurement outcome has physical meaning without a reference class.

### Axiom 2. Gauge of Common Scale

If all compared magnitudes are rescaled by the same positive factor, the
physical content is unchanged.

Formally, if
\[
x \sim \lambda x, \qquad \lambda > 0,
\]
then the equivalence class, not the raw representative, carries physical
meaning.

### Axiom 3. Admissible Observables

Only quantities invariant under common rescaling are admissible as primitive
physical observables.

Examples include:

- ratios;
- logarithmic ratios;
- relative densities;
- Radon–Nikodym derivatives;
- projective coordinates;
- cocycles and gauge-invariant comparison functionals.

### Axiom 4. Compositional Relativity

If one quantity is measured relative to a second, and the second relative to a
third, then the physically meaningful law is the law of composition of these
relations.

This yields multiplicative cocycles in ratio form and additive potentials in
logarithmic form.

### Axiom 5. Normalization is Gauge Fixing

Normalization may be useful, convenient, or computationally canonical, but it is
not ontologically primary. It is a choice of section through a projective
equivalence class.

> **Normalization is not ontology; it is gauge fixing.**

## Core Mandate: Goutev’s Principle of Absolute Relativity of Measurement

All measurements in InfoGeometry are relative. There is no isolated
observable; every observable is a comparison made relative to a reference
state, gauge, section, or projective chart.

This principle governs the architecture:

1. **Normalization is gauge fixing, not ontology.**
   A normalized state is not more fundamental than its projective ray. It is a
   choice of section through a ray.

2. **Scale is not physical until compared.**
   Raw magnitudes live upstream of measurement. Physical readouts are invariant
   under a Weyl/projective rescaling whenever the theory claims to measure
   shape rather than scale.

3. **Reference states are part of the datum.**
   A vacuum, KMS state, thermal reference, or causal cone is not an empty
   background. It is the chosen comparison frame.

4. **Every closure claim must descend.**
   A high-level thermodynamic or conformal claim must descend through
   transport, Krein/operator structure, projective normalization, and finite/
   count substrate before it is counted as native closure.

5. **Multiple representations are allowed only with bridges.**
   Boolean cubes, exterior/Fock states, Cantor cylinders, CAR atoms, and
   projective rays may coexist. They are not duplicates when their preservation
   maps are kernel-visible. Without those maps, they are duplication debt.

   Every future bridge must expose normalization, gauge, and coherence fields
   explicitly. Those fields are part of the formal contract, not optional
   commentary.

### The Master 2-Morphism

The finite master 2-morphism is:

\[
\text{gauge-normalized causal cone}
\longrightarrow
\text{finite Cantor tilt/switch Clifford cylinder algebra}.
\]

It says that after dividing out a nonzero Weyl scale, the causal-cone
generators recover the normalized finite Cantor/Fock generators:

\[
T_p^2 = 1,\qquad S_p^2 = 1,\qquad T_pS_p=-S_pT_p.
\]

Equivalently, with

\[
c_p=S_p,\qquad d_p=S_pT_p,
\]

one obtains the finite \(\mathcal C\ell(1,1)\) atom:

\[
c_p^2=1,\qquad d_p^2=-1,\qquad c_pd_p+d_pc_p=0.
\]

This is native finite closure.

The infinite completion is not native closure. It is a literature-owned socket:

\[
\text{finite Cantor cylinders}
\longrightarrow
L^2(K)
\longrightarrow
\text{Fock representation of } Cl_\infty.
\]

The owner is Çelik–Koçak 2011, which constructs a representation of the
infinite-dimensional complex Clifford algebra on \(L^2(K)\), where \(K\) is
the Cantor set, and proves equivalence with the classical Fock
representation. Their Lemma 1.1 supplies the infinite tilt/switch relations,
Theorem 2.1 builds the \(Cl_\infty\) representation, and Theorem 3.3 proves
Fock equivalence.

### Bridge Contract

The safe bridge shape is:

```text
raw carrier
  -> normalization / gauge fix
  -> normalized representation
  -> coherence / preservation data
  -> delegated owner readout
```

In Lean terms, that means the module surface must make the normalization map,
the gauge witness, and the preservation theorems explicit. A bridge that hides
those fields is incomplete, even if its prose is persuasive.

The DAG toolchain already implements the Hodge / chiral / Dirac operator
overlays in Lean as derived observability. They are useful for audit and
navigation, but they remain downstream of Lean source and do not replace owner
proofs.

## Source/Sink Chain: Log Generator -> Bregman Gap -> Free Energy

The repository treats free energy as a relative readout of a generator field,
not as an isolated scalar.

The source chain is:

\[
\text{log/Radon--Nikodym generator}
\to
\text{modular Hamiltonian}
\to
\text{Bregman gap}
\to
\text{free energy}.
\]

### 1. Log / Modular Generator

The logarithmic Radon--Nikodym density is the relative information generator.
In the finite/classical packet, KL is recorded as expectation of the log-density.
In the operator packet, the modular Hamiltonian is the negative logarithmic
density.

Thus:

\[
K = -\log \rho
\]

is not an absolute Hamiltonian first. It is a relative modular generator.

### 2. Bregman Gap

A Legendre potential determines a Bregman divergence. The repository uses this
gap as the energy induced by a reference point:

\[
E_{\theta_0}(\theta)
=
D_L(\theta,\theta_0).
\]

This is the finite scalar bridge from convex geometry to thermodynamics.

### 3. Free Energy Readout

The free energy is the Legendre/Fenchel/Bregman thermodynamic readout of the
generator-induced gap:

\[
F
=
U-\varepsilon S.
\]

This is a scalar thermodynamic theorem in the finite Bregman/Gibbs setting.

The repository does not assert a universal unbounded operator Legendre theorem
for arbitrary type-III algebras. Operatorial versions are bounded/modular
packets whose scalar thermodynamic meaning appears only after a trace, state,
KMS datum, or projective readout is supplied.

## DAG/Hodge Toolchain: The Causal Cone as a Finite Operator System

The declaration DAG is not only an index. It is the finite causal cone on which
the repository measures descent, obstruction, and closure flow.

The graph/Hodge layer implements:

\[
\Delta_0=\partial_1^T\partial_1,
\]

\[
\Delta_1=\partial_1\partial_1^T+\partial_2^T\partial_2,
\]

and the graph Dirac operator

\[
D=
\begin{pmatrix}
0 & \partial_1^T\\
\partial_1 & 0
\end{pmatrix}
\]

on \(0\oplus1\)-chains.

A chiral grading \(\Gamma\) is implemented as a signed diagonal grading, and the
finite anticommutation check is

\[
\Gamma D + D\Gamma=0.
\]

### DAG Operator Owner Map

| Role | Layer | Responsibility |
|---|---|---|
| Graph/Hodge implementation | `lean/DAG/GraphHodge.lean` | concrete coboundaries, Laplacians, graph Dirac, chiral grading |
| Krein chirality owner | `lean/InfoGeometry/Krein/Prelude.lean` | doubled/Krein chirality operator and projectors |
| Modular block split | `lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean` | active/apex projector split, scale/shape decomposition |
| Arithmetic finite carrier | `lean/InfoGeometry/Arithmetic/PrimeExteriorRepresentation.lean`, `lean/InfoGeometry/Arithmetic/PrimeBooleanCube.lean` | square-free finite states, chirality, state energy, Möbius readout |
| Infinite Cantor/Fock socket | Çelik--Koçak 2011 | \(L^2(K)\) Clifford representation equivalent to Fock |
| Closure discipline | `OwnerTarget`, `BridgeTarget`, `SocketTarget` | machine-visible owner, bridge, and socket-debt surfaces |

### Operator Boundary Rule

The DAG graph Dirac, the arithmetic Cantor/Fock Dirac package, and the modular
Hamiltonian are adjacent but not identical.

- The DAG graph Dirac measures the declaration causal cone.
- The finite arithmetic Hamiltonian is the prime-weighted number operator.
- The modular Hamiltonian is a relative logarithmic generator.
- The Bregman free energy is a scalar thermodynamic readout of a generator gap.

A bridge may relate these objects only by exposing its reference datum:
projector, gauge, state, trace, KMS datum, finite cutoff, or literature-owned
completion theorem.

### Relative Measurement Interpretation

A theorem is not merely a closed term. It is a closed term situated in a
reference frame.

The reference may be:

- a projective ray representative,
- a KMS state,
- a Drazin projector,
- a finite prime cutoff,
- a graph/Hodge causal cone,
- a Weyl gauge,
- or a literature-owned infinite completion.

Thus the repository treats absolute magnitudes as pre-observables and
relative/projective/cocycle/Bregman readouts as theorem-safe observables.

## Temperature as Inverse Modular Scale

The scalar first-law readout is:

\[
\delta Q_{\mathrm{rev}} = T\,dS,
\qquad
\beta := \frac{1}{T} = \frac{dS}{\delta Q_{\mathrm{rev}}}.
\]

In the repository dictionary, \(\beta\) is the state-relative modular scale.
The modular Hamiltonian / log generator is the operator field whose scalar
readout gives the heat or energy variation being compared.

So the correct boundary is:

- temperature is not the raw operator;
- the operator is the state-relative modular generator;
- temperature is the inverse projective/modular scale of the readout.

The theorem-safe scalar core already exists in
`lean/InfoGeometry/Thermo/RelativeTemperatureFirstLaw.lean`, and the projective
temperature inversion discipline is separately handled in
`lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean`.

### Finite Arithmetic Interpretation

The finite Cantor lattice is

\[
X_\Lambda=\{0,1\}^{\mathcal P_\Lambda}.
\]

A vertex is a square-free prime occupancy state

\[
S\subseteq \mathcal P_\Lambda,
\qquad
n_S=\prod_{p\in S}p.
\]

The local split-Majorana pair satisfies

\[
c_p=\varepsilon_p+\iota_p,\qquad
d_p=\varepsilon_p-\iota_p,
\]

and the local parity is

\[
\Pi_p=c_pd_p=1-2N_p.
\]

The global chirality is

\[
\Gamma_\Lambda=\prod_{p\le \Lambda}(1-2N_p),
\]

and on a square-free state it is

\[
\Gamma_\Lambda|S\rangle=(-1)^{|S|}|S\rangle
=\mu(n_S)|S\rangle.
\]

The arithmetic Hamiltonian is the diagonal number operator

\[
H_\Lambda=\sum_{p\le\Lambda}(\log p)N_p,
\]

so

\[
H_\Lambda|S\rangle
=
\left(\sum_{p\in S}\log p\right)|S\rangle
=
\log(n_S)|S\rangle.
\]

The Möbius/Witten character is finite:

\[
\mathcal I_\Lambda(s)
=
\operatorname{Tr}_{\mathcal F_\Lambda}
\left(\Gamma_\Lambda e^{-sH_\Lambda}\right)
=
\prod_{p\le\Lambda}(1-p^{-s}).
\]

The infinite identity

\[
\prod_p(1-p^{-s})=\frac1{\zeta(s)}
\]

is analytic and belongs to the Euler-product socket, valid first in the region
\(\Re(s)>1\). It is not a finite native theorem.

### The Dirac Warning

The naive Majorana sum

\[
D_\Lambda=\sum_{p\le\Lambda}\sqrt{\log p}\,c_p
\]

does not square to the arithmetic Hamiltonian. Since the \(c_p\) anticommute,

\[
D_\Lambda^2
=
\sum_{p\le\Lambda}\log p\cdot 1,
\]

which is a scalar cutoff energy, not

\[
H_\Lambda=\sum_p(\log p)N_p.
\]

The correct finite arithmetic Hamiltonian is the diagonal number operator, or
the square of a genuine Hodge/graph Dirac package with the appropriate
creation/annihilation and projection structure. This distinction is mandatory
for the Hilbert–Pólya lane to remain honest.

### Relation to Projective/Weyl Gauge

The projective layer enforces the principle that scale is gauge.
`ProjectiveFoundation.lean` treats the real projective substrate separately
from the lifted cocycle, defines cover-to-projective descent, and records
kernel anomalies as the obstruction carried by invisible lifts.

The Weyl-gauge bridge applies the same principle to the Cantor/Fock layer:

\[
\text{raw scaled generators}
\quad
\xrightarrow{\text{divide by nonzero Weyl scale}}
\quad
\text{normalized Clifford generators}.
\]

The normalized algebra is the invariant content; the raw scale is the gauge.

### Implementation Rule

Every future bridge must be one of:

- `@[owner_target_tag]`: the module owns and proves the closure contract.
- `@[bridge_target_tag]`: the theorem transports an invariant between
  representations.
- `@[socket_debt_tag]`: the statement is honest deferred content.

The compiler addons already make these surfaces machine-visible: owner targets,
bridge targets, and socket debt are auditable by dedicated commands.

## Source/Sink Chain: Log Generator → Bregman Gap → Free Energy

The repository treats free energy as a relative readout of a generator field,
not as an isolated scalar.

The source chain is:

\[
\text{log/Radon--Nikodym generator}
\to
\text{modular Hamiltonian}
\to
\text{Bregman gap}
\to
\text{free energy}.
\]

### 1. Log / Modular Generator

The logarithmic Radon--Nikodym density is the relative information generator.
In the finite/classical packet, KL is recorded as expectation of the
log-density. In the operator packet, the modular Hamiltonian is the negative
logarithmic density.

Thus:

\[
K = -\log \rho
\]

is not an absolute Hamiltonian first. It is a relative modular generator.

### 2. Bregman Gap

A Legendre potential determines a Bregman divergence. The repository uses this
gap as the energy induced by a reference point:

\[
E_{\theta_0}(\theta)
=
D_L(\theta,\theta_0).
\]

This is the finite scalar bridge from convex geometry to thermodynamics.

### 3. Free Energy Readout

The free energy is the Legendre/Fenchel/Bregman thermodynamic readout of the
generator-induced gap:

\[
F
=
U-\varepsilon S.
\]

This is a scalar thermodynamic theorem in the finite Bregman/Gibbs setting.

The repository does not assert a universal unbounded operator Legendre theorem
for arbitrary type-III algebras. Operatorial versions are bounded/modular
packets whose scalar thermodynamic meaning appears only after a trace, state,
KMS, or projective readout is supplied.

## DAG/Hodge Toolchain: The Causal Cone as a Finite Operator System

The declaration DAG is not only an index. It is the finite causal cone on
which the repository measures descent, obstruction, and closure flow.

The graph/Hodge layer implements:

\[
\Delta_0=\partial_1^T\partial_1,
\]

\[
\Delta_1=\partial_1\partial_1^T+\partial_2^T\partial_2,
\]

and the graph Dirac operator

\[
D=
\begin{pmatrix}
0 & \partial_1^T\\
\partial_1 & 0
\end{pmatrix}
\]

on \(0\oplus1\)-chains.

A chiral grading \(\Gamma\) is implemented as a signed diagonal grading, and
the finite anticommutation check is

\[
\Gamma D + D\Gamma=0.
\]

### Operator Boundary Rule

The DAG graph Dirac, the arithmetic Cantor/Fock Dirac package, and the modular
Hamiltonian are adjacent but not identical.

- The DAG graph Dirac measures the declaration causal cone.
- The finite arithmetic Hamiltonian is the prime-weighted number operator.
- The modular Hamiltonian is a relative logarithmic generator.
- The Bregman free energy is a scalar thermodynamic readout of a generator gap.

A bridge may relate these objects only by exposing its reference datum:
projector, gauge, state, trace, KMS datum, finite cutoff, or
literature-owned completion theorem.

### Relative Measurement Interpretation

A theorem is not merely a closed term. It is a closed term situated in a
reference frame.

The reference may be:

- a projective ray representative,
- a KMS state,
- a Drazin projector,
- a finite prime cutoff,
- a graph/Hodge causal cone,
- a Weyl gauge,
- or a literature-owned infinite completion.

Thus the repository treats absolute magnitudes as pre-observables and
relative/projective/cocycle/Bregman readouts as theorem-safe observables.

## Mathematical Consequences

The principle has immediate structural consequences.

### 1. Projective States Are More Primitive Than Normalized States

A normalized probability vector or density is not the primary physical object.
The more primitive object is a positive ray or equivalence class under common
scaling.

This motivates treating projective positive states as foundational.

### 2. Relative Quantities Are More Primitive Than Absolute Quantities

The fundamental observables are not bare values but relations such as
\[
\frac{x}{y}, \qquad \log\frac{x}{y}, \qquad \frac{d\mu}{d\nu}.
\]

This shifts emphasis from absolute entropy or energy to:

- relative entropy;
- relative potential;
- relative modular operator;
- relative log-density;
- relative transport laws.

### 3. Gauge-Invariant Structure Replaces Absolute Scale

Any theory that takes absolute magnitude as primitive risks encoding
representation-dependent artifacts as physics.

The correct invariant content lies in what survives after quotienting out common
scale.

### 4. Composition Laws Become Central

Once measurement is relational, cocycle laws and transport laws are not
secondary technical facts. They become primary statements about how measurement
content propagates across layers of description.

### 5. Reference Dependence Is Structural, Not Merely Epistemic

The role of a reference state, background law, calibration, or comparison class
is not an accidental feature of imperfect knowledge. It is built into the
structure of measurement itself.

## Relation to Jaynes

This principle is compatible with Jaynes, but stronger.

### Jaynes-Type Statement

Probability assignments are relative to prior information.

### Goutev-Type Statement

Measurement outcomes themselves are relative structures. Absolute magnitudes are
not physically primitive.

Jaynes emphasizes epistemic relativity: inference depends on available
information.

Goutev’s Principle emphasizes ontological and structural relativity: even before
inference, the measured content is relational.

Thus the principle extends the informational viewpoint from probability
assignment to the very meaning of physical measurement.

## Interpretation for Physics of Information

If this principle is taken seriously, then information is not a layer added on
top of physics. Rather, physics itself becomes a theory of admissible
relational distinctions and their transport.

The deepest objects are then not isolated values, but structured comparisons:

- relative state to reference state;
- signal to calibration;
- operator to modular background;
- boundary mode to bulk constraint;
- transported observable to its generating relation.

In such a framework:

- inference becomes a form of physical transport;
- modular structure becomes a generator of relational dynamics;
- anomalies become obstructions to coherent relational transport;
- boundary singularities become visible failures or concentrations of relational
  consistency.

## Repository Implications

Within this repository, Goutev’s Principle supports the architectural choice
that:

- positive rays are more fundamental than normalized representatives;
- relative potentials are more fundamental than absolute scalar observables;
- relative modular operators are more fundamental than isolated Hamiltonian-like
  readouts;
- transport laws and cocycles are not optional decoration but primary
  structural content;
- normalization bridges are sections, not roots;
- scalar quantities should be treated as readouts of deeper relational or
  operator-level objects whenever possible.

This principle therefore aligns with the count → projective → operator → Krein
→ transport → thermo ladder.

It supports the claim that adjacent translators and coherence theorems are not
mere implementation details, but expressions of a deeper physical doctrine:
**all admissible physics is relationally organized physics**.

## Theorem-Style Formulation

A concise theorem-style version is:

> **Goutev’s Principle.**
> Physical measurement is projective: two representations related by a common
> positive rescaling encode the same physical content. Hence primitive
> observables are relational invariants rather than absolute magnitudes.

## Strong Ontological Form

A still stronger philosophical form is:

> Nature does not present isolated magnitudes. It presents only structures of
> comparison, distinction, and transformability. Absolute value is a
> representational convenience; relation is the ontology.

## Practical Rule for Formal Development

When choosing between two formulations, prefer the one that:

- makes the reference structure explicit;
- treats normalization as secondary;
- exposes the gauge symmetry of common scale;
- promotes relative observables over absolute ones;
- makes compositional laws visible.

This is the preferred direction of formalization.

## Closing Declaration

The principle can be summarized in one sentence:

> **There is no measure outside comparison, no value outside relation, and no
> physical content outside invariant structure.**

That sentence is the intended interpretive spine of this manifesto.
