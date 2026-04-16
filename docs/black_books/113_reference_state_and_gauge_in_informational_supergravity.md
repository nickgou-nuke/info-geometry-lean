# Reference State and Gauge in Informational Supergravity

This is the boundary between formalizing mathematics and formalizing physics in
Lean.

If this were only a generic math library, the "vacuum" would be the empty Lean
context (`Type*`, logic, imported lemmas).

In this repository, the vacuum is not that.
The vacuum is a deliberately engineered algebraic ground state:

- split-signature `Cl(n,n)` doubled real carrier,
- Krein-compatible sign/analyzer structure,
- modular/KMS baseline package for the active lane.

## 1. Reference State (Thermal Vacuum)

The reference state is the equilibrium background prior to local observer frame
choice.

Repo-native form:

- ground carrier: doubled lane (`E ⊕ E*` style realization),
- balancing involution/conjugation channel on the doubled space,
- thermal bath: KMS datum `ω` as baseline equilibrium,
- accepted ontology assumptions that define the lane's ground state.

So owner files do not define objects in an empty logical void.
They define excitations of this prepared vacuum.

Example reading:

- defining a quasilattice Dirac surface is an excitation relative to this
  ground state,
- not a free-floating declaration detached from modular/Krein preparation.

## 2. Gauge (Representation Frame)

If the vacuum is objective background, gauge is the subjective frame of
measurement/representation.

In repo terms, gauge moves include:

- owner presentation ↔ translator presentation,
- projective/operator/Krein basis changes,
- analyzer/projector choice in readout,
- comparison-state anchoring choices.

Therefore:

- translator file = gauge-transform candidate,
- coherence theorem = gauge-invariance certificate,
- obstruction term = quantified gauge non-invariance (line splitting).

## 3. Spectroscopic Identity Rule

A theorem-object is not identified by syntax alone.
It is identified by response under admissible probes relative to a reference
state and gauge choice.

That response packet includes, depending on lane:

- structural channel (dependencies, rep-depth legality, ownership),
- symmetry/energetic channel (grading, transport, anomaly, regular/defect).

This is why doubled/Krein surfaces are not decorative.
They are the correct geometry for sign-sensitive and conjugate response modes.

## 4. Closure Trichotomy

Every cross-presentation claim must close as exactly one of:

- equivalence,
- quantified obstruction,
- discard.

Anything else remains exploratory spectroscopy and must not be promoted as
owner truth.

## 5. Minimal Formal Target (Schematic)

```lean
structure ReferenceState (α : Type _) where
  ground : α
  assumptions : List String

structure GaugeTransform (α : Type _) where
  map : α → α
  admissible : Prop

inductive BridgeOutcome
  | equivalence
  | obstruction (residue : String)
  | discard (reason : String)
```

The key point is methodological, not syntactic:
all measurements are relative to prepared vacuum plus gauge, with kernel-gated
closure.
