# Considering Alignment: Reference State, Gauge, and the Digital Spectrometer

This chapter formalizes the alignment intuition as method, not metaphor.

The core move is to treat spectroscopy as a structural discipline for theorem
architecture:

- the object is not read directly;
- it is interrogated under controlled couplings;
- what stabilizes is the invariant response pattern across channels.

In repo terms, this is already the working grammar of owner, translator,
coherence, and obstruction surfaces.

## Alignment Thesis

The spectroscopy background is not peripheral biography.
It is a generative method for this repository's architecture.

A presentation lane is a response channel.
A theorem object is identified by the spectrum it induces under admissible
probes and gauge choices relative to a fixed reference state.

So the audit problem is not "is this statement syntactically present?"
It is:

- what channel was used,
- what baseline was assumed,
- which response invariants persisted,
- where splitting or leakage appeared,
- and whether the split was closed as equivalence, obstruction, or discard.

## The Doubled Spectral View

The repository repeatedly exposes a doubled response structure:

- structural/semantic spectrum (dependencies, ownership, rep-depth legality),
- energetic/symmetry spectrum (grading, transport, anomaly, defect/regular split).

This is why doubled/Krein language is natural here.
It carries sign-sensitive channels where one scalar lane is insufficient.

## Reference State (Repo-Native Ground State)

Reference state is not empty Lean context.
It is a deliberately engineered ground state with two layers:

- logical layer: kernel + toolchain + declared foundational assumptions,
- lane layer: minimal owner skeleton and admissibility packet for that branch.

For modular lanes this includes, at minimum:

- owner modular surface,
- support/regular-core hypotheses,
- projector package assumptions,
- domain-sensitive log admissibility constraints.

All observed behavior is interpreted relative to this ground state.

## Gauge (Representation Relativity)

Gauge freedom is representation freedom with owner meaning preserved.

- translator files are gauge transforms,
- coherence files are gauge-invariance witnesses,
- obstruction terms are certified non-invariance/splitting residues.

This connects projective states, relative modular operators, comparison metrics,
and transported observables without collapsing them into one syntax lane.

## Spectral Audit Pipeline (Operational)

The pipeline can be treated as a strict spectroscopic protocol:

- sample preparation: file identity card,
- spectral decomposition: basis packet,
- overlap analysis: mixed-state detector,
- line assignment: candidate bridge finder,
- selection rules: Pauli audit,
- closure: compiler crystallization,
- atlas: Rosetta registry.

This vocabulary should be adopted in CLI/orchestrator surfaces where useful,
including `injection_capture` and umbrella routing/reporting.

## The Repo as Digital Spectrometer

Under this doctrine, the repository is a digital spectrometer for formal
mathematics:

- owner lanes prepare the sample,
- translator lanes rotate polarization/basis,
- coherence lanes calibrate cross-channel alignment,
- defect/anomaly lanes report line splitting and forbidden transitions,
- kernel closure certifies resolved assignment.

## Formalization Target: Reference/Gauge Surface

A concrete next theorem architecture target:

1. define lane-level `ReferenceState` packets,
2. define admissible `GaugeTransform` classes on maintained presentations,
3. define probe/readout families for each lane,
4. prove response covariance or emit explicit obstruction,
5. enforce final trichotomy:
   - equivalence,
   - obstruction,
   - discard.

## Minimal Lean Skeleton (Schematic)

```lean
structure ReferenceState (α : Type _) where
  owner_surface : α
  assumptions   : List String

structure GaugeTransform (α : Type _) where
  map : α → α
  admissible : Prop

structure ProbeFamily (α : Type _) where
  probe : List (α → ℝ)

structure SpectralResponse (α : Type _) where
  reference : ReferenceState α
  gauge     : GaugeTransform α
  probes    : ProbeFamily α

/-- Closure outcome for bridge candidates. -/
inductive BridgeOutcome
  | equivalence
  | obstruction (residue : String)
  | discard (reason : String)
```

The point is not this exact syntax, but the typed discipline:
response is always measured relative to a reference state and gauge class,
never as free-floating narrative.

## Closing Statement

The alignment is now explicit:

- spectroscopy gives the methodological grammar,
- repo architecture gives the typed implementation surface,
- Lean kernel gives closure authority.

From here, "considering alignment" becomes executable doctrine rather than
interpretive prose.
