# Mass-spectrometry experimental evidence contracts

## Scope and owner reuse

Additive modules, initially based on main 2d3a6ed286fde7098d152b83c9c75580b98865d0.
Existing Peak, Spectrum, CanonicalSpectrum, CollisionCondition, MolecularGraph,
FragmentationDAG, StochasticGrammar, NormalizedGrammar, IsSoftAssignment and
MultiEnergyForwardModel definitions are not modified or redefined.

The intended dependency order is:

    measured coordinates and acquisition metadata
      -> explicit ion interpretation / canonical spectrum
      -> rectangular partial assignment and terminating fragment grammar
      -> finite candidate experiment
      -> quantitative implementation error budget
      -> uniqueness up to an explicitly chosen chemical equivalence

## Observation semantics

ExperimentalObservation retains the original collision-energy unit and signed
precursor charge. Its legacy CollisionCondition view requires a separately
supplied calibrated energy and exposes charge magnitude only. This conversion
is deliberately lossy; the original record must be retained. No formula for
converting normalized collision energy, voltage or vendor settings to eV is
asserted.

An IonInterpretation declares nonzero signed charge z and a real ionMassOffset:

    neutralMass(mz) = |z| mz - ionMassOffset
    mzOfNeutralMass(m) = (m + ionMassOffset) / |z|

Both round trips and strict-order equivalence under ONE fixed interpretation
are proved. Different charge interpretations may reverse the order: the
fixture compares m/z 100 at charge 1 with m/z 75 at charge 2. Neutral-mass
positivity is required when constructing an existing Peak; intensities and
index counts are preserved. No isotope masses or adduct constants are invented.

VariableSpectrum is the native dependent pair `Sigma n, Spectrum n`. Each scan
can have a different length. Canonicalization reuses the existing sorting
implementation and length theorem. Source checksum and processing identifiers
are metadata, not proofs of parser correctness or cryptographic provenance.

RationalPeakRecord has an executable exact positivity checker with a soundness
and completeness theorem, and casts accepted rational values to the existing
real-valued Peak. This is not an mzML/RAW/MGF parser, a validated measurement,
or a proof about floating-point decoding.

## Partial assignment

PartialPeakAssignment has independent row and column index types and capacity
vectors. Its nonnegative matrix has row/column sums at most those capacities.
Nonnegativity of unmatched and undetected capacity is derived. Exact total
accounting is:

    total unmatched peaks - total undetected fragments
      = total peak capacity - total fragment capacity.

An all-unmatched plan is constructed. An existing square Birkhoff certificate
maps to a unit-capacity plan with zero residual. Conversely, zero residuals
imply the existing IsSoftAssignment only in the square unit-capacity case.
No transportation optimizer, matching algorithm, uniqueness, or calibrated
intensity model is implied. Peaks and fragment states are not forced into a
single common index set.

## Termination

Any nonempty finite rank-decreasing FragmentationDAG has a terminal vertex.
Its StochasticGrammar row is zero there, and its terminalWeight is one. The
existing NormalizedGrammar on only strict DAG edges is therefore uninhabited
when the vertex set is nonempty. The zero-vertex exception is retained.

The explicit Option-indexed absorbingCompletion has nonnegative entries and
all row sums exactly one. `none` is absorbing; `some u -> some v` preserves the
original weight and rank-decrease law. The completed carrier is NOT claimed to
be a DAG (its absorbing state has a self-loop). No eventual-absorption time or
quantitative Markov convergence result is claimed here.

## Finite conditions and robust identification

restrictConditions reuses MultiEnergyForwardModel on the subtype of a Finset.
Its exact observational equivalence is equality at precisely those conditions.
Adding conditions refines that equivalence. The native chemical quotient and
injectivity theorem are reused on the restricted model.

For a finite candidate type, an existing global IdentifiableUpTo certificate
implies the existence of a finite identifying condition set. The proof selects
one witness per inequivalent ordered pair. It does not establish global
separation for a simulator, optimize experiment cost, or claim that one
condition separates every pair.

In any chosen pseudometric observation carrier, if every chemically distinct
candidate pair is separated at one measured condition by MORE THAN 2 epsilon,
then two candidates fitting all sampled observations within epsilon must be
chemically equivalent. This conclusion is a quotient-class uniqueness theorem,
not uniqueness of an atom labelling. At exactly 2 epsilon, closed error balls
may intersect; a concrete midpoint counterexample is included.

A second simulator G may be used numerically when its deviation from reference
F is bounded by delta. Its fit radius epsilon becomes epsilon + delta in F,
so the required margin is greater than 2(epsilon + delta). The
UniformErrorBound contract feeds this theorem directly. No sampling test is
promoted to a uniform error proof.

## Error composition

UniformErrorBound augments the existing exact KernelRefinement concept without
redefining it or importing the unrelated GPU/Clifford dependency graph. It uses
Mathlib PseudoMetricSpace and LipschitzWith. Two maps compose with error bound

    e2 + L * e1,

where L is a certified Lipschitz constant of the downstream specification.
Zero error implies function equality only in a MetricSpace. Three explicitly
bounded intermediate deviations add by the triangle inequality. The input
bounds, metrics, model discrepancy and physical validity remain obligations.

## Molecular connection

AcquisitionForwardModel uses actual MolecularGraph values, typed
AcquisitionCondition inputs, and variable-length existing Spectrum outputs.
candidateModel selects a candidate-indexed family and an explicit feature map.
The supplied chemical setoid is pulled back to candidate indices. Proven
simulator invariance is transported through the feature map; no invariance or
feature injectivity is assumed implicitly. The finite-experiment and robust
uniqueness theorems are specialized to this carrier.

## Verification

Acceptance requires compiling all seven new modules and their unchanged source
closure against the root's pinned Lean and Mathlib, followed by the existing
native imported-environment declaration audit. The dedicated workflow performs
this scoped check, not the root package build. It rejects new unsafe/partial
declarations and any transitive axiom outside propext, Classical.choice and
Quot.sound. There are no changes to dependency pins, existing theorem owners,
umbrella imports, parsers, training code or UI.

Build target with root dependencies available:

    python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
      InfoGeometry.MassSpectrometry.ExperimentalEvidenceAudit

This source contract does not itself constitute a successful verification run.
