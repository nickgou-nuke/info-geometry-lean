# Executable mass-spectrometry validation contract

Intake: the source audit of commit `2d3a6ed286fde7098d152b83c9c75580b98865d0`
and the request to implement the missing Lean pipeline pieces. The audit
separates mathematical specifications from executable input validation.

## Ground-truth contract

- `StochasticGrammar` permits row deficits; `terminalWeight` is that deficit.
  `NormalizedGrammar` requires every row of a strict finite DAG to sum to one,
  which is impossible on a nonempty carrier. Preserve the legacy API, prove
  this obstruction, and provide an absorbing completion on `Fin (n + 1)`.
  Reuse `StochasticTransitionMatrix`; its absorbing self-loop is not a cleavage.
- Raw candidate data use `Fin`, `Bool`, `Nat`, and exact `Rat`, with no proof
  fields. A computable decision procedure checks positive peak/fragment
  masses, nonnegative intensity, rank and mass decrease on edges, exact
  doubly-stochastic assignment, and supported substochastic transition weights
  at each of finitely many supplied condition indices.
- Acceptance constructs the existing `ValuedFragmentationDAG`, `Spectrum`,
  `StochasticGrammar`, and `FiniteValuedFragmentationModel` using rational to
  real casts. A caller-supplied condition selector chooses a checked kernel;
  this does not establish empirical validity at unobserved collision energies.
- Numerical assignment tolerances, peak-mass fit, elemental/charge balance,
  and finite observed round-trip residuals must be checked as explicit,
  separately named predicates. Approximate balance is not exact Birkhoff
  membership. Supplied composition labels are not a chemical graph validator.

The mathematical owners are `FragmentationDAG`, `ValuedFragmentationDAG`,
`PeakSpectrum`, `StochasticFragmentGrammar`, `BirkhoffAssignment`, `FiniteModel`,
and `VerifiedInferenceArchitecture`. Real-valued interpretation is a proof
layer; the acceptance Boolean operates entirely on exact finite input data.

## Scope boundary

This work does not establish learned reconstruction accuracy, simulator
identifiability, GPU floating-point refinement, chemical valence/aromaticity,
raw instrument parsing, regulatory certification, or a cryptographic signature.
Executable acceptance and Lean proof elaboration are distinct operations.

## Library and executable entry points

- `AbsorbingFragmentGrammar`: terminal completion on `Fin (n+1)`; legacy
  `NormalizedGrammar` remains source compatible, with its nonempty obstruction
  now proved explicitly.
- `RationalCandidate.check`: exact Boolean acceptance of proof-free finite data.
  `validate` returns the accepted input as a subtype or `none`.
  `toModel` interprets accepted data; `check_sound` proves the existing
  `IsStructurallyAdmissible` property.
- `RationalSinkhorn.iterate`: bounded executable row/column normalization.
  The rational steps commute with the existing real specification under its
  positivity hypotheses. Nonnegativity is preserved. Check the output with
  `NumericalValidation.checkAssignment`; only zero residual entails exact
  Birkhoff membership. There is no guarantee that a finite iteration count
  reaches exact balance; the bounded iterator itself terminates.
- `CandidateChemistry.check`: per-edge species-count and charge balance.
  `checkNeutralLosses` additionally checks zero loss charge. `checkMassModel`
  explicitly links the candidate masses to a supplied additive species mass
  table; `fragment_mass_balance` then proves equality with the declared loss
  mass. Graph-derived inventories and physical atomic masses remain external.
- `NumericalValidation`: separate mass-fit, assignment-tolerance, and finite
  observed residual checks, with rational-to-real soundness theorems.
- `ValidatorIO`: shape-checked JSON parsing and `checkJson`. Its soundness
  theorem is about the parsed candidate. It does not authenticate the file.

The CLI performs **structural validation only**. The chemistry, residual,
Sinkhorn and absorbing-completion operations above are Lean library APIs;
they are not silently run or reported as approved by this command.

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.MassSpectrometry.ValidatorIO
lake env lean --run lean/Examples/MassSpectrometry/Validate.lean \
  examples/mass-spectrometry/two-fragment.json
```

Expected output:

```json
{"structurallyAccepted":true,"arithmetic":"exact-rational"}
```

Exit status: 0 accepted, 1 structurally rejected, 2 input/usage error. This is an
executable decision backed by a general soundness theorem, not a per-input
serialized proof certificate or a kernel invocation on every CLI execution.

JSON requires `n`, `k`, vectors `peakMass`, `intensity`, `rank`, `fragmentMass`,
square matrices `edge`, `assignment`, and a `k`-element array of square `weight`
matrices. Rational values are strings such as `"60"` or `"3/4"`; denominators
must be positive. No floating-point rounding, default padding or zero-denominator
repair is performed. Both dimensions must be positive to pass validation.
Masses must already use consistent units and charge/adduct conventions.

To interpret the table, supply `select : CollisionCondition → Fin k` explicitly.
A constant selector uses one checked condition everywhere; it does not prove
that the chosen kernel describes other experimental conditions.

## Verification

The six new owner modules build successfully in Lean **4.34.1**, using the
repository's exact Mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`.
All **32 new named theorems** were inspected with `#print axioms`; their combined
footprint is only `propext`, `Classical.choice`, and `Quot.sound`.

**29 kernel regression examples** pass in `ValidationChecks.lean`, including a
nonempty accepted model, cycle/rank/mass/weight/assignment rejection, chemistry
and mass-model checks, approximate versus exact assignment, and finite Sinkhorn
results. These use kernel reduction, not native proof evaluation. String parsing
is tested separately at runtime in `JsonChecks.lean`.

```sh
lake env lean lean/Examples/MassSpectrometry/ValidationChecks.lean
lake env lean --run lean/Examples/MassSpectrometry/JsonChecks.lean \
  examples/mass-spectrometry/two-fragment.json
```

**14 executable JSON cases** pass, including a valid two-condition chain,
invalid structural data, ragged arrays, missing fields, malformed JSON,
zero/negative denominators, and numeric values where rational strings are
required. The actual CLI was also run on valid, rejected, and malformed input:
its JSON results and exit codes **0, 1, and 2** all match the documented contract.
Independent acceptance passed for this finite validation scope.

The normal repository build was attempted through the maintained locked wrapper
and stops at the existing missing `external_refs/atlas-lean` package. The checks
above use an isolated verification project loading the unchanged repository
source with the same Lean/Mathlib pins and the shared build lock. No dependency
pins or existing owners were modified. This is targeted verification of the new
modules and their imported dependencies, not a claim that the entire repository
or every pre-existing mass-spectrometry module was rebuilt.

No new-owner compiler warnings. Replayed dependency warnings remain unchanged.
The staged proof-policy gate passes. The semantic scanner's sole `no_hyp_use`
warning on `RationalCandidate.realAssignment_soft` is a reviewed lexical false
positive: all three proof branches use the hypothesis. Independent source audit
and acceptance roles reviewed scope and nonvacuity.
