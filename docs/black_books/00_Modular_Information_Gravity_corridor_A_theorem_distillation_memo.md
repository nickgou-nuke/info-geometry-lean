# Corridor A theorem-distillation memo

Corridor:
- RedLine / RN / modular potential / KL / Massieu

Black-book source shards reviewed:
- `00a_modular_information_gravity_apotheosis_and_redline.md`
- `00f_spacetime_coordinateless_cstar_bures_and_emergent_gravity.md`
- `00h_split_cl44_tkk_kkt_and_fisher_bridge.md`
- `00k_operator_moment_map_grand_canonical_operator_ensemble.md`
- `00ae_negative_logarithm_dictionary_and_modular_time_emergence.md`

Primary repo surfaces checked:
- `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
- `lean/InfoGeometry/Canonical/RelativeModularOperator.lean`
- `lean/InfoGeometry/Canonical/CertifiedModularReduction.lean`
- `lean/InfoGeometry/Canonical/OperatorialHessianBridge.lean`
- `lean/InfoGeometry/GrandCanonical/Core.lean`

## 1. Core symbolic claims in Corridor A

Recurring claims in the source shards:

1. The negative logarithmic Radon–Nikodym derivative is the foundational redline.
2. The modular Hamiltonian is the negative logarithm of the modular operator.
3. KL divergence / free energy / Massieu potential / Gibbs factors belong to one common logarithmic generating corridor.
4. The inverse exponential chart of the modular operator is the surprisal operator.
5. Spacetime and gravity language should be secondary to operator-algebraic / KMS / modular flow language.
6. A scalar logarithmic readout should arise only after an operatorial transport/modular layer exists.

These symbolic claims are not all equally owned by the repo. Some are already theorem-backed; some remain synthesis language.

## 2. What is already owner-backed in the repo

### A. RN / projective / modular-potential lane is genuinely owned

`RelativePotentialCore.lean` already owns:
- `representativeRelativeDensity`
- `representativeRelativeLogDensity`
- `representativeModularPotential`
- `relativeDensity`
- `relativeLogDensity`
- `relativeModularPotential`

And proves the exact logarithmic identities:
- relative density = exponential of relative log density
- modular potential = negative relative log density
- cocycle laws under composition
- representative/projective scale-shift laws via canonical gauge normalization

So the following black-book sentence is basically repo-native already:
- “the negative logarithmic Radon–Nikodym derivative defines the modular potential on the projective count/ray corridor.”

### B. The finite operator owner exists

`RelativeModularOperator.lean` already owns:
- `relativeModularOperator`
- diagonal entries recover `relativeDensity`
- `relativeLogDensity_eq_log_relativeModularOperator_diag`
- `relativeModularPotential_eq_neg_log_relativeModularOperator_diag`

So the finite commuting operator shadow is already precise:
- the modular operator is the diagonal operator with relative density on the diagonal;
- taking `log` on the diagonal recovers the relative log-density;
- taking `-log` on the diagonal recovers the modular potential.

This is the strongest currently owned bridge behind the “universal dictionary of the negative logarithm” rhetoric.

### C. Support-restricted modular logarithm is owned on the regular lane

`CertifiedModularReduction.lean` already owns:
- `Preg`, `Pzero`
- `Δreg`
- `Kreg := -logOn(logDomain)`
- `Kambient`
- support/defect theorems for the regular lane
- `no_log_on_zero_sector`

So the following statement is repo-faithful:
- “the logarithm of the modular operator is lawful only on the regular support-restricted lane; defect support is excluded.”

This is stronger and more precise than the black-book rhetoric of taking `-log Δ` globally.

### D. Scalar logarithmic readout exists at first derivative order

`OperatorialHessianBridge.lean` already owns:
- `scalarLogReadout (ω, X, A, t) = log ω(transportedObservable X A t)`
- `hasDerivAt_scalarLogReadout_zero`

So the first scalar log-readout layer exists.
This is important because the black-book source repeatedly asks for logarithmic generating/readout structure in the operatorial lane.

### E. `ln Z` and chemical-potential Massieu structure are already owned in finite thermodynamics

`GrandCanonical/Core.lean` already owns:
- canonical `partition`, `potential = log Z`
- grand-canonical `shiftedEnergy = E - μN`
- `partitionGC`
- `potentialGC = log Z(β, μ)`
- `∂β potentialGC = - mean(E - μN)`
- `∂μ potentialGC = β meanNumber`

So the following is already precise in the repo:
- `ln Z` is not merely rhetoric; it is formalized as `potential` / `potentialGC`.
- the grand-canonical chemical-potential lane is real and theorem-backed.

## 3. What is only partially owned / still requires theorem work

### A. “KL divergence as the energy with temperature regularization”

Partially supported:
- finite thermodynamic owner surfaces (`potential`, `potentialGC`, Hessian/variance identities)
- projective/operator modular lane

Still missing as one unified theorem surface:
- an explicit owner theorem identifying a Type-III/support-restricted modular free-energy readout with an Araki/KL divergence object in the exact black-book wording.

Status:
- conceptually aligned,
- not yet fully unified in one theorem family.

### B. “Modular Hamiltonian as the operatorial lift of surprisal”

Finite/commuting shadow:
- yes, essentially owned through `relativeModularPotential_eq_neg_log_relativeModularOperator_diag`

Infinite-dimensional/support-restricted general owner:
- partly owned through `CertifiedModularReduction.Kreg`, `Kambient`, and `ModularHamiltonianPregSupportBridge`
- but the complete scalar surprisal/free-energy reading remains partially bridge-level rather than one final owner theorem.

Status:
- strong corridor support,
- still not a single finished theorem package.

### C. “Thermal time / spacetime emergence / gravity is geometry of surprisal”

This remains black-book/capstone language.
The repo has ingredients:
- modular flow / support-restricted Hamiltonian
- scalar log-readout first derivative
- operatorial Lie transport

But it does not yet own a theorem saying the cosmological/gravitational interpretation is derived.

Status:
- not owner-closed,
- should remain capstone/proposal language.

### D. Second scalar derivative / norm / free-energy curvature

Still missing as a fully closed scalar bridge:
- second derivative of `scalarLogReadout`
- theorem identifying it with operatorial Hessian / Fisher / free-energy curvature
- positivity theorem for that scalar second variation

This is the main missing scalar bridge debt in Corridor A.

## 4. Owner-level statements we can already safely extract

These are safe, repo-faithful statements:

1. The projective relative-potential corridor owns the negative logarithmic relative-density readout:
   - `relativeModularPotential = - relativeLogDensity`.

2. The finite commuting operator corridor owns the diagonal modular operator and its logarithmic readout:
   - `relativeLogDensity = log diag(Δ)`
   - `relativeModularPotential = -log diag(Δ)`.

3. The support-restricted modular corridor owns the regular logarithmic generator only on `Preg`:
   - `Kreg := -logOn(logDomain)`
   - no logarithm is admitted on the defect lane `Pzero`.

4. The finite grand-canonical corridor owns `ln Z` and the `μ`-conjugate count readout:
   - `potentialGC = log Z(β, μ)`
   - `∂μ potentialGC = β meanNumber`.

5. The operatorial scalar log-readout exists at first derivative order:
   - `scalarLogReadout`
   - first derivative at zero equals the expectation of the first information variation under normalization.

## 5. Statements that must remain marked as debt/proposal

These should not yet be promoted as already proved:

1. A single theorem identifying KL divergence, free energy, Massieu potential, surprisal, and support-restricted modular Hamiltonian in full Type III generality.
2. A complete second-derivative scalar log-readout theorem.
3. Positivity/nonnegativity of that scalar second variation in the operatorial lane.
4. Any claim that cosmological gravity or spacetime emergence is already theorem-derived from these surfaces.

## 6. Best next theorem targets for Corridor A

Priority theorem targets:

1. Second derivative of scalar log-readout
- extend `OperatorialHessianBridge.lean`
- prove the second derivative formula for `scalarLogReadout`
- isolate exact domain/positivity hypotheses

2. Bridge to existing operatorial Hessian surfaces
- identify the second scalar log-readout with operatorial Lie-Hessian / operatorial Hessian evaluation under a chosen state/readout.

3. Type-III / support-restricted free-energy readout packaging
- if possible, add a theorem/bridge file connecting:
  - `CertifiedModularReduction.Kreg / Kambient`
  - scalar log-generating readout
  - modular surprisal/free-energy language
without overclaiming an already completed Araki package.

## 7. Pauli-style closure status for Corridor A

ROLE:
- owner + translator corridor, with some capstone overgrowth in the black-book prose

SEMANTIC_FIDELITY:
- high for RN/modular/logarithmic redline claims
- medium for cosmological/gravity/surprisal unification rhetoric

THEOREM_STRENGTH:
- high for finite projective/operator/log-partition owners
- medium for support-restricted operatorial scalar bridges
- low for cosmological capstone claims as currently formalized

CLOSURE_STRENGTH:
- owner-closed on the finite projective/modular/log-partition lane
- bridge-valid-but-not-closed on the support-restricted scalar free-energy lane
- capstone-only on gravity/emergence rhetoric

PROMOTION_ALLOWED:
- yes for the owner statements listed in section 4
- no for the capstone statements listed in section 5

## 8. Recommended extraction order inside Corridor A

Extract in this order:

1. `00a` -> redline dictionary (but filter out triumphalist and cosmological overclaim)
2. `00k` -> operator moment-map / grand-canonical operator ensemble claims
3. `00h` -> Massieu / Hessian / Fisher links
4. `00f` -> coordinateless algebra/state rhetoric, but only where it matches existing operator/state/KMS surfaces
5. `00ae` -> modular time / negative-log dictionary as capstone notes, not owner facts

This keeps the theorem factory anchored to currently real repo surfaces while preserving the black-book pressure for later deeper closure.
