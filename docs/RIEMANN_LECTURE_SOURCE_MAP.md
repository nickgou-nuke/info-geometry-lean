# Riemann lecture: source-backed dependency map

Source audit: 2026-09-16, working tree `/home/goutev/info-geometry-lean`.
Scope: the supplied Sarnak transcript and the subsequent Maass/conductor and
split-lightcone interpretations. This is a mathematical dependency roadmap,
not a reconstruction of private reasoning and not a proof of RH or GRH.

## Search and evidence discipline

The first recursive lexical pass examined 24,800 Lean source paths respecting
ignore rules. It found matching files in native `lean/`, legacy `proofs/`,
external sources, and other folders. A second, no-ignore inventory includes
external references and archives, excluding Git internals, build caches,
virtual environments, and node modules. Selected pinned Mathlib owners were
read separately. Counts of keyword matches are not counts of relevant theorems.

The session inventory is `/tmp/rh_lecture_inventory.json`; its generator is
`/tmp/rh_lecture_inventory.py`. These are temporary navigation artifacts, not
kernel certificates. The inventory records source hashes, imports, declaration
starts, topic matches, and lexical proof-debt matches. Comment matches are not
proof defects. Native module import closure is not declaration-level dependency
closure. The completed no-ignore pass examined 52,333 Lean paths, with topic
matches in 2,838 native `lean/` files, 266 legacy files, 526 external files,
and 3,641 other paths (including archives). Those paths are not necessarily
distinct mathematical implementations.

Recursive native import closures contained 42 modules for the evidence
corridor, 327 for the geometric/dynamical corridor, 9 for the abstract idele
symmetry layer, 6 for the finite cyclotomic Galois tower, 284 for the log-cylinder
Klein glide, 10 for the entire-Xi Schwarz bridge, and 3 for finite Weil
positivity. These counts include the seed and exclude external/Mathlib imports.

The configured Arango hive endpoint refused a connection, including the host
retry. Declaration DAG artifacts requested by context preflight were absent.
Accordingly, conclusions below come from source inspection, not an invented
Arango query result. No external dependency or pin was changed.

Existing maps to reuse:

- `lean/InfoGeometry/Arithmetic/RiemannZetaEvidenceLogosMap.lean`
- `lean/InfoGeometry/Arithmetic/RiemannZetaExtendedEvidenceLogosMap.lean`
- `lean/InfoGeometry/Arithmetic/RiemannZetaEvidenceCorridor.lean`
- `lean/InfoGeometry/Arithmetic/RiemannZetaGeometricDynamicsCorridor.lean`
- `docs/physics-riemann-hypothesis-theorem-ladder.md`
- `docs/centered-zeta-trifactor-corridor-map.md`

The Logos maps already distinguish theorem, conditional, structural, numerical,
and open-debt entries. Their owner-name audits check declaration existence, not
whether a declaration proves all claims suggested by its name. Their ordered
lists must not be read as automatic logical implications.

## Lecture order and actual owners

Paths in this table are relative to `lean/InfoGeometry/` unless stated otherwise.
“Source theorem” means an inspected theorem body, not a new compilation claim.

| Lecture archetype | Existing owner / declaration | Established scope and missing step |
|---|---|---|
| 02:00: Dirichlet sum and Euler product | `Arithmetic/RiemannZetaEvidenceCorridor.lean`: `primeEulerProduct_eq_zeta`, `dirichletSeries_eq_zeta` | Actual Mathlib zeta; hypotheses `1 < s.re` remain essential. |
| 03:00: continuation and completion | Same owner: `riemannZeta_differentiable_off_one`, `completed_zeta_functional_equation`; `Arithmetic/ActualRiemannXiEntireBridge.lean` | Pole-removed entire Xi is separate from the unregularized product definition. |
| 04:00: symmetry line | Same corridor: `critical_line_fixed_locus`; `Arithmetic/ActualRiemannXiEntireSchwarzBridge.lean`: `entireRiemannXi_conj` | Reflection fixes the critical line; a reflection-invariant zero set need not lie in its fixed locus. |
| 05:00–09:00: certifying individual zeros | New local lemma in the Schwarz owner, described below | Requires a unique zero in an invariant region. No certified contour count or actual Riemann–Siegel remainder bound is supplied. |
| 09:00–12:00: primes and explicit formula | `Arithmetic/ActualRiemannZetaVonMangoldtBridge.lean`: `vonMangoldt_LSeries_eq_actualRiemannZetaLogDerivative` | Actual logarithmic derivative for `Re(s)>1`; not the full prime-counting explicit formula. |
| 17:00–24:00: Dedekind zeta, discriminants, GRH | Pinned Mathlib `NumberTheory/NumberField/DedekindZeta.lean`; native finite cyclotomic owners | Ideal-norm series and class-number residue infrastructure exist. No general GRH ramification bound was located in the inspected owners. |
| 25:00–31:00: GRH applications | Searches for the named applications | No corresponding closed owner located for the lecture's Miller/AKS, André–Oort, Hooley, or random-polynomial implications. This is a search result, not a proof of repository-wide absence. |
| 31:00–36:00: finite fields, Frobenius, cohomology, monodromy | Numerous generic Frobenius/cohomology/monodromy hits | These do not establish the Weil conjectures or Deligne's purity theorem. A matching complete bridge was not located. |
| 38:00–42:00: additive versus multiplicative structures | Pinned Mathlib Gaussian Poisson summation; native Mellin/Schwarz and Euler-product owners | Both mathematical ingredients exist; their mere coexistence is not a positive explicit-formula pairing. |
| 39:00–42:00: why symmetry is insufficient | `Arithmetic/ZetaSymmetryHeuristicComplement.lean`: `even_symmetry_allows_off_axis_zero_pair` | Concrete even polynomial with off-axis zeros; reusable obstruction to symmetry-only RH arguments. |
| 44:00–46:00: Liouville cancellation | `Arithmetic/LiouvilleParity.lean` | Exact multiplicative/parity facts. No square-root cancellation estimate was located. |
| 46:00–49:00: spectral statistics | `Analysis/KatzSarnakDensity.lean`; finite spectral packets | Density-profile identities, not convergence of zeta-zero statistics to GUE. |
| 50:00–54:00: adeles, ideles, singular quotient, trace | `Arithmetic/IdeleClassZetaSymmetry.lean`; pinned Mathlib `NumberTheory/NumberField/AdeleRing.lean` | Native abstract symmetry layer and genuine Mathlib adele carrier are distinct. A concrete Connes–Meyer spectral realization is not supplied by the abstract layer. |
| 54:00–56:00: discriminants and towers | `Arithmetic/PrimeCyclotomicGaloisGroupTower.lean`: `gal6EquivUnits`, `gal6To2_unit_readback`, etc. | Genuine finite cyclotomic Galois equivalences and transported maps. Not a Golod–Shafarevich tower or a GRH discriminant inequality. |
| 56:00–end: high-rank Maass forms and Archimedean complexity | `Automorphic/LFunctionResonance.lean`: `AutomorphicOperatorIntertwining`, `boundaryProjector_commutes` | Abstract linear intertwining data; the header explicitly excludes Euler products, functional equations and spectral zero theorems. No concrete Maass analytic-conductor owner was located. |

## Branching dependency order, not a forced single chain

Arrows below mean explicit mathematical prerequisites. Dashed arrows denote
missing theorems, not implemented implications. Sibling branches are incomparable
until an actual bridge is proved. The reflexive transitive closure of this
acyclic roadmap is the intended dependency poset; it is not asserted to be the
kernel declaration DAG or a physical causal order.

```text
integer factorization -> Euler product --+--> actual zeta on Re(s)>1
Dirichlet series ------------------------+             |
                                                      +-> Mangoldt logarithmic derivative
                                                      +-> reciprocal via Möbius L-series
                                                      +-> real beta>1 thermodynamic readout

Poisson / Mellin infrastructure -> completed functional equation
Mellin conjugation -------------> actual Schwarz symmetry
                                 |                 |
                                 +--> reflected Xi-zero orbits
                                               |
                      invariant region + unique zero
                                               |
                                               +--> that zero has Re(s)=1/2

critical-line fixed locus -> Cayley unit-circle reformulation
log-cylinder coordinates -> Klein glide/deck relations
split/Krein algebra ------> operator identities and conditional transport
finite cyclotomic fields -> Galois/unit equivalences -> finite inverse tower
actual adele carrier -----> [concrete idele quotient / compatible action needed]

Euler arithmetic + analytic test spaces + spectral action
                 - - -> exact explicit formula for actual zeta zeros
                 - - -> the required positivity and zero identification
                 - - -> RH (or a specified GRH family)

automorphic representation + local factors + spectral parameters
                 - - -> analytic conductor with explicit normalization
                 - - -> a precisely stated high-rank conditional estimate
                 - - -> a meaningful GRH stress test
```

Klein seams, Apollonius coordinates and metriplectic flows are the user's
additional comparison branches, not constructions asserted in the supplied
Sarnak lecture. No arrow from a seam or a balance point to all zeta zeros has
been established.

## Scope traps found by opening the files

- `Arithmetic/ExplicitFormula.lean`: `explicitFormulaFromRH` receives
  `hformula`; `hadamard_product_xi` and `log_derivative_xi` receive their claimed
  identities as hypotheses. Its `N_function` is a prescribed expression, not
  an actual zero-counting function. These are not proofs of the analytic
  explicit formula or Riemann–von Mangoldt zero counting.
- `Arithmetic/IdeleClassZetaSymmetry.lean`: `IdeleClassLayer` is abstract.
  `StrictUnitaryBinding` is an additional premise of `no_off_critical_zero`.
  `RationalIdeleClassDecomposition` bundles supplied inverse maps; it does not
  construct the quotient of Mathlib adeles by rational units.
- `Arithmetic/PrimeCyclotomicGaloisGroupTower.lean`: transition maps are
  transported through unit-group equivalences. Compatibility with literal
  restriction along selected field embeddings still needs its own proof.
- `Quantum/ConnesAdeleTrace.lean`: the finite register does not require its
  listed points to be actual zeta zeros; independent test-function transforms
  do not establish Fourier duality.
- `Spectral/WeilPositivityCriterion.lean`: finite arithmetic-comb positivity
  under explicit sign hypotheses, not the complete analytic Weil criterion.
- `Arithmetic/FiniteWeilMangoldtQuadraticFormBridge.lean`: Hermitian symmetry
  and real diagonal values do not imply positive semidefiniteness.
- `Arithmetic/ConnesConsaniAdelicMotivesCapstone.lean`: real scaling and an
  absorption parameter are not an adelic quotient or a motivic cohomology.
- `Arithmetic/AdelicHeckeSatakeLFunctionCapstone.lean`: local polynomial
  algebra and norm estimates with parameter assumptions are not a proved
  Satake correspondence or Ramanujan theorem.
- `Analysis/KatzSarnakDensity.lean`: formulas for profiles and their values
  are not a zero-statistics limiting theorem.
- `Omega/CircleDimension/RiemannSiegelGabckeLocalZeroStability.lean`:
  the inspected local model is affine, not the actual Riemann–Siegel formula.
- `Canonical/TensorTowerColimit.lean`: compatible-map transport must not be
  promoted to spectral convergence, completeness, or positivity without the
  relevant additional data and proofs.

External `external_refs/atlas-lean/Atlas/NumberTheoryI/code/Adeles.lean` and
`Ideles.lean` use genuine adelic carriers but contain explicit `sorry` debt.
Their presence is useful navigation evidence, not a verified native dependency.

## The Maass/conductor proposal: retain arithmetic, reject relabeling

The supplied `LFunction` record contains two real numbers, not an L-function.
Its proposed `MaassForm` adds only that one number equals one; there is no
automorphic function, Laplace/Casimir eigencondition, Hecke data, or cusp
condition. The product identity at finite conductor one is valid algebra but
does not implement those missing structures.

`SatisfiesGRHSparsity C count` defines a particular logarithmic bound.
Its proposed violation theorem only negates that bound. It says nothing about
GRH unless a separately proved implication from a precisely defined GRH to
that exact bound is provided. At `X=1` the proposed bound already requires
`count 1 ≤ 0`. There is no rank parameter, spectral window, normalization, or
specified family. The transcript supplies none of the missing quantitative
theorem.

Do not conflate growth of a conductor cutoff at fixed rank with the lecture's
high-rank, low-complexity question. Actual counting results specify families
and hypotheses; see Brumley–Milićević,
[Counting cusp forms by analytic conductor](https://arxiv.org/abs/1805.00633),
which proves conductor-ordered counting asymptotics with stated restrictions,
and Müller's [Weyl's law in the theory of automorphic forms](https://arxiv.org/abs/0710.2319).
Neither citation supplies the proposed `GRH -> count(X) ≤ C log X` theorem.

Motivic L-functions also have Archimedean factors. “Motivic versus Maass”
must not be encoded as “finite complexity versus infinite-place complexity.”
No new misleading `MaassArchimedeanComplexity` record was introduced.

## The split-lightcone / HDKKC proposal: native owners and obstructions

| Algebraic ingredient | Reuse owner | Precise scope |
|---|---|---|
| Left/right coordinates and neutral quadratic form | `Arithmetic/HestenesKreinPrimeThermodynamics.lean`, `SplitComplex.leftPart`, `rightPart`, `norm_reconstruct` | Reconstructed coordinates have split norm `u*v`. This is a quadratic readout, not by itself a full spectral triple. |
| Reciprocal squeeze | `Krein/SplitBoost.lean`, `boost_leftPart_mul`, `boost_rightPart_mul`, `boost_norm_preserved` | Actual boost action scales by `exp(t)` and `exp(-t)` and preserves the split norm. |
| Doubled carrier and swap | `Krein/DoubledSpace.lean`, `modular_j_involution`; `Canonical/KreinParaKahlerTwinWaveBridge.lean`, `paraSwap_sq`, `toDoubled_paraSwap` | Existing involutions and a concrete intertwining map; do not duplicate them as `CausalTwin`. |
| Genuine Hodge–Dirac square | `HodgeCohomology/KreinHodgeDirac.lean`, `dirac_sq_eq_laplacian` | Requires a nilpotent differential, an adjoint codifferential, and a nondegenerate pairing. |
| Chiral block decomposition | `Canonical/ChiralHodgeDiracBlockBridge.lean` | Existing projector, odd-operator and off-diagonal factorization infrastructure. |
| Finite Cantor/null readout | `Canonical/CantorSplitNullBridge.lean`, `cantor_split_null_bridge_packet` | Finite addresses select native Zorn null generators; not a fractal detector propagation theorem. |
| Klein action | `Quantum/NeutralKreinKleinAction.lean`, `affineGlide_conjugates_winding_inverse` | Algebraic deck relation, separately from topological quotient identification. |
| Apollonius flow | `Canonical/ApolloniusRapidityFlowBridge.lean`, `flowMap_apollonius_zero_iff` | Invariant layer and preservation statements; explicitly no identification with zeta zeros. |

For the proposed two-coordinate maps, `D S_c = S_(1/c) D` is conjugation
to the inverse, not anticommutation `D S_c = -S_c D`. The relation alone does
not prove a faithful infinite dihedral action: at `c=1`, the squeeze is the
identity; at `c=-1` it has order two. Infinite order and faithfulness require
additional proofs and restrictions on the selected scale.

The diagonal is fixed by the swap, but is not invariant under general
squeezing: `S_2(1,1)=(2,1/2)`. Thus the claimed common self-dual invariant
space is false as stated. The union of the two null axes is preserved by
both maps; the swap exchanges the individual axes. The entire plane is also
invariant. None of this identifies a zeta-zero set.

An involution squared is the identity, not automatically a geometric
Laplacian. The proposed file defines no Cantor set, iterated-function system,
limit construction, coordinate algebra representation, or analytic spectral
triple. Even the existing `Quantum/SpectralTripleApollonius.lean` bundles
algebraic spinor/operator conditions rather than proving all analytic
spectral-triple requirements. No duplicate `CantorHDKKC.lean` was added.

## Andreev, quadratic wells, and the missing zero-locus bridge

The latest `AndreevMetriplecticSeam` proposal also duplicates existing owners:

- `OperatorAlgebra/AndreevBoundary.lean`: `andreevFlipLinear_sq` and finite
  diagonal/imbalance fixed-point theorems.
- `Canonical/BipolarTwoSheetCore.lean`: `sheetToAndreevChannel_swap` connects
  the existing sheet labels to the actual channel-flip interface.
- `Arithmetic/RiemannApolloniusLocalLyapunov.lean`:
  `informationPotential_eq_zero_iff` already proves that its chosen quadratic
  potential vanishes precisely at `sigma=1/2`; its derivative along its
  explicitly chosen normal field is nonpositive.
- `Topology/CanonicalRapidityAngleMetriplecticFlow.lean`: an explicit
  exponential flow, group law, and critical-layer identities; the header
  explicitly disclaims arithmetic conclusions about zeta zeros.
- `Canonical/ApolloniusCriticalLineLeafBridge.lean`: projective-coordinate
  critical-line equivalences. Here `xi_zero` in theorem names means that the
  real coordinate `ξ` equals zero, NOT that the completed Xi function vanishes.

The proposed real reflection fixes one real point. On the complex plane,
`s ↦ 1-s` fixes only the single complex point `1/2`; the anti-holomorphic
reflection `s ↦ 1-conj(s)` fixes the entire critical line. The former is an
orientation-preserving complex affine map, not a construction of a Klein
bottle. Existing glide/quotient owners retain the missing topological data.

Reflection symmetry alone does not force a minimum at its fixed point:
`V(s)=((s-1/2)^2-1)^2` is symmetric under `s ↦ 1-s` and has minima at
`s=-1/2` and `s=3/2`, not at the seam. The chosen quadratic has a seam minimum
because of its particular formula, not because every symmetric well does.

Calling an arbitrary constant `CR_bound` does not prove a Cramér–Rao theorem;
that requires a statistical model and estimator/information hypotheses.
Calling affine coordinate functions waves does not construct interference
amplitudes. In particular, the proposed file never evaluates `riemannZeta`.
Its missing assertion is that EVERY actual nontrivial zero lies in the
chosen potential's zero set. Substituting the existing zero-set equivalence
shows that this assertion is precisely the unproved critical-line conclusion,
not a consequence of the quadratic's minimum.

## The Maass/Fisher quarter: existing code and its exact scope

The newest proposed `MaassSuperconductor` module is unnecessary:

- `Physics/HarishChandraCasimirBridge.lean`:
  `casimirEigenvalue_reflection`, `casimirEigenvalue_critical_line`, and
  `casimir_spectral_gap` already prove the scalar polynomial identities and
  the bound on parameters explicitly of the form `1/2 + I*t`, `t : ℝ`.
- `Arithmetic/AmariZetaDuallyFlatGeometry.lean`:
  `fisherRaoMetric_on_critical_line` proves the same polynomial evaluation;
  `fisherRaoMetric_is_real_iff` explicitly retains the additional real-axis
  possibility. Reality alone does not force the critical line.
- `Detector/AmariHessianDuality.lean`: `fisher_metric_le_quarter`,
  `fisher_metric_eq_quarter_iff`, `maximum_fisher_info_at_summit`, and
  `fisher_efficiency_pullback` give the detector model's actual metric and
  coordinate transformation, rather than defining a new constant `1/4`.
- `Canonical/AmariBinarySimplexBridge.lean` distinguishes `fisherExp` from
  `fisherMix`: the natural/logit-coordinate metric is `p*(1-p)`, while the
  probability-coordinate metric is `1/(p*(1-p))`.

Selecting a real spectral parameter already restricts to the principal-line
case. The identity `(1/2+I*t)*(1/2-I*t)=1/4+t^2` does not prove that every
automorphic eigenvalue admits such a parameter. Nor does evaluation at `t=0`
prove the existence of a cusp eigenfunction with eigenvalue `1/4`.
The separate exceptional-eigenvalue problem is substantive; see
[Booker–Lee–Strömberg, Twist-minimal trace formulas and the Selberg eigenvalue conjecture](https://doi.org/10.1112/jlms.12349).

The quarter bound for the natural-coordinate Fisher metric is not a
coordinate-independent ceiling on information: at `p=1/2`, the dual
probability-coordinate value is `4`. The existing pullback theorem records
the required transformation. Equality of two numerical constants does not
construct an intertwiner, a coupling, a resonance frequency, or a
reflectionless detector. Finite unramifiedness is not electrical zero
resistance, and general Maass forms should not be defined as level one.

## Small genuine extension prepared

The existing `Arithmetic/ActualRiemannXiEntireSchwarzBridge.lean` now contains:

1. `entireRiemannXi_one_sub_star`: combines its existing actual Schwarz theorem
   with the existing functional equation.
2. `entireRiemannXi_reflected_zero`: reflection sends an actual Xi zero to a
   zero.
3. `entireRiemannXi_unique_zero_in_invariant_region_critical`: an actual Xi zero
   in a reflection-invariant region containing at most one zero is on the
   critical line.

The third theorem exposes the indispensable local uniqueness hypothesis.
It does not manufacture that hypothesis, prove simplicity, or certify any
numerical zero. The sibling `ActualRiemannXiLocalZeroTests.lean` includes
`#print axioms` checks and reuses the existing symmetry counterexample.

## Next proof obligations, in dependency order

1. Verify the local Xi extension; then obtain actual contour-count certificates
   that imply its uniqueness premise. Do not substitute an affine toy model.
2. Prove finite Galois transition compatibility with the chosen field embeddings
   before assigning an arithmetic meaning to an inverse-limit action.
3. Connect existing abstract idele symmetry to concrete pinned adele/idele
   carriers, with quotient and topology hypotheses explicit.
4. Specify a real test-function class, its actual transform, convergence, and
   the actual zero register before proving a spectral explicit formula.
5. Establish the missing positivity and complete spectral identification;
   neither symmetry, a conditional unitary binding, nor finite truncations
   supply them.
6. For the Maass branch, first implement or reuse actual automorphic spectral
   data and local factors. Then state the rank-dependent estimate precisely,
   with its GRH premise and all quantitative parameters.
7. For the lightcone branch, reuse the existing boost, doubled-space and
   Hodge–Dirac owners. Any Cantor, spectral-triple or detector identification
   needs a separate concrete construction and intertwining theorem.

## Verification status

The shared `lake build -R` remained active while this audit was written.
The Xi test target is queued through the repository build lock; it has not
yet returned a kernel-verification result for the new extension. Earlier
build-log success for the Schwarz owner predates that extension. The report
does not claim a clean global build or an axiom audit that has not run.

Separately discovered legacy `proofs` import failures in Klein owners were
repaired by relocating existing owners and reusing the native semidirect
product bridge; their targeted verification is also queued. No second
compiler or cache-destructive command was launched.
