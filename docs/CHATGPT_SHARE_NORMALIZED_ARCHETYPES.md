# Normalized mathematical archetypes from the shared Plabic/Krein session

## Scope

This file removes narrative interpretation and records only typed mathematical
objects, operations, hypotheses, and conclusions supported by repository owner
files.  A declaration is marked **proved** only at the exact carrier and
hypothesis scope of its owner.  A structure field is marked **conditional**;
its existence is not inferred.  A target with no owner theorem is **open**.
No chat prose, physical slogan, external link, or pasted build report is proof
evidence.

## 1. Atomic normalized claims

### A. Algebraic exchange and Jordan--Lie decomposition

**Carrier.** `A` with `[Ring A] [Algebra ℝ A]`.

**Definitions.**

```lean
ScalarQCommutes (q : ℝ) (X Y : A) : Prop := X * Y = q • (Y * X)
jordanProduct a b := (a * b + b * a) / 2
lieBracket a b := (a * b - b * a) / 2
```

**Proved owner declarations.**

- `InfoGeometry.Algebra.QDeformedJordanLieBridgeWave21.jordan_lie_balance_of_scalarQCommutes`
  proves, under `ScalarQCommutes q X Y`,
  `(q + 1) • lieBracket X Y = (q - 1) • jordanProduct X Y`.
- `...lieBracket_eq_zero_of_scalarQCommutes_one` proves the `q = 1`
  specialization.
- `...jordanProduct_eq_zero_of_scalarQCommutes_neg_one` proves the `q = -1`
  specialization.
- `InfoGeometry.Algebraic.affine_jordan_lie_interpolation` proves for every
  real `q` and `a b : A`:

```lean
((1 + q) / 2 : ℝ) • (a * b) + ((1 - q) / 2 : ℝ) • (b * a)
  = jordanProduct a b + q • lieBracket a b
```

**Valid interpretation.** These are ring/algebra identities.  They do not
construct CCR/CAR representations, thermal states, or partition functions.

### B. Split-complex/Bogoliubov algebra

**Carrier.** `SplitComplex R`, where `[CommRing R]`.

**Proved owner declarations.**

- `SplitComplex.epsilon_squared` proves the distinguished split element
  squares to one.
- `SplitComplex.bogoliubov_interval_invariance` proves, under
  `c*c - s*s = 1`, that the defined coordinate transformation preserves
  `u*u - v*v`.
- `SplitComplex.bogoliubov_ccr_preservation` returns exactly the supplied
  hyperbolic equation; it does not prove an operator CCR theorem.

**Valid interpretation.** This is a polynomial split-algebra identity and a
coordinate quadratic-form preservation law.  A physical Bogoliubov transform,
CCR/CAR representation, KMS state, or Unruh theorem requires a separately
constructed operator/state carrier.

### C. Fixed two-sector projector algebra

**Carrier.** `Matrix (Fin 2) (Fin 2) ℂ` in
`InfoGeometry.Algebra.KreinPosNegDecomposition`.

**Proved owner declarations.**

- `J_sq` proves the displayed grading matrix squares to identity.
- `P_plus_sq`, `P_minus_sq`, `P_plus_mul_P_minus`,
  `P_minus_mul_P_plus`, and `P_plus_add_P_minus` prove idempotence,
  orthogonality, and partition of unity.
- `J_as_projectors` and `J_sq_via_projectors` identify the grading with the
  difference of these concrete projectors.

**Valid interpretation.** This is a finite matrix decomposition.  It is not,
by itself, a general Krein-space positivity theorem, thermal density matrix,
or modular flow.

### D. Para-Kähler isotropic splitting

**Carrier.** The exact `V`, bilinear form, and `ParaComplexStructure` /
`ParaKahlerStructure` hypotheses in `InfoGeometry.Canonical.FiniteParaKahler`.

**Proved owner declarations.**

- `plus_metric_isotropic` proves vanishing of the metric on the plus
  eigenspace under the owner hypotheses.
- `minus_metric_isotropic` proves the corresponding minus result.

**Valid interpretation.** These are conditional linear/para-Kähler isotropy
lemmas.  They do not identify this carrier with a thermal simplex or a
positive Fisher metric.

### E. Plabic incidence and chiral block operator

**Carrier.** Finite bipartite indices and a matrix
`K : Matrix VW VB R` with `[CommRing R] [StarRing R]` plus the owner finiteness
and decidable-equality assumptions.

**Definitions.**

- `kreinSignature` is the block diagonal grading `diag(1,-1)`.
- `diracDHK K` is the off-diagonal block matrix
  `[[0, K.conjTranspose], [K, 0]]`.
- `kreinAdjoint M := kreinSignature * M.conjTranspose * kreinSignature`.

**Proved owner declarations.**

- `diracDHK_sq` proves
  `diracDHK K * diracDHK K = fromBlocks (K†K) 0 0 (KK†)`.
- `diracDHK_anticommutes_chirality` proves the anticommutator with
  `kreinSignature` is zero.
- `diracDHK_krein_skew` proves the owner’s matrix identity
  `kreinAdjoint (diracDHK K) = -diracDHK K`.

**Valid interpretation.** These are exact block-matrix identities.  A theorem
about matching nonzero spectra or singular values requires an additional
finite-dimensional field/star/inner-product theorem and is open at this
scope.

### F. Finite graph and Kasteleyn data

**Carriers.** `FinitePlabicGraph`, `KasteleynSigning`, and the weighted edge
matrix definitions in `InfoGeometry.Canonical.FinitePlabicKasteleyn`.

**Status.** The graph, endpoint maps, supplied face boundaries, signing
constraints, and signed incidence-matrix readouts are owner-level data and
lemmas.  Existence of a signing and a planar embedding are not consequences of
the data structures.

### G. Directed paths and presented path classes

**Carrier.** `DirectedPath`, `DirectedPathPresentation`, contextual rewrites,
and `PresentedPathClass` in `InfoGeometry.Topology.ChiralDirectedGraphHomotopy`.

**Proved structural laws.** Identity/append laws and append congruence for the
presented quotient are available at their exact owner scope.

**Valid interpretation.** A directed path is a typed compositional object.
A rewrite is admissible only when declared by the presentation.  A plabic
square move is not a path rewrite unless an explicit presentation and proof
are added.

### H. Nilpotent local transport

**Carrier.** The local `Cl11Op` carrier owned by
`InfoGeometry.Holography.PlabicKreinTwistedClusterMutation`.

**Proved owner surface.** `Gamma_sq_zero`, `mutation_rotor_unitary`, and
`cluster_mutation_is_exponential_adjoint` establish the nilpotent square,
two-sided inverse, and the stated local conjugation computation.

**Valid interpretation.** “Unitary” in this owner means a two-sided inverse in
the local ring.  It does not mean star-unitarity.  The result does not identify
all square moves with conjugation.

### I. Boundary bridge and Plücker readouts

**Carrier.** The explicit boundary-measurement matrix and `addBridge` owner in
`InfoGeometry.Topology.PlabicBoundaryMeasurement`.

**Proved scope.** Column-shear behavior, disjoint-minor invariance, target
minor expansion, explicit `Gr(2,4)` minors, the three-term Plücker identity,
and positivity under the file’s stated positive parameters.

**Boundary.** No planar network boundary-measurement map is supplied by these
facts, so no general square-move/gauge-equivalence theorem follows.

### J. Cluster face mutation

**Carrier.** `SquareFaceWeights F` in `InfoGeometry.Topology.PlabicCluster`,
with the file’s field/nonzero-denominator assumptions.

**Proved declarations.** `square_move_central_inversion`,
`square_move_opposite_pair_12`, `square_move_opposite_pair_34`,
`total_cluster_face_weight_monodromy`, `cluster_mutation_involution`,
`ptolemy_face_weight_add_one`, and `ptolemy_face_weight_inv`.

**Valid interpretation.** These prove rational coordinate identities and
involution for the declared five-face mutation.  They do not prove equality
with the local `Cl11Op` conjugation or a graph square move without a typed map.

### K. Thermodynamic graph/path readouts

**Carrier.** `DirectedThermoGraph` and finite path structures in
`InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus` and
`InfoGeometry.Canonical.MaximumCaliberPath`.

**Proved/conditional scope.** Edge affinities, currents, finite path ratios,
additive log readouts, and the positive-ratio exponential identity are
available under their exact hypotheses.  `GraphMaxCalPathLaw` and
`MaximumCaliberOptimizer` contain assumptions as fields; they do not prove
optimizer existence or uniqueness.

### L. Function-to-function operator contracts

**Carrier.** `NeuralOperator X Y Z := (X → Y) → (X → Z)` in
`InfoGeometry.Canonical.NeuralOperatorCore`.

**Proved scope.** `totalCost_nonneg`, `operator_totalCost_le_of_contract`,
`pointwiseReadoutError_nonneg`, and `pointwiseReadoutError_le_of_contract`.

**Valid interpretation.** These are contract-implied inequalities.  No
training, differentiability, reverse-mode adjoint, biological network, or PDE
solver theorem is present in this owner surface.

### M. BKM operator-form readouts

**Carrier.** `FaithfulDensityOperator n`, operator-valued one-forms, and the
finite BKM real bilinear form in
`InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms`.

**Proved declarations.** `bkmOperator1Form_swap`, `bkmOperator1Form_nonneg`,
`bkmOperator1Form_polarization`, `bkmProbeReadout_skew`,
`bkmProbeReadout_wedge_self_diag_zero`, and the linearity/subtraction lemmas.

**Valid interpretation.** These establish symmetry, nonnegativity,
polarization, and alternating readouts for the finite BKM carrier under the
stated continuity hypothesis.  They do not identify BKM with a para-Kähler
metric or establish a general infinite-dimensional modular logarithm.

### N. Colimits and typed comparison

**Carrier distinction.** Algebraic colimits, Hilbert completions, supplied
cocones, and inverse systems are distinct categorical problems.

**Proved scope.** The repository contains owner-specific categorical colimit
constructions and selected comparison results, including matrix-stage and
other direct-limit lanes.  A pasted global “all seven lanes are equivalent”
report is not promoted without exact declarations and a verified build log.

**Open comparison contract.** A genuine comparison theorem must specify two
carriers in the same category, stage maps, an actual morphism, its stage
naturality, an inverse or universal-property uniqueness proof, and transport
laws for each claimed operation. A supplied isomorphism field alone is not a
proof of canonical equivalence.

**Closed local comparisons.** `InfoGeometry.Categorical.ColimitComparison`
proves universal-property comparison and stagewise endomorphism transport for
categorical colimits. `InfoGeometry.Topology.ChiralDirectedGraphHomotopy`
now proves `map_contextualPathRewrite`, constructs
`PresentedPathClass.mapClass`, and proves `PresentedPathClass.mapClass_comp`
under the explicit cell-preservation hypothesis. These are typed local edges;
they do not close the remaining cross-carrier equivalences.

## 2. Causal prerequisite poset

The following order contains only dependencies justified by the mathematical
interfaces above.

```text
finite graph data
  ├─→ signing constraints and weighted incidence matrix
  ├─→ typed directed paths ─→ presented path classes
  └─→ endpoint-respecting edge/path maps (if supplied)

weighted incidence matrix
  └─→ chiral block Dirac operator
       ├─→ block-square Gram identity
       └─→ with grading ─→ anticommutation and Krein-skew identity

local Cl11Op
  └─→ nilpotent edge
       └─→ truncated inverse
            └─→ local conjugation readout

boundary matrix
  └─→ bridge/minor identities
       └─→ explicit Plücker relation and positivity readouts

square-face weights
  └─→ rational mutation
       └─→ opposite-pair identities and mutation involution

thermodynamic graph
  └─→ affinities/currents
       └─→ finite path product/log readouts
            ├─→ detailed-balance cycle criterion
            └─→ conditional MaxCal law/optimizer interfaces

finite density operator + continuity
  └─→ BKM symmetry/nonnegativity
       └─→ polarization and alternating probe readouts

projector/grading carrier
  └─→ para-Kähler isotropy or finite matrix projector identities

all proposed cross-domain arrows
  └─→ require explicit carrier maps + composition + commuting readouts
       └─→ typed comparison theorem [OPEN]
```

## 3. Invalid interpretations rewritten as valid mathematics

| Prose interpretation | Valid replacement |
|---|---|
| “Krein sheets are a Klein bottle.” | A finite Krein/projector carrier and a topological quotient are separate objects. A theorem requires explicit maps and a homeomorphism theorem. |
| “The EPR condition glues the Möbius boundaries.” | A scalar pairing condition may imply an algebraic involution under stated hypotheses; it does not define a topological gluing map. |
| “q-commutation is a thermal partition function.” | A scalar exchange relation yields the Jordan/Lie balance identity only. A partition function requires a state, spectrum, and trace/summability data. |
| “BKM equals the para-Kähler metric.” | The BKM form is a positive finite bilinear form under hypotheses; para-Kähler isotropy is an independent conditional structure. A comparison needs a common tangent carrier and equality theorem. |
| “Bogoliubov algebra proves Unruh/KMS physics.” | The split polynomial preserves its quadratic form. A KMS or Unruh result requires an operator algebra, state, and one-parameter action with the KMS law proved. |
| “Plabic mutation is neural backpropagation.” | Cluster mutation, path transport, and reverse-mode adjoints are distinct operations. An identification requires typed maps and a composition theorem. |
| “A neural operator contract proves training or a PDE solution.” | It proves only the inequalities encoded by the contract. |
| “A finite index/analytic carrier is a full Lorentzian Kasparov theorem.” | The exact finite or conditional owner theorem is the only admitted scope. |
| “A local algebraic Klein-bottle shadow proves topology.” | Group/commutant identities are algebraic. A topological conclusion requires a quotient carrier and topological invariants. |

## 4. Open theorem contracts

These are genuine targets, not asserted results.

1. **Plabic path transport.** **Closed at the presented-path level:** the
owner maps contextual rewrites and preserves quotient composition under
`hcell`. A concrete Plabic graph instantiation and invariant readout remain
open.
2. **Plabic path readout.** Choose one finite graph, define an
   endpoint-preserving edge map into a fixed operator category, define ordered
   path transport, and prove identity and append composition. Then prove one
   invariant readout commutes with transport.
3. **Dirac spectral correspondence.** Fix a field/star-compatible finite
   inner-product carrier and prove the precise nonzero spectral correspondence
   of `K†K` and `KK†`, including multiplicities if claimed.
4. **Cluster/conjugation comparison.** Provide a typed map from the local
   `Cl11Op` carrier to the face-weight carrier and prove that the map sends the
   local conjugation readout to the declared mutation formula. Do not infer it
   from matching symbols.
5. **BKM/para-Kähler comparison.** Specify one shared finite tangent carrier,
   both bilinear forms, and prove equality or a stated pullback relation with
   all positivity and nondegeneracy hypotheses explicit.
6. **Colimit comparison.** For a fixed diagram and category, construct the
   comparison morphisms from independently proved universal properties and
   prove stage triangles and inverse identities. Do not use a supplied witness
   packet as canonicality evidence.
7. **Adjoint path transport.** Add a differentiable finite-stage carrier,
   define the differential and adjoint maps, and prove reverse-order
   composition. The current neural operator contract does not supply this.

## 5. Admission rule

A new edge in the causal graph is admitted only after a native Lean theorem
with explicit carrier, hypotheses, conclusion, and full kernel-checked proof
exists in the owner module.  Definitions, aliases, structures containing the
claim, `rfl` readbacks, pasted build summaries, filenames, and semantic
similarity are not theorem evidence.
