# Krein adjoint, native Zorn multiplication, and dependency-order contract

## Intake and scope

The task starts from the user's Krein/split-octonion/Kantor synthesis and its
fifteen-node dependency table, followed by a request for native Lean 4/Mathlib
formalization and an upstream PR. The implementation base is
`08c34e03f610b452e03422037949196dc7d92d6d`.

The input supplies candidate mathematical claims and a proposed graph. Its
psychological labels and physical interpretations supply neither axioms nor
proofs. This contract preserves those boundaries: the finite graph represents
the supplied table; it is not a proof-dependency graph for exceptional-group
quantization. Incomplete targets remain in this document, not in Lean proof
holes or theorem assumptions that merely restate their conclusions.

The change has four mathematical owners and one axiom-audit leaf. Its intended
acceptance surface consists of 52 new public theorems and 17 named reused
theorems. The current validation status is recorded separately in
[the validation report](KREIN_OCTONION_BOUNDARY_REPORT.md).

## Carriers and existing owners

| Object | Native owner and conventions |
|---|---|
| Split Zorn product | `InfoGeometry.Algebra.ZornVectorMatrix`; the nonassociative product is the explicit function `mul`, with native `one` and `associator`. Coefficients form an arbitrary `CommRing R`. |
| Associative target | Mathlib `NonUnitalRing A`, additive maps `ZornVectorMatrix R →+ A`, and separately linear maps. Multiplicativity is an explicit hypothesis for the native product. |
| General Krein operator | `InfoGeometry.Krein.KreinSpace` and `KreinAdjointCommutantBridge`; bounded real operators `H →L[ℝ] H` on a complete real inner-product space with the existing `KreinSpace H` structure. |
| Doubled Hilbert space | `InfoGeometry.Krein.DoubledSpace E`, namely `WithLp 2 (E × E)`, with complete real inner-product space `E`. The Krein form is positive on the first sheet and negative on the second. |
| Fundamental symmetry | Existing `jCLM`; the Hilbert adjoint is `ContinuousLinearMap.adjoint`, and the Krein adjoint conjugates it by the fundamental symmetry. |
| Doubled operators | Existing `P_plus`, `modular_j`, `complex_i`, and `ArchetypeDictionary.peircePlus`. Operator composition remains ordered and generally noncommutative. |
| Finite dependency order | New fifteen-constructor `Node`, the supplied predecessor sets, a finite order table checked against its exact covers, and Mathlib transitive-closure/order interfaces. |

The input's real finite-dimensional examples are instances of the doubled
Hilbert statements. The latter allow arbitrary complete real Hilbert `E`;
they do not construct an inductive limit or a new analytic completion.

## Exact mathematical targets and causal dependencies

### 1. Native associator to zero associative image

Owner: `InfoGeometry.Algebra.ZornAssociativeCollapse`.

The existing associator of `U 0`, `U 1`, and `U 2` squares to the native unit.
An additive multiplicative map to an associative ring annihilates every
associator. Applying multiplicativity to this specific square therefore
annihilates the unit, and multiplying by the unit annihilates every element.

Acceptance endpoints:

- `additiveMap_eq_zero_of_multiplicative`;
- `linearMap_eq_zero_of_multiplicative`;
- `no_unital_additive_multiplicative_map`, with a nontrivial unital target.

This route requires neither simplicity of the split octonions nor injectivity
of the proposed map. It distinguishes the zero nonunital map from the absence
of any unital map to a nontrivial target. It does not exclude injective linear
maps, left multiplication as a linear action, or derivation Lie algebras.

### 2. Krein Gram operator to range isotropy and adjoint compatibility

Owner: `InfoGeometry.Krein.KreinAdjointBoundary`.

The null Gram criterion is an equivalence:
`(kreinAdjoint A).comp A = 0` precisely when
`∀ u v, kreinInner (A u) (A v) = 0`.
The proof uses nondegeneracy from the existing fundamental symmetry and the
positive Hilbert inner product, not a premise that the operator is zero.

Equality of the Krein and Hilbert adjoints is equivalent to commutation with
the fundamental symmetry. For Krein-skew operators, this is also equivalent
to Hilbert skew-adjointness. On that commutant, the Krein Gram operator has
the usual Hilbert zero-detection property.

The doubled diagonal projector maps `(x,y)` to
`((x+y)/2,(x+y)/2)`. Its idempotence and isotropic range imply null Krein
Gram. When `E` is nontrivial it is nonzero, is not Krein-self-adjoint, and has
nonzero Hilbert Gram. The nontriviality hypothesis is essential to these
inequalities.

### 3. Ordered transfers to pairing-sensitive sign witnesses

Owner: `InfoGeometry.Krein.DoubledKreinWitnesses`.

Local notation uses existing compositions:
`U = P_plus.comp modular_j` and `L = modular_j.comp P_plus`.
They act as `(x,y) ↦ (y,0)` and `(x,y) ↦ (0,x)`.

Their Hilbert adjoints interchange them; their Krein adjoints are the
negatives of the opposite transfers. The two ordered Gram operators act as
`diag(0,-Id)` and `diag(-Id,0)`. They are kept distinct.

| Input vector `u = (x,y)` | Hilbert pairing with Krein Gram | Krein pairing with Krein Gram |
|---|---|---|
| `U` | `-⟪y,y⟫` | `⟪y,y⟫` |
| `L` | `-⟪x,x⟫` | `-⟪x,x⟫` |

Nonzero-vector hypotheses give the strict sign statements. Nontrivial `E`
gives actual noncommutation of the two ordered transfer products. The carrier
is the full bounded-operator algebra, not a commuting surrogate.

The existing `complex_i` is Krein-self-adjoint and squares to `-Id`. The new
real eigenvector theorem proves that `A² = -Id` and `A v = t • v`, for real
`t`, force `v = 0`. No complexification, spectrum, exponential evolution,
or dynamical stability theorem is asserted.

### 4. Proposed edges to a finite partial order and its limitations

Owner: `InfoGeometry.Order.KreinOctonionDependencyPoset`.

The exact fifteen vertices and twenty-eight edges are retained. The finite
comparison table defines a partial order; every supplied edge is a cover,
and every cover is a supplied edge. Mathlib's locally finite order results
identify the comparison relation with reflexive transitive reachability.

The supplied levels are strictly increasing along paths, which establishes
acyclicity. They are not a cover rank. The two-edge saturated chain
`thesis → classical → bridge` and three-edge saturated chain
`thesis → projection → linearization → bridge` preclude any natural-valued
rank increasing by exactly one on every cover.

The terminal pair `calibration, quantization` has least upper bound
`synthesis`. The pair `thesis, shadow` has no least upper bound. Consequently,
the whole graph is not a join semilattice. A terminal join in the supplied
graph does not establish uniqueness of an external mathematical or physical
interpretation.

## Reuse and audit surface

`InfoGeometry.KreinOctonionAudit` imports the four owners and the existing
`ZornLeftMultiplicationDefect` owner. Its `#print axioms` commands cover every
new public theorem, fourteen existing `ZornLeftCAR` declarations, and the
existing doubled-space declarations `complex_i_sq`, `modular_j_involution`,
and `modular_j_kreinSkewAdjoint`.

This source-level audit inventory is distinct from a successfully elaborated
axiom report. Only actual compiler output can establish the transitive axiom
footprint. Permitted foundational axioms are `propext`, `Classical.choice`,
and `Quot.sound`.

## Explicit unclosed targets

The following input claims are outside this change's theorem surface:

- simplicity/classification of the split-octonion algebra;
- construction and classification of the two exceptional Kantor prolongations;
- a compatible graded inclusion of the intrinsic `G₂` grading in the octonionic
  `F₄` grading;
- exceptional Lie-algebra Killing signatures and maximal compact subgroups;
- finite-dimensional unitary representation classification;
- an analytic minimal representation on `L²(ℝ³)`, including operator domains,
  skew-adjointness, integration to a group action, and unitarity;
- a physical state-space or quotient construction that removes unphysical
  states, and any theorem of physical uniqueness.

No new theorem infers these targets from dimension counts, graph reachability,
an indefinite adjoint, or the existence of a null Gram idempotent.
