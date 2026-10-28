# Anomaly as a Peirce-Component Readout

## Purpose and truth boundary

A counterexample to a universal identity is evidence that the identity is false
on its stated domain. Preserve the counterexample and its exact carrier, inputs,
and defect; do not preserve the refuted universal claim as though it were true.
A useful follow-up is to define the defect and prove where its components land
for the particular algebra and inputs. The counterexample is not, by itself, a
generator theorem.

The repository-native results in this area concern the nonassociative
`OpZornMatrix A` carrier from
`InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix`,
with coefficient type `[Ring A]`. They do not establish a general physical
interpretation, a general theorem that every nonzero defect is odd, or the
standalone alternate multiplication pasted in an intake prompt.

## Safe mathematical protocol

For a proposed broken identity `L = R`:

1. Pin the carrier, operations, parentheses, coefficient assumptions, and
   quantifiers. In a nonassociative carrier, `((P * X) * P)` and
   `(P * (X * P))` are different expressions unless their equality is proved.
2. Define the defect with the declared subtraction convention, for example
   `D := L - R`. Do not infer `D ≠ 0` merely because the identity was expected
   to fail; prove nonvanishing for a specific example if it is needed.
3. Use the actual Peirce projections of the owner carrier. For the four
   projections `D₊₊`, `D₋₋`, `D₊₋`, and `D₋₊`, prove the reconstruction formula
   `D = D₊₊ + D₋₋ + D₊₋ + D₋₊` and, where useful, uniqueness/separation of the
   components.
4. Prove component support for each claimed input sector. State whether a
   result is a component identity, a vanishing result, or a nonvanishing
   witness. These are distinct conclusions.
5. Call a component a grade only when the relevant grading action or grading
   structure is explicitly defined and its claimed action is proved. An
   involution on the carrier is not automatically an algebra automorphism.
6. Order declarations by actual prerequisite definitions/imports/proof uses.
   A conceptual diagram is not a formal dependency poset unless its edges are
   justified by those dependencies.
7. Build the native owner file and report warnings and remaining gates
   separately. A successful build certifies the Lean proposition, not its
   physical gloss or an unstated relationship to another carrier.

### Correct replacement principle

> A defect is a structured obstruction when its components and component
> formulas are proved. Decompose it in the native carrier, report the actual
> component support for the stated inputs, and prove nonvanishing separately.
> A nonzero defect may be diagonal, off-diagonal, or have several nonzero
> components. Do not assert universal odd-grade generation without a theorem
> that rules out purely even defects on the stated domain.

The identity `D = D₊₊ + D₋₋ + D₊₋ + D₋₊` is a reconstruction theorem. The word
"generator" should be reserved for an additional result identifying a
component as the output of a specified map/operation, with the relevant image
or nonvanishing statement proved.

## Repository-grounded theorem map

| Layer | Repo-owned Lean owner | Scope actually formalized |
|---|---|---|
| Coefficient algebra and native Zorn product | `lean/InfoGeometry/Canonical/AlbertCayleyDickson.lean` | Defines `OpZornMatrix A`, ordered dot and `skewCross`, multiplication coordinates, `opAssociator`, and `opCommutator`. The canonical product uses `a = X.a * Y.a - dot X.v Y.w` and `b = -dot X.w Y.v + X.b * Y.b`. |
| Peirce idempotents | `lean/InfoGeometry/NCG/PeirceGradingOperator.lean` | `P_plus`, `P_minus`, orthogonal idempotents, sum-to-one, and the carrier element `eta_grading`. |
| Commutator obstruction | `lean/InfoGeometry/NCG/ZornCommutator.lean` | `zornJacobiator_eq_alternating_associator`; Jacobi on the specified `quatSubalgX` sector; generic commutator Leibniz defect as a signed sum of associators. |
| Sector restrictions | `lean/InfoGeometry/NCG/TrialitySingletLieDerivation.lean` and `lean/InfoGeometry/NCG/CausalPoset.lean` | Associativity/Jacobi/Leibniz results on named sectors and the stated eta actions. These do not identify every fixed locus or make eta-conjugation a full algebra automorphism. |
| Component readouts and examples | `lean/InfoGeometry/NCG/AnomalyGradeGeneration.lean` | Four component formulas and reconstruction; same-grade product, one triple-raise associator formula, one mixed associator formula, eta parity readouts, and a diagonal-iff-off-diagonal-vanishing criterion for the Jacobiator. |

The build target for the component file is
`InfoGeometry.NCG.AnomalyGradeGeneration`. Current verification results must
be taken from a fresh locked build, not this inventory document.

## Status of the proposed table

| Proposed item | Correct repository-aligned disposition |
|---|---|
| Same-grade odd products | `opLightconeRay_nilpotence_teleportation_and_split_nambu_det` proves both same-ray square-zero identities and the two-ray products using `OpVec3.skewCross`, which land in the opposite odd slot. Thus each ray is square-zero while two distinct rays can have a nonzero product. In general noncommutative coefficients, replacing `skewCross` with `naiveCross` changes the operation. |
| Triple-odd associators | `opLightconeRay_nilpotence_teleportation_and_split_nambu_det` gives the upper-ray associator as the left/right ordered determinants in the two diagonal corners. `opUnipotent_first_quantized_nambu_three_cocycles` gives both upper and lower unipotent associators. These are distinct input families; do not identify unipotent elements with pure rays. Other orderings must be checked against owner declarations before being stated. |
| Mixed associators | The component owner proves a specified raise-raise-lower ordering. Do not silently promote it to all permutations; prove each desired ordering or cite an exact existing owner theorem. |
| Jacobiator | The universal six-associator identity is already owned by `ZornCommutator.lean`. The Jacobiator itself decomposes into all four Peirce components. It can have a diagonal component; nonzero Jacobiator does not imply a nonzero off-diagonal component. |
| Grading-number Leibniz defect | No `N` and no coefficient-`-3` formula are defined by the pasted module. The native owner instead proves the commutator Leibniz defect as a signed sum of three associators. A different grading operator requires its own definition and proof. |
| "Self-commutator vorticity" | Do not use this phrase as a theorem until the operator and exact proposition are defined. The owner proves commutator antisymmetry and self-commutator vanishing. |

The pasted self-contained proposal creates a parallel `OpZornMatrix` and
changes the canonical product signs; it also uses `naiveCross` where the owner
uses `skewCross`. A proof about that parallel definition would not certify a
claim about the repository's native carrier. Its additive four-block formula
also does not on its own prove the listed generation claims. In particular,
the naive assertion `U₁ * U₂ = 0` for arbitrary two elements of one odd grade
must be refined: the owner proves `U * U = 0`, but the product of two different
rays is the opposite-grade `skewCross` term.

## Dependency order: source-confirmed version

The useful dependency picture is a partial order, not the symmetric diagram in
the proposal:

```text
Canonical.AlbertCayleyDickson (carrier, operations, associator)
        ├──> NCG.PeirceGradingOperator (P₊, P₋, eta)
        ├──> NCG.ZornCommutator (commutator, Jacobiator identity, sector Jacobi)
        └──> NCG.TrialitySingletLieDerivation (named singlet-sector results)
                    │
PeirceGradingOperator ─┼──> NCG.CausalPoset (compositions of these results)
ZornCommutator ────────┤
TrialitySingletLieDerivation ┘
                    │
                    └──> NCG.AnomalyGradeGeneration
                         (component readouts and input-specific formulas)
```

This is a module-level prerequisite sketch. It does **not** assert that the
same-grade product theorem is a logical prerequisite of each associator
formula, or that every conceptual arrow in the proposal is a proof dependency.
For a declaration-level poset, record actual declaration references as well as
imports.

## Agent-prompt block (safe replacement)

```markdown
### Defect and Peirce-Component Protocol

1. Translate heuristic prose into a precise mathematical statement only after
   pinning the repository carrier, operations, parentheses, coefficient
   assumptions, and quantifiers. Keep the source interpretation separate from
   any physical narrative.
2. Search and read the actual owner definitions, instances, theorem statements,
   imports, and dependents before deciding a construction is absent or wrong.
   Reuse the native carrier; do not introduce a parallel presentation with
   different signs or operations.
3. If a universal identity has a counterexample, retain the witness and state
   exactly which universal claim it refutes. Do not pretend the false claim is
   true. Define the defect `D := L - R` only with the owner subtraction
   convention.
4. Decompose `D` using the actual Peirce maps. Prove reconstruction and any
   component-support or component-nonvanishing results separately. A nonzero
   defect does not, without further hypotheses, imply a nonzero odd component.
5. Use "grade" only when the relevant action/grading has been defined and its
   properties proved. An involution on the carrier need not be an algebra
   automorphism. Do not call an output a generator unless the generating map
   and image result are stated and proved.
6. Treat product, associator, Jacobiator, and Leibniz-defect formulas as
   carrier- and ordering-specific. Preserve coefficient order, cross-product
   convention, and signs; prove all desired input permutations explicitly.
7. Order results only by actual proved dependencies. Separate imports,
   declaration-level proof dependencies, and conceptual motivation.
8. Use native Lean definitions and complete kernel-checked proofs. Report
   build warnings and unresolved gates honestly. Zero `sorry`, `admit`, custom
   axioms, proxies, vacuity, or unsupported cross-carrier interpretations.
```
