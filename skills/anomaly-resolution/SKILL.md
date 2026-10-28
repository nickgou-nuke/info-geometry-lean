---
name: anomaly-resolution
description: Replace an overstrong algebraic identity with an exact defect formula and proved component or grade characterization on the repository's actual operator carrier.
---

# Anomaly Resolution

Use when a counterexample, failed identity, or nonzero residual appears in a
Lean owner. The goal is a sharper theorem about the defect on the same carrier,
not a bare negation and not an automatic claim that every defect generates a
new grade.

## Owner-first workflow

1. Read the carrier's multiplication, additive structure, grade embeddings,
   and existing defect definitions. Search for an existing correction and its
   consumers before adding declarations.
2. State the proposed identity as `LHS = RHS`, then define the defect with the
   exact operation order, e.g. `LHS - RHS`. In noncommutative settings do not
   commute coefficients, reorder products, or replace the owner cross product
   with a familiar coordinate convention.
3. Prove the universal defect identity first. Then prove its decomposition
   into the actual owner components. Keep decomposition distinct from
   nonvanishing: component membership/parity alone does not establish a
   nonzero generator.
4. Prove a support criterion when available (for example, defect is nonzero
   iff its embedded component is nonzero). State extra coefficient, sector,
   characteristic, or nondegeneracy assumptions explicitly.
5. Order the results by dependency: carrier and projections; exact product or
   associator defect; component decomposition; nonvanishing criterion or
   sector-specific vanishing; downstream bracket/geometry consequence.
6. Add only the smallest reusable owner-aligned theorem. Compile it with the
   repository's locked build path, then run applicable placeholder, vacuity,
   and axiom gates. Follow the repository's sequential-build rule.

## Repository anchors

Use these as search starting points, not substitutes for reading current code:

- `lean/InfoGeometry/NCG/ZornCommutator.lean` proves the inner-commutator
  Leibniz defect as a signed sum of associators on the nonassociative owner
  product, and contains the Jacobiator/associator identity.
- `lean/InfoGeometry/NCG/AnomalyGradeGeneration.lean` defines the four Peirce
  component readouts on the actual operator-valued Zorn carrier. It proves
  ordered `skewCross` product and associator formulas, embedding-zero criteria,
  and component-level conditions. Its module comment explicitly distinguishes
  “defect decomposes” from “defect has a nonzero component.”
- `lean/InfoGeometry/NCG/PeirceGradingOperator.lean`,
  `TrialitySingletLieDerivation.lean`, and `CausalPoset.lean` supply related
  projections, sectors, and restricted identities; inspect their exact
  hypotheses before reuse.
- `docs/COUNTEREXAMPLE_INVENTORY_STATUS.md` is a work ledger, not proof
  authority. Recheck the current Lean owner and build state.

## Mathematical honesty conditions

- A countermodel refutes only the exact quantified claim and hypotheses it
  instantiates. Preserve valid restricted theorems.
- “Anomaly generates grade (g)” requires an equality locating the defect in
  grade (g), and a separate nonzero result if generation means nonzero.
- A four-component decomposition is a coordinate identity; it does not imply
  that any component is nonzero or that the grades form a new algebra.
- A Jacobiator formula as alternating associators is not Jacobi identity.
- A commutator Leibniz defect in a nonassociative algebra is not repaired by
  assuming associativity silently; prove the associator correction or state a
  sector where it vanishes.
- Do not add scalar, diagonal, or commuting surrogates when the request is
  about an existing noncommutative operator algebra.

Report the exact defect theorem, component theorem, assumptions, owner file,
and verification result. Label unproved nonvanishing or interpretation as
open debt.
