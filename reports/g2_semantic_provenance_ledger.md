# G₂ semantic provenance ledger

This ledger records the distinction between what a theorem states and what a
nearby comment, name, or downstream narrative may suggest.  A theorem is not
promoted beyond its displayed hypotheses.

| Status | Owner / theorem | Formal statement boundary | Semantic classification | Required downstream guard |
|---|---|---|---|---|
| GREEN | `G2NativeFlagStabilizerTransport.pcWord_mem_nativeFlagStabilizer` | Every `pcWord e` fixes `baseIntrinsicFlag` | native forward stabilizer inclusion for PC words | do not infer stabilizer equality |
| GREEN | `G2NativeFlagStabilizerTransport.unipotentSubgroup_le_nativeFlagStabilizer` | `unipotentSubgroup ≤ nativeFlagStabilizer` | native subgroup inclusion | reverse inclusion or cardinality/transitivity is still required |
| YELLOW | `G2NativeFlagStabilizerReadback.nativeFlagStabilizer_card_eq_64_of_flag_transitive` | stabilizer cardinality is `64` under group order, flag cardinality, and transitivity hypotheses | conditional orbit–stabilizer result | supply and audit transitivity independently |
| GREEN | `G2BruhatResidualSimpleEquiv.residualSubgroup_simple_card_eq_32` | `Nat.card (residualSubgroup (2,true)) = 32` | concrete native residual cardinality | do not identify it with the 8-element exponent carrier |
| GREEN | `G2BruhatResidualSimpleEquiv.no_residualExponent_equiv_simple` | no equivalence exists between the exponent carrier and `residualSubgroup (2,true)` | native counterexample to generic residual identification | generic length-based residual equivalence is prohibited |
| GREEN | `G2TopOrderedRootProduct.topOrderedRootProduct_residual_card` | longest-element residual subgroup has cardinality `64` | parameter-specific native result | do not generalize to arbitrary Weyl parameters |
| GREEN | `G2NativePositiveRootSubgroupSystem.orderedRootProduct_unique` | each element in the six-root product image has a unique Boolean coordinate | ordered-product image normal form | image is not proved equal to `positiveRootSubgroup` |
| YELLOW | `G2NativePositiveRootSubgroupSystem.orderedRootProduct_range_card` | ordered product image has cardinality `64` | exact image cardinality, not subgroup classification | retain `Set.range` in the statement |
| ORANGE | `G2FlagFactorizationRecursion.factorization_of_depth` | factorization follows from an explicit certificate/depth hypothesis | generic conditional infrastructure | never present as a concrete 189-row certificate |
| RED | `g2FlagFactorizationTarget` as a uniform exact CAS target | claims one `left * Weyl * right` convention for all rows | contradicted by `row_4_18` orientation | use quotient-level witnesses with row-specific orientation |
| GREEN | `G2FlagCellQuotientWitness.quotient_witness_cell_one_45` | quotient equality for row `(1,45)` | concrete quotient witness | does not imply exact group factorization globally |
| GREEN | `G2FlagCellQuotientWitness.quotient_witness_cell_one_73` | quotient equality for row `(1,73)` | concrete quotient witness | same guard |
| GREEN | `G2FlagCellQuotientWitness.quotient_witness_cell_one_178` | quotient equality for row `(1,178)` | concrete quotient witness | same guard |
| GREEN | `G2FlagCellQuotientWitness.quotient_witness_cell_four_18` | quotient equality for row `(4,18)` using reversed orientation | concrete quotient witness | orientation is certificate data |
| GREEN | `G2FlagQuotientProvenance.quotient_anchor` | every anchor has a quotient witness | structural anchor transport | does not cover non-anchor rows |
| GREEN | `G2FlagQuotientProvenance.quotient_cell_zero` | quotient witness for every row in singleton cell `0` | structural singleton-cell coverage | does not cover other cells |
| GREEN | `G2FlagQuotientProvenance.exact_factorization_exists_of_quotient_row` | quotient witness implies existential exact `U·W·U` factorization | native algebraic consequence | right factor is existential, not exported raw data |
| YELLOW | `G2FlagCellQuotientWitness.hcell_one` | all four indices in cell `1` have quotient witnesses | cell-local coverage | does not cover cells `2`–`11` |
| DEAD/REMOVED | `G2FlagCell2SignedWitness.hcell_two_signed` | former cell `2` coverage theorem used 16 index cases and per-leaf `decide` | brute-force table proof removed from the owner | replace only with a native signed-word certificate or proved recursive/coordinate theorem |
| YELLOW | `G2FlagCellQuotientWitness.hcell_anchor` | every cell anchor has a quotient witness | anchor-only coverage | non-anchor rows remain separate obligations |
| YELLOW | `G2IntrinsicFlagCardinality` fiber/cardinality results | cardinality follows from explicit fiber assumptions | conditional counting framework | do not infer transitivity or quotient equivalence |
| ORANGE | `G2Fin189Certificate` | `FlagFiber ≃ Fin 189` and cardinality facts | index/cardinality carrier | does not prove quotient orbit membership |
| GREEN | `G2FlagFactorizationProvenance.CellFactorizationSound.factorization` | derives a row factorization from an explicitly supplied soundness proposition | exact native consequence of a certificate contract | does not construct the contract or claim 189-row soundness |
| ORANGE | `G2Fin189OrbitMembership` | orbit membership follows from a `CellFactorizationCertificate` input | proof contract / conditional bridge | certificate soundness must be constructed independently |
| YELLOW | `G2SchubertCalculus.structureConstants_wdvv` and related quantum claims | current owner compiles without `sorry`; scope is finite/conditional structure-constant infrastructure | kernel-checked local statements, not a completed construction of `QH^*(G_2/B)` or GW theory | do not promote to full quantum cohomology until the ring laws, grading, and geometric identifications are proved |
| DEAD | any all-row owner whose leaves are closed by `revert ...; decide` | finite proposition is discharged by global enumeration | unacceptable surrogate for structural certificate | replace with native alignment theorem or explicit proof-producing data |

## Current concrete frontier

The missing theorem is not exact group factorization and not predecessor
recursion.  It is the quotient-level family

```lean
∀ k i, i ∈ orbitCells k →
  ∃ b ∈ unipotentSubgroup,
    orbitEnum i = b •
      (QuotientGroup.mk (weylNF (orbitWeyl k).1 (orbitWeyl k).2) : CarrierQuotient)
```

To promote that family to GREEN, the repository needs either:

1. a native theorem aligning the complete `flagRepWords` carrier with the
   quotient normal form; or
2. proof-producing row data for every non-anchor row, checked by Lean matrix
   equalities and assembled through a structural certificate interface.

The CAS payload alone is data, not proof authority.  A finite table must not
be described as a structural theorem unless its soundness is independently
kernel-checked.

## Narrow verification evidence (2026-08-26)

The following owners passed individual `lake env lean` checks:

```text
G2FlagCellQuotientWitness.lean
G2FlagFactorizationRows.lean
G2NativeRootSubgroupSystem.lean
G2NativePositiveRootSubgroupSystem.lean
```

`#print axioms` reports the ordinary quotient/classical axioms and, for
selected existing computational proofs, `Lean.ofReduceBool` and
`Lean.trustCompiler`.  In particular, this is not reported as an axiom-free
claim:

```text
hcell_one, hcell_anchor:
  propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound

native_root_additive:
  propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound

orderedRootProduct_unique:
  propext, Classical.choice, Quot.sound
```

The computational dependencies are recorded explicitly rather than being
silently described as zero-axiom certificates.
