# BdG/KMS Finite Algebraic Certificate

**Generated**: 2026-06-16T10:53:20.990961+00:00
**Database**: `info_geometry`

> Excellent — that’s the right boundary: finite algebraic BdG/KMS layer closed, analytic completion explicitly socketed instead of faked.

## Summary
| Metric | Value |
|---|---|
| finite theorem declarations present | 9/9 |
| theorem-kind metadata present | 7/9 |
| finite algebraic blockers | 1/1 |
| analytic sockets present | 3/4 |
| BdG/KMS sorry/admit atoms | 0 |

## Graph Counts
| Collection | Count |
|---|---|
| lean_decls | 1044 |
| syntax_nodes | 34212 |
| references | 3128 |
| ast_child | 33472 |
| has_syntax | 740 |

## Proved Finite Algebraic Layer
| Declaration | Kind | Deps | Ref By |
|---|---|---|---|
| `SupergradedCuntzBdG.star_bdgMajoranaPlus` | `theorem` | 9 | 0 |
| `SupergradedCuntzBdG.bdgMajoranaPlus_sq_eq_hamiltonianAtom` | `theorem` | 4 | 0 |
| `SupergradedCuntzBdG.bdgMajoranaMinus_is_odd` | `theorem` | 10 | 0 |
| `SupergradedCuntzBdG.grandCanonicalBracket_even_left` | `unknown` | 8 | 1 |
| `SupergradedCuntzBdG.grandCanonicalBracket_even_right` | `unknown` | 8 | 1 |
| `SupergradedCuntzBdG.grandCanonicalBracket_odd_odd` | `theorem` | 6 | 0 |
| `SupergradedCuntzBdG.grandCanonicalWeightedBracket_even_left` | `theorem` | 8 | 0 |
| `SupergradedCuntzBdG.grandCanonicalWeightedBracket_even_right` | `theorem` | 8 | 0 |
| `SupergradedCuntzBdG.grandCanonicalWeightedBracket_odd_odd` | `theorem` | 8 | 0 |

## Classified Finite Blocker
| Declaration | Kind | Classification | Blocker |
|---|---|---|---|
| `SupergradedCuntzBdG.bdgMajoranaMinus` | `unknown` | `finite-algebraic-blocker` | bdgMajoranaMinus star/square requires finite Cuntz T_mul_S/partition algebra, not analytic completion |

## Analytic Socket Frontier
| Declaration | Exists | Kind | Layer |
|---|---|---|---|
| `CStarCuntzTensorQuotient.UniversalCStarCompletionSocket` | True | `def` | C*/universal completion |
| `SupergradedCuntzBdG.KMSStateSocket` | True | `unknown` | algebraic KMS expectation interface |
| `SupergradedCuntzBdG.TomitaTakesakiKMSRealizationSocket` | True | `inductive` | GNS/Tomita cyclic-separating realization |
| `ModularRenyiEntropy.ModularRenyiEntropySocket` | False | `future` | future spectral/Renyi/Mellin analytic layer |

## Module Inventory
| Module | Theorems | Defs | Structures | Total |
|---|---|---|---|---|
| `AlgebraicCuntzQuotient` | 1 | 0 | 0 | 51 |
| `ComplexStarCuntzRedesign` | 5 | 0 | 0 | 20 |
| `CStarCuntzTensorQuotient` | 10 | 1 | 0 | 37 |
| `SupergradedCuntzBdG` | 48 | 0 | 0 | 148 |

## Socket Users
| Socket | Transitive Users |
|---|---|
| `CStarCuntzTensorQuotient.UniversalCStarCompletionSocket` | none |
| `SupergradedCuntzBdG.KMSStateSocket` | `SupergradedCuntzBdG.KMSStateSocket.pullback`, `SupergradedCuntzBdG.KMSStateSocket.pullback_omega_apply` |
| `SupergradedCuntzBdG.TomitaTakesakiKMSRealizationSocket` | none |
