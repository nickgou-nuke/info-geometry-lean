# Clifford centralizer / twisted-centralizer formalization map

Source: E. R. Filimoshina and D. S. Shirokov, “A Note on Centralizers and
Twisted Centralizers in Clifford Algebras”, arXiv:2404.15169v2, 22 pp.[1]

Status: theorem-factory intake. The paper classifies centralizers and twisted
centralizers of fixed-grade, involution/reversion, and direct-sum subspaces of
degenerate Clifford algebras `Cℓ_{p,q,r}`. This map records only the native
Lean surface that is already reachable; the full grade-wise classification is
open debt.

## Symbol dictionary

- `Cℓ_{p,q,r}` → `CliffordAlgebra Q` for a quadratic form `Q` on a real module.
- `Zᵐ` (ordinary centralizer of grade `m`) → `ordinaryCommutant S` applied to
  the carrier interpreting `Cℓᵐ`.
- `Žᵐ` (twisted centralizer of grade `m`) → carrier set
  `{x | ∀ v ∈ S, involute x * v = v * x}`.
- grade involution `x ↦ x̂` → `CliffordAlgebra.involute`.
- even/odd subspaces `Cℓ⁽⁰⁾`, `Cℓ⁽¹⁾` → `CliffordAlgebra.evenOdd Q 0/1`.
- reversion `x ↦ x̃` → `CliffordAlgebra.reverse` where the installed carrier
  exposes it; no reversion-centralizer theorem is asserted here.
- radical exterior algebra `Λ_r` → not formalized in this packet.

## Existing owner hits

- `lean/InfoGeometry/Algebra/KleinBottleTwistedCommutantBridge.lean:17`
  — `ordinaryCommutant`.
- `lean/InfoGeometry/Algebra/KleinBottleTwistedCommutantBridge.lean:20`
  — generic `twistedCommutant` twisting the test element `a` by an order-two
  automorphism; this is not the paper's `Žᵐ` convention.
- `lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean:307`
  — `involute_eq_self_iff_mem_even`.
- `lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean:345`
  — `involute_eq_neg_self_iff_mem_odd`.
- `lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean:160`
  — center transport under `equivOfIsometry`.
- `lean/InfoGeometry/Clifford/Cl55WittVectorCommutant.lean:14`
  — `wittTwistedVectorCommutant`, the Cl(5,5) vector/twisted specialization.
- `lean/InfoGeometry/Clifford/Cl55WittVectorCommutant.lean:39`
  — `wittVectorCenter` and its equivalence with `Subalgebra.center`.
- `lean/InfoGeometry/Physics/CentralizerInvariance.lean:91`
  — triviality of the action of the central `-1`.

Alexandria PDF lane contains the paper already as retrieval context: 40
`Filimoshina` chunk hits and 28 `twisted centralizer` chunk hits in both
`:8538` and `:8532`. These are `retrieval_context_only`, not Lean authority.

## New native owner

`lean/InfoGeometry/Clifford/CliffordCentralizerTwistedCore.lean`

Closed here:

- `gradedTwistedCentralizer` — the paper-faithful set-level twisted
  centralizer, with the involution applied to the tested element.
- `gradedTwistedCentralizer_zero_mem`.
- `gradedTwistedCentralizer_add_mem`.
- `algebraMap_mem_ordinaryCommutant_clifford`.
- `ordinaryCommutant_range_algebraMap_eq_univ` — grade-zero ordinary
  centralizer is the full carrier.
- `gradedTwistedCentralizer_range_algebraMap_eq_even` — grade-zero twisted
  centralizer is the even subspace, matching the paper's `Ž⁰ = Cℓ⁽⁰⁾`.
- `cl55_vector_commutant_eq_gradedTwistedCentralizer` — the existing Cl(5,5)
  Witt vector commutant is exactly the paper-faithful grade-one
  specialization.

## Open debt

1. Generic fixed-grade subspaces `Cℓᵐ` for arbitrary `m` are not exposed by the
   pinned Mathlib `CliffordAlgebra` API; only `evenOdd Q (i : ZMod 2)` is
   native here. Lemmas 3.1, 3.2 and 3.4 remain unformalized.
2. Theorem 3.6 (explicit centralizers/twisted centralizers of fixed grades),
   including the degenerate radical `Λ_r` terms, is open.
3. Theorem 5.1 and Theorem 5.2 (subspaces determined by grade involution and
   reversion, and their direct sums) are open.
4. The reversion-based centralizers and the appendix `Z̃ᵐ` family are open.
5. No claim is made that Cl(5,5) vector commutant reduces to scalars.

## Sources

[1] https://arxiv.org/abs/2404.15169 — Filimoshina and Shirokov 2024, A Note on Centralizers and Twisted Centralizers in Clifford Algebras
