# TheoremCandidatePacket: AsanoKleinFourSymmetry

## Formal Target
**Namespace:** `InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry`
**Socket:** `AsanoCompactificationWitness`
**Authority Level:** `execution_intent` (socket debt)

## Candidate Signature
```lean
@[socket_debt_tag, rep_depth thermo]
structure AsanoCompactificationWitness where
  forbiddenSet : Set ℂ
  forbiddenSet_no_zero : (0 : ℂ) ∉ forbiddenSet
  forbiddenSet_v4_symmetric : IsV4Symmetric forbiddenSet
  leeYangCircle_outside_forbidden : LeeYangCircle ⊆ forbiddenSetᶜ
  no_unconditional_Asano_claim_guard : Type
```

## Bridge Claim
The V₄ = {id, inv, conj, cpt} action on the complex fugacity plane:
- `id: z ↦ z`
- `inv: z ↦ z⁻¹`
- `conj: z ↦ z̄`
- `cpt: z ↦ z̄⁻¹`

preserves the Lee-Yang circle `LeeYangCircle = {z : ℂ | ‖z‖ = 1}`.

## Novelty Defense
1. **Finite symmetry reduction**: The infinite analytic Lee-Yang/Asano covering argument is reduced to a finite V₄ orbit check on the Lee-Yang circle.
2. **V₄ action on fugacity plane**: The specific Klein-four generators (inversion, conjugation, CPT) are proved to preserve the Lee-Yang circle (`v4Action_preserves_LeeYangCircle`).
3. **Witness structure**: `AsanoCompactificationWitness` packages the finite algebraic content (V₄-symmetric forbidden set, Lee-Yang circle outside forbidden set) that a concrete prime/Majorana system must supply.
4. **No unconditional claim**: Explicit guardrail `no_unconditional_Asano_claim_guard : Type` prevents misinterpretation as unconditional Asano theorem proof.

## Bridge Claim
The V₄ symmetry on the fugacity plane provides the finite algebraic skeleton that a concrete prime/Majorana system must instantiate to complete the global Asano contraction argument. The V₄ action preserves the Lee-Yang circle, reducing the global analytic problem to a finite orbit check over endpoint representatives.

## Authority Level
`execution_intent` — This is a socket awaiting concrete analytic completion. The finite V₄ structure is proved; the global analytic covering argument remains a socket debt.