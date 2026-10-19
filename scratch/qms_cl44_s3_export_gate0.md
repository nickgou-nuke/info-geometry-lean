# Gate 0 contract: export the finite Cl(4,4) three-copy model

## Claim and scope

Make the finite `Cl44S3CopyModel` owner and its axiom audit, both added in the
current staged change set, reachable from the standard
`InfoGeometry.Clifford.All` umbrella. Relative to the staged owner source,
this task is an import/export integration only. It does not add a theorem or
strengthen the model's interpretation.

The exported construction is the existing `S₃ = Equiv.Perm (Fin 3)`
inverse-precomposition action on `Fin 3 → SemiSpinorPlus`, with a selected
one-hot family and componentwise lifts of arbitrary linear endomorphisms. Its
source explicitly disclaims an `SU(3)` or `U(1)` action, an action on one
spinor, and an action induced by another algebra.

## Carrier, operations, and conventions

- `CopyCarrier := Fin 3 → SemiSpinorPlus` in
  `InfoGeometry.Clifford.Cl44S3CopyModel`.
- The action is `x ↦ (j ↦ x (σ.symm j))`; permutation multiplication is
  checked against Mathlib's `Equiv.Perm` convention in `s3CopyAction_mul`.
- `diagonalLift` applies one arbitrary `ℝ`-linear endomorphism pointwise.
- No multiplication on the copy carrier and no gauge-group representation is
  introduced by this integration.

## Existing owners and proved declarations

- The staged addition `lean/InfoGeometry/Clifford/Cl44S3CopyModel.lean` imports
  `Cl44S3Family` and `Synthesis.Cl44PrimitiveIdempotentIdeal`; it proves the
  finite permutation/action, one-hot, commutation, independence, and datum
  existence results.
- The staged addition `lean/InfoGeometry/Clifford/Cl44S3CopyModelAudit.lean` imports the owner and
  prints axioms for its listed results.
- `Cl44S3Family.lean` supplies `SplitS3FamilyDatum` and explicitly scopes its
  predicates; it is currently imported by `CoverageClosure` and
  `AllExhaustive` but not by `Clifford.All`.
- `Cl44PrimitiveIdempotentIdeal.lean` is also imported by `InfoGeometry.lean`
  and the existing split-sedenion synthesis owners. The copy model's imports
  therefore introduce no new carrier or operation.

## Import and dependent search

Repo-owned Lean search found `Cl44S3CopyModel` in its staged owner and audit;
no umbrella currently imports either. `InfoGeometry.Clifford.All` is imported
by `InfoGeometry.AllExhaustive`, which is imported by `InfoGeometry.All` and
ultimately by the root library. No `Synthesis` or `Clifford` owner importing
`Clifford.All` was found in the directly searched dependency region. The
proposed insertion point is `Clifford.All`, adjacent to the Cl44 modules.
The exact umbrella import build must verify the dependency graph.

## Smallest delta

Add imports for the staged model and audit to
`lean/InfoGeometry/Clifford/All.lean`. No owner theorem changes are part of
this task.

## Not established

- An `SU(3)`, `U(1)`, or continuous color action.
- A representation induced by `Der(𝕊ₛ)` or a Clifford algebra automorphism.
- Identification of the three-copy carrier with a physical generation space.
- The relation between volume-element chirality and the parity-defined
  `SemiSpinorPlus` / `SemiSpinorMinus` submodules.

## QMS classification

```json
{
  "concept_id": "cl44_s3_copy_model_umbrella_export",
  "source_text": "Export the finite Cl(4,4) three-copy permutation model and audit, present as staged owner files, through the standard Clifford umbrella.",
  "intake_classification": "narrative-documentation",
  "target_status": "definition-backed",
  "risk_level": "R2",
  "allowed_imports": [
    "InfoGeometry.Clifford.Cl44S3CopyModel",
    "InfoGeometry.Clifford.Cl44S3CopyModelAudit"
  ],
  "formal_objects": [
    "InfoGeometry.Clifford.Cl44S3CopyModel.s3CopyAction",
    "InfoGeometry.Clifford.Cl44S3CopyModel.exists_cl44_three_copy_s3_family_datum"
  ],
  "acceptance_theorems": [
    "The owner and audit import successfully through InfoGeometry.Clifford.All.",
    "The umbrella build and root aggregate build pass without changing owner theorem statements."
  ],
  "non_theorem_claims": [
    "No SU(3)/U(1) or physical color/generation interpretation is established."
  ]
}
```

## Independent disposition

- A-A: PASS. The import point is coherent and no `Clifford.All` cycle was
  found in the inspected dependency path.
- QA-A: PASS. Strict OpenGauss screens passed for the owner, audit, and
  umbrella (0 traps); headers and staged diff checks passed.
- Semantic-vacuity scan: one classified `trivial_surface` warning at
  `evenBasisState_zero`, the direct coordinate evaluation used by the
  nonzero-state and one-hot-independence proofs; the audit file had zero
  findings. This was reviewed and accepted as a supporting coordinate lemma,
  not a placeholder or unsupported claim.
- Sequential locked builds passed: `InfoGeometry.Clifford.All` (9,916 jobs),
  `InfoGeometry.All` (25,873 jobs), and
  `InfoGeometry.Clifford.Cl44S3CopyModelAudit` (8,940 jobs). The audit prints
  `[propext]` for `stateParity_zero_even`; the remaining audited declarations
  print `[propext, Classical.choice, Quot.sound]`.
- Existing dependency and style/deprecation warnings remain; there were no
  build errors. The three Cl55 imports present elsewhere in the staged
  `Clifford.All` diff were excluded from this disposition.
- The OpenGauss discovery command was attempted but did not return a receipt
  before interruption. Its result is not counted as evidence; the contract's
  source and import-path search is the recorded Gate 0 grounding.
