# Release v1.3.0 — Grand-Canonical BdG/KMS Algebraic Layer

This release closes the finite algebraic BdG/KMS layer while preserving the
analytic C*/GNS/Tomita boundary as explicit socket data.

> Excellent — that’s the right boundary: finite algebraic BdG/KMS layer closed,
> analytic completion explicitly socketed instead of faked.

## Finite Algebraic Status

The `SupergradedCuntzBdG.lean` layer proves the finite grand-canonical
reductions and Majorana-plus square laws without claiming analytic completion.

Key proved declarations:

- `SupergradedCuntzBdG.star_bdgMajoranaPlus`
- `SupergradedCuntzBdG.bdgMajoranaPlus_sq_eq_hamiltonianAtom`
- `SupergradedCuntzBdG.bdgMajoranaMinus_is_odd`
- `SupergradedCuntzBdG.grandCanonicalBracket_even_left`
- `SupergradedCuntzBdG.grandCanonicalBracket_even_right`
- `SupergradedCuntzBdG.grandCanonicalBracket_odd_odd`
- `SupergradedCuntzBdG.grandCanonicalWeightedBracket_even_left`
- `SupergradedCuntzBdG.grandCanonicalWeightedBracket_even_right`
- `SupergradedCuntzBdG.grandCanonicalWeightedBracket_odd_odd`

## Classified Boundary

Finite algebraic blocker:

- `SupergradedCuntzBdG.bdgMajoranaMinus`: the missing star/square closure is a
  finite Cuntz-relation problem, not an analytic KMS/GNS problem.

Analytic sockets:

- `CStarCuntzTensorQuotient.UniversalCStarCompletionSocket`
- `SupergradedCuntzBdG.KMSStateSocket`
- `SupergradedCuntzBdG.TomitaTakesakiKMSRealizationSocket`
- future `ModularRenyiEntropy` spectral/Rényi/Mellin layer

## GEPA Certificate

Generate the machine-readable certificate with:

```bash
cd proofs
python3 tools/lean_graph/export_bdg_kms_certificate.py
```

Outputs:

- `proofs/tools/lean_graph/out/bdg_kms_certificate.json`
- `proofs/tools/lean_graph/out/bdg_kms_report.md`

The audit queries are in:

- `proofs/tools/lean_graph/aql_audit_bdg_kms.md`
