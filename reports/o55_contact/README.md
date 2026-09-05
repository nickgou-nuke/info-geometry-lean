Run from the repository root:

```bash
bash scripts/check_o55_contact_full_formalism.sh
```

The script builds `InfoGeometry.Orthogonal.O55ContactFullFormalism`, executes
`O55ContactAudit.lean`, and rejects unexpected or incomplete transitive axiom
reports.
