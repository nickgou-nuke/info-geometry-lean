# CP-003 Sandbox Witness

- Packet: `CP-003`
- Sandbox file: `lean/InfoGeometry/Canonical/Sandbox_CP003_SingularPolarDecomposition.lean`
- Date: `2026-04-14`

## Compile Gate

Command:

```bash
lake env lean lean/InfoGeometry/Canonical/Sandbox_CP003_SingularPolarDecomposition.lean
```

Result:
- `PASS` (file-level compile successful)
- linter warning only (`simpa` → `simp` suggestion at line 70)

## Surfaces Implemented

- `global_active_apex_decomposition`
- `chiral_range_domain_decomposition`
- `singular_polar_surrogate_closure`

The sandbox theorem family is now registered and compile-verified, ready for
promotion planning into a non-sandbox owner after downstream significance checks.
