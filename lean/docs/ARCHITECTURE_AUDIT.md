# InfoGeometry Architecture Audit (Import & Packetization Baseline)

## Repository proof policy

1. A theorem with missing derivation must be marked by `sorry` and not hidden behind fake witness fields.
2. Conditional adapters are allowed when they are explicitly consumed by a downstream theorem.
3. `Zorn` split-octonions are nonassociative; do not treat them as ordinary matrix-multiplication algebras.
4. `twistor` is a target of a transported structure, not definitionally a split-octonion.
5. `Cl(4,4) -> Cl(5,5)` is a real split Bott step: `Cl(4,4) ⊗̂ Cl(1,1)`.
6. Heisenberg/Sugawara is downstream; source-side proofs of `J`, `trunc`, and `comm` must be explicit.

## Current scan snapshot

I ran a repo-wide import audit.

- `import Mathlib` occurrences: **460**
- `import InfoGeometry.*.All` occurrences: **40**
- `import InfoGeometry.External.Virasoro` occurrences: **2** (`InfoGeometry/All.lean`, `InfoGeometry/Canonical/All.lean`)
- compatibility shadow imports (`InfoGeometry.Compatibility.*.Shadow`): **6**

## Import hygiene targets

- `*.lean` proof files should import only exact owners they use.
- Avoid `import InfoGeometry.All` / `import InfoGeometry.<Domain>.All` in proof files.
- Avoid `import Mathlib` in proof files when exact imports suffice.
- Keep only export barrels (`InfoGeometry.All`, `InfoGeometry.<Domain>.All`, `InfoGeometry/Compatibility/All.lean`) as umbrella imports.

## Known safe exception (current)

- `InfoGeometry/Canonical/SplitCliffordHeisenbergBridge.lean` and adjacent split current lane files already avoid blanket Mathlib imports.
- `InfoGeometry/Clifford/Cl44Witt.lean` has complete split-Witt CAR proofs (and no broad import packetization).
