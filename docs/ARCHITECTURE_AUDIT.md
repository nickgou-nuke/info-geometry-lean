# Architecture Audit

Repository proof policy:

1. A theorem with missing derivation must be marked by `sorry`, not hidden behind a fake structure field or `True`.
2. Conditional adapters must say they are conditional.
3. Zorn split-octonions are not ordinary associative matrices.
4. Twistor space is not definitionally split-octonions.
5. `Cl(4,4) -> Cl(5,5)` is a real split Bott step, not complexification.
6. Heisenberg/Sugawara requires a source-side proof of `J`, `trunc`, `comm`.

Packetization audit:

- Packet names do not imply wrappers. A `Packet` file may be a real owner surface, a theorem-debt surface, or a pure import shim.
- `Bridge` files are conditional adapters when they only transport already-owned data into a downstream interface.
- `Adapter` files are compatibility shims. If they contain no proof content, flatten them to a plain import surface.
- `Wrapper` files are only kept if they discharge a real theorem burden or preserve a named legacy API. Otherwise flatten them.
- `Boundary` files are allowed when they package a real local boundary theory, but they must not pretend to prove a global realization theorem.
- A file that only re-exports imported theorems and defines no new claims should be reduced to a plain import-only module.

Packetization kinds currently present in the repository:

1. Proof-carrying owner packets:
   - `InfoGeometry.Canonical.SouriauTheoremTranslatorPacket`
   - `InfoGeometry.Canonical.ModularSurprisalThermoPacket`
   - `InfoGeometry.Canonical.ConformalFiveGradeCurrentPacket`
   - `InfoGeometry.Canonical.ConformalFiveGradeClosurePacket`
   - `InfoGeometry.Canonical.LeeYangStabilityPacket`
   - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket`
   - `InfoGeometry.Core.MajoranaLiftPacket`
   - `InfoGeometry.Physics.FreeEntropyCalibrationVariationPacket`
   - `InfoGeometry.Clifford.SplitCliffordBoundaryPacket`

2. Conditional bridge / source-witness packets:
   - `InfoGeometry.Canonical.MajoranaLiftPacketBridge`
   - `InfoGeometry.Canonical.SplitCliffordHeisenbergBridge`
   - `InfoGeometry.Canonical.SplitCARCurrentSource`

3. Import-only shim surfaces already safe to flatten:
   - `InfoGeometry.Canonical.SplitCliffordSourceCurrent`
   - `InfoGeometry.Canonical.SplitCliffordHeisenbergAdapter`
   - `InfoGeometry.Projective.SplitOctonions.BoundaryPacket`

4. Theorem-debt packet surfaces that must stay explicit until proved:
   - `InfoGeometry.Canonical.LeeYangStabilityPacket`
   - `InfoGeometry.Canonical.ModularSurprisalThermoPacket`
   - `InfoGeometry.Canonical.SouriauTheoremTranslatorPacket`
   - any packet whose public API exposes `sorry`/axiom-like debt directly

Flattened import-only surfaces in the split-Clifford lane:

- `InfoGeometry.Canonical.SplitCliffordSourceCurrent`
- `InfoGeometry.Canonical.SplitCliffordHeisenbergAdapter`

Flattened import-only surfaces in adjacent lanes:

- `InfoGeometry.Algebra.Zorn.Projective`
- `InfoGeometry.External.Virasoro.HeisenbergFlip`

Owner surfaces retained:

- `InfoGeometry.Canonical.SplitCARCurrentSource`
- `InfoGeometry.Canonical.SplitCliffordCurrentLift`
- `InfoGeometry.Canonical.SplitCliffordHeisenbergBridge`
- `InfoGeometry.Canonical.CurrentSugawaraBridge`
- `InfoGeometry.Projective.SplitOctonions`
- `InfoGeometry.External.Virasoro.HeisenbergModeFlip`

Audit boundary:

This document is a policy note, not proof evidence. Lean source remains the authority.

Operational packetization status (2026-05-24):

- `import InfoGeometry.<Domain>.All` in owner/proof files: remaining hits are limited to
  export or audit entry modules (`InfoGeometry.Library`, `InfoGeometry.Unstable.Quarantine`,
  `InfoGeometry/auto_blueprints.lean`, `AuditStrict.lean`, `AuditNative.lean`), not theorem
  owner files.

- `import Mathlib` (global packet) appears in many domain files and test files across the
  repository. This is a known large legacy cleanup task; the split/projective/Clifford lane
  files already used in the current priority phases are largely clean.

- `import InfoGeometry.External.Virasoro` appears only through barrel modules (`InfoGeometry.All`,
  and the export layer used by some unstable/audit entry points), so owner files should not
  depend on it directly.

- `Mathlib.LinearAlgebra.Matrix.Basic` is no longer used as a blanket import in the target files
  below; explicit matrix imports are used in the currently audited modules.

- `Mathlib.Analysis.Complex.Basic` currently appears in several files and is valid in this pinned
  mathlib snapshot.

- Existing fake theorem-debt wrappers (theorem value literally `True` without a proof term) were
  reduced where identified in this audit pass (e.g. `InfoGeometry.Analysis.SouriauCocycle.cocycle_jacobi_identity`
  is now explicit debt with `sorry` and a debt marker comment).
