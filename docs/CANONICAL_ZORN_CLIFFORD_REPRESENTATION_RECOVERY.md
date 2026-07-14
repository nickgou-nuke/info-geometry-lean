# CanonicalZornCliffordRepresentation recovery dossier

Status: kernel-verified Clifford core recovery; integral/five-grade/PBW extensions deferred
Date: 2026-07-14

Recovered sources
- raw fragment in Hermes paste cache: `/home/goutev/.hermes/pastes/paste_56_195829.txt`
- untracked repo copy encountered during restore: `lean/InfoGeometry/Canonical/CanonicalZornCliffordRepresentation.lean`
- private source commit: `nickgou-nuke/auto@65f92a0e8f9cab105c19d96eb9946894bc4c4191`
- exact owner sources recovered from that commit:
  - `CanonicalZornCompositionTriality.lean`
  - `CanonicalZornCliffordRepresentation.lean`
  - `CanonicalZornCliffordIsomorphism.lean`
  - the deferred integral/five-grade/PBW dependency files

Live check
- restored modules:
  - `InfoGeometry.Canonical.CanonicalZornCompositionTriality`
  - `InfoGeometry.Canonical.CanonicalZornCliffordRepresentation`
  - `InfoGeometry.Canonical.CanonicalZornCliffordIsomorphism`
- locked build of each module succeeds
- locked build of `InfoGeometry.Canonical.All` succeeds
- load-bearing declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`

Nearest live codebase context
- Zorn algebra operations (`zornMul`, `zornAdd`, `zornSmul`, `zornNorm`, `zornConj`):
  `lean/InfoGeometry/Physics/SplitOctonionBraidSU3.lean`
- triality-sector label owner (`TrialitySector`, cycle facts):
  `lean/InfoGeometry/Canonical/TrialitySpin8Permutations.lean`
- existing split-spin group substrate:
  `lean/InfoGeometry/Algebraic/SplitCliffordCarrier.lean`
- existing spin-group import users / context:
  `lean/InfoGeometry/Physics/Pin55Formal.lean`

Recovered fragment dependencies: current owner status
- `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` — present
- `SplitOctonionBraidSU3` — present, but under `InfoGeometry.Physics.SplitOctonionBraidSU3`
- `CanonicalZornCompositionTriality` — restored as a buildable core owner
- `CanonicalZornFiveGradedClosure` — source recovered, not promoted; its flat archive closure reaches 53 modules
- `IntegralZornII44Bridge` — source recovered, not promoted pending its projective owner chain
- `CanonicalZornProjectiveTKKBridge` — source recovered, not promoted pending owner-by-owner migration

Recovered fragment symbols: owner status
- `coordinateQuadraticFun`, `coordinateQuadratic` — now salvaged into
  `lean/InfoGeometry/Canonical/ZornCoordinateQuadraticRecovered.lean`
- `Vector8`, `ZornCopy`, `SpinorPlus8`, `SpinorMinus8` — restored
- `copyLinearEquivCoordinates`, `copyEquivCoordinates`, `copy_finrank_eight` — restored
- `cliffordPlus`, `cliffordMinus`, `cliffordPlus_minus`, `cliffordMinus_plus` — restored
- `diracGamma`, `zornCliffordRepresentation`, complex spin-group restriction — restored
- coordinate/vector quadratic nondegeneracy and `diracEnd_finrank = 256` — restored
- `realVector8` — missing
- `conformalVectorQuadratic`, `zornProjectiveVector` — missing
- `vectorGradePlus`, `spinorPlusGradePlus`, `composition_triality_five_grade_projective_bridge` — missing
- `TKKJordanPairData` grading owner used by the fragment — missing from the searched context for this lane

Action taken
1. Preserved the raw fragment as an archive artifact.
2. Extracted the buildable coordinate-quadratic core into a separate file:
   `lean/InfoGeometry/Canonical/ZornCoordinateQuadraticRecovered.lean`
3. Recovered the exact private source commit through the authorized SSH identity.
4. Split the recovered source at its existing section boundaries to avoid importing the unrelated 53-module flat archive closure.
5. Promoted the typed composition/triality core, Clifford lift/spin restriction, and first finite-dimensional isomorphism prerequisites.
6. Imported the verified chain from `InfoGeometry.Canonical.All`.

What remains
1. migrate and verify the projective/TKK/five-grading owner chain independently
2. migrate and verify the integral `II₄,₄` bridge only after its projective owner builds
3. audit the recovered PBW basis, trace orthogonality, and bijectivity modules before any full algebra-isomorphism claim
4. do not use the broken archive experiment `finiteDimensional_of_finrank`; the live Mathlib API is `FiniteDimensional.of_finrank_eq_succ` or `FiniteDimensional.of_finrank_pos`

Verification
- `lake env lean lean/InfoGeometry/Canonical/CanonicalZornCompositionTriality.lean`
- `lake build InfoGeometry.Canonical.CanonicalZornCompositionTriality`
- `lake build InfoGeometry.Canonical.CanonicalZornCliffordRepresentation`
- `lake build InfoGeometry.Canonical.CanonicalZornCliffordIsomorphism`
- `lake build InfoGeometry.Canonical.All`
- `#print axioms` on the composition closure, Clifford square/lift, nondegeneracy, and finrank declarations

This recovery is intentionally conservative: it restores only the private-source
core that can be mapped to maintained live owners and records the remaining
integral, five-grade, PBW, trace, and bijectivity debt explicitly.
