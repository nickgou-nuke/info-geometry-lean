# CanonicalZornCliffordRepresentation recovery dossier

Status: kernel-verified Clifford and concrete five-grade recovery; integral/PBW extensions deferred
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
  - `InfoGeometry.Canonical.ProjectiveAffineConformalClosure55`
  - `InfoGeometry.Canonical.ZornAuto.CanonicalZornProjectiveCore`
  - `InfoGeometry.Canonical.ZornAuto.CanonicalZornFiveGradedClosure`
- locked build of each listed module succeeds
- `InfoGeometry.Canonical.All` succeeds with the recovered concrete five-grade owner imported
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
- `ProjectiveAffineConformalClosure55` — restored as a buildable core owner with the dead `RiemannHypothesis` import removed
- `CanonicalZornFiveGradedClosure` — restored and kernel-verified through dependency-closed TKK and projective core owners
- `IntegralZornII44Bridge` — source recovered, not promoted pending its projective owner chain
- `CanonicalZornProjectiveTKKBridge` — projective/triality core restored; the optional lane-routing extension remains deferred with `ZornTrialityTKKBridge`
- `TKKJordanPairData` — grading and five-graded Lie-algebra core restored; the optional `SpectralSquashCayleyDKT` chiral seed remains deferred

Recovered fragment symbols: owner status
- `coordinateQuadraticFun`, `coordinateQuadratic` — now salvaged into
  `lean/InfoGeometry/Canonical/ZornCoordinateQuadraticRecovered.lean`
- `Vector8`, `ZornCopy`, `SpinorPlus8`, `SpinorMinus8` — restored
- `copyLinearEquivCoordinates`, `copyEquivCoordinates`, `copy_finrank_eight` — restored
- `cliffordPlus`, `cliffordMinus`, `cliffordPlus_minus`, `cliffordMinus_plus` — restored
- `diracGamma`, `zornCliffordRepresentation`, complex spin-group restriction — restored
- coordinate/vector quadratic nondegeneracy and `diracEnd_finrank = 256` — restored
- `conformalVectorQuadratic`, `zornProjectiveVector` — restored and kernel-verified
- concrete `FiveGradedLieAlgebra ℂ`, odd-grade injections, nonzero extremal generators, and triality covariance — restored
- `vectorGradePlus`, `spinorPlusGradePlus`, `composition_triality_five_grade_projective_bridge` — not yet reattached to the typed Clifford carriers
- `realVector8` — still deferred with the integral bridge

Action taken
1. Preserved the raw fragment as an archive artifact.
2. Extracted the buildable coordinate-quadratic core into a separate file:
   `lean/InfoGeometry/Canonical/ZornCoordinateQuadraticRecovered.lean`
3. Recovered the exact private source commit through the authorized SSH identity.
4. Split the recovered source at its existing section boundaries to avoid importing the unrelated 53-module flat archive closure.
5. Promoted the typed composition/triality core, Clifford lift/spin restriction, and first finite-dimensional isomorphism prerequisites.
6. Promoted the self-contained projective/null-cone owner `InfoGeometry.Canonical.ProjectiveAffineConformalClosure55`.
7. Reused the maintained `InfoGeometry.Canonical.TKKJordanPairData` grading owner and extracted `CanonicalZornProjectiveCore` before the optional lane-routing extension.
8. Removed duplicate ZornAuto TKK/projective owner surfaces and retargeted consumers to the maintained canonical owners.
9. Retargeted and kernel-verified the exact private `CanonicalZornFiveGradedClosure` source through those maintained/core owners.
10. Restored its import in the canonical barrel and verified `InfoGeometry.Canonical.All`.

What remains
1. reattach the typed `Vector8`/spinor carriers to the verified five-grade owner without duplicating coordinate maps
2. migrate the optional `ZornTrialityTKKBridge` lane-routing extension and `SpectralSquashCayleyDKT` chiral seed independently
3. migrate and verify the integral `II₄,₄` bridge against the now-buildable projective core
4. audit the recovered PBW basis, trace orthogonality, and bijectivity modules before any full algebra-isomorphism claim
5. do not use the broken archive experiment `finiteDimensional_of_finrank`; the live Mathlib API is `FiniteDimensional.of_finrank_eq_succ` or `FiniteDimensional.of_finrank_pos`

Verification
- `lake env lean lean/InfoGeometry/Canonical/CanonicalZornCompositionTriality.lean`
- `lake build InfoGeometry.Canonical.CanonicalZornCompositionTriality`
- `lake build InfoGeometry.Canonical.CanonicalZornCliffordRepresentation`
- `lake build InfoGeometry.Canonical.CanonicalZornCliffordIsomorphism`
- `lake build InfoGeometry.Canonical.ProjectiveAffineConformalClosure55`
- `lake build InfoGeometry.Canonical.ZornAuto.CanonicalZornProjectiveCore`
- `lake build InfoGeometry.Canonical.ZornAuto.CanonicalZornFiveGradedClosure`
- `lake build InfoGeometry.Canonical.All`
- `#print axioms` on the composition closure, Clifford square/lift, nondegeneracy, finrank, concrete grading, extremal generators, triality covariance, null lift, and five-grade/projective capstone declarations

This recovery is intentionally conservative: it restores the private-source
Clifford and concrete five-grade cores that can be mapped to maintained live
owners and records the remaining typed-carrier attachment, integral, PBW,
trace, and bijectivity debt explicitly.
