# Gate 0 — Native `Cl(4,4)` volume action on the four-mode ideal

## Intake and classification

- **Task:** construct the linear action of the native ordered volume element on the existing four-mode vacuum-generated left ideal and prove that this action is an involution.
- **Risk:** R4 (Clifford algebra and ideal representation).
- **Status:** the promoted owner and audit passed independent locked Lean builds and distinct QA-A. Full OpenGauss Gate 4 remains blocked before its kernel phase by unrelated staged-snapshot findings listed below; no Gate 7 receipt is claimed.

## Ground-truth carrier and convention

- Native carrier: `InfoGeometry.Clifford.Cl44 = CliffordAlgebra splitQ44`.
- Four-mode idempotent: `cl44VacuumIdempotent = P₀ P₁ P₂ P₃`, where `Pᵢ = a i * adag i`.
- Target submodule: `cl44LeftIdealSubmodule = range (LinearMap.mulRight ℝ cl44VacuumIdempotent)`, namely the range `{y * f}`. It is a left ideal under native associative Clifford multiplication.
- Volume: the ordered product of the actual Witt-carrier basis vectors `(e₀,e₁,e₂,e₃,f₀,f₁,f₂,f₃)`, with a proved square `+1` in the owner source.

## Existing source facts

- `Cl44VolumeElement.volumeElement` is defined in `lean/InfoGeometry/Clifford/Cl44VolumeElement.lean:43` as `cliffordVolumeElement splitQ44 volumeVectorList`.
- `Cl44VolumeElement.volumeElement_sq` is stated at line 54 as `volumeElement * volumeElement = 1`; its source proof reduces the ordered orthogonal basis product using the native Clifford relations.
- `Cl44LeftIdealSplitSedenionSynthesis.cl44VacuumIdempotent` is defined at `lean/InfoGeometry/Synthesis/Cl44LeftIdealSplitSedenionSynthesis.lean:95`; idempotency is proved at line 149.
- `cl44LeftIdealSubmodule` is the range of right multiplication by this idempotent at line 306; `cl44LeftIdealSubmodule_mem_iff` states its exact equivalence with the product range at line 316.
- `Cl44Spinors.evenSemiSpinorProj` and `oddSemiSpinorProj` are algebra elements built from the same native volume involution. No theorem currently in this task identifies their action with the coordinate parity submodules in the separate matrix model.

## Smallest gap and candidate

Kernel-checked scratch proposal: `scratch/Cl44VolumeVacuumInvariantCandidate.lean`.
Promoted narrow owner: `lean/InfoGeometry/Synthesis/Cl44NativeVolumeIdealAction.lean`, with its axiom inventory in the adjacent audit module.

The owner already proves set-level closure of the generated left ideal under arbitrary left multiplication in `cl44_left_right_spinor_ideal_corner_synthesis` (`Cl44LeftIdealSplitSedenionSynthesis.lean:393`). The missing increment is the real-linear endomorphism package on the range submodule and the involution law, not ideal closure itself.

Define `volumeLeftAction : cl44LeftIdealSubmodule →ₗ[ℝ] cl44LeftIdealSubmodule` by left multiplication by the native volume element, then prove:

```lean
theorem volumeLeftAction_involutive (x : cl44LeftIdealSubmodule) :
    volumeLeftAction (volumeLeftAction x) = x
```

The signature is finite and native. Its proof uses the range witness and associativity for the submodule-valued action, and the existing `volumeElement_sq` for involutivity.

## Imports, uses, and provenance

- Direct owner imports: `InfoGeometry.Clifford.Cl44VolumeElement` and `InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis`.
- Existing package export paths for the ideal: `InfoGeometry.All` and root `InfoGeometry`; no new public export is proposed in this Gate 0 task.
- Discovery navigation receipt: `scratch/cl44_volume_ideal_discovery_gate0.json`; receipt hash and contract bindings are recorded in `scratch/qms_cl44_volume_action_contract.json`.
- No current downstream consumer of this action is claimed. A future native-to-coordinate Fock intertwiner would be a separate consumer task.

## Explicit exclusions

This proves no ideal dimension, minimality, basis enumeration, matrix representation, coordinate Fock parity identification, `SemiSpinorPlus/Minus` equivalence, sedenion action, or physical interpretation. The native volume action on the ideal is not by itself the full Majorana–Weyl representation theorem.

## Required gates

- Strict OpenGauss screening and semantic-vacuity scan.
- Direct scratch check and locked owner/audit build passed; the audit reports `[propext, Classical.choice, Quot.sound]` for the target theorem.
- A-A and QA-A source reviews passed. Independent QA-A screening, vacuity scans, and locked builds passed for owner and audit; the audit axiom footprint is `[propext, Classical.choice, Quot.sound]`.
- The initial full Gate 4 attempt was rejected by the repository-wide staged
  hook before kernel verification. The two findings were subsequently
  repaired: the AI Studio owner now has a concrete matrix noncommutativity
  witness, and the QGT scalar identities normalize after reduction to scalar
  goals. Strict screens pass for both owners. The T16 parser needed a separate
  CAPA because nested `Matrix (Fin 2) (Fin 2) R` type ascriptions were not
  recognized; its focused 41-test T16 suite passes, strict screens pass for
  both owners, and corrected-diff A-A and independent QA-A passed for the
  parser CAPA. Fresh locked builds and Gate 4 are pending, so this task has
  not been promoted to release-ready.

## Follow-up disposition for the two staged-hook findings

- The four QGT `ring` to `ring_nf` repairs passed independent A-A and QA-A
  source review as scalar normalizations after matrix/trace/determinant
  reduction. The semantic-vacuity warning on
  `symmetricPartTwice_is_symmetric` is a nonvacuous definitional symmetry
  theorem.
- QA-A also found that the current QGT staged diff is substantially broader
  than those four tactic changes relative to `HEAD`: it replaces the previous
  `Cl11Op` API and removes/renames theorem surfaces. The new module documents
  its finite native-matrix scope. This broader source delta must be considered
  in review; the four tactic repairs alone do not characterize the whole diff.
- A Gate 4 review was started for `AiStudioNativeMathlibFindings.lean`, but
  after printing its static-preflight start line the tool returned no further
  output for several minutes; that stale review session was interrupted with
  exit 130 after confirming no Lean/Lake process was running. Running the
  staged proof-proxy hook directly then completed successfully
  (`proof_proxy_staged_gate: ok`). Gate 4 must now be retried on the stable
  index and allowed to reach its locked kernel phase.
