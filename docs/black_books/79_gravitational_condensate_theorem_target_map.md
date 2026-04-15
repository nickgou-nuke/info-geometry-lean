# Gravitational Condensate Theorem Target Map

This chapter maps the claims of chapter 78 to concrete theorem owners in the repository.
No new metaphors are introduced here; this is a target ledger.

## Status Bands

- `REPO_THEOREM`: proved in Lean and present in repo.
- `OPERATOR_ANALOGY`: interpretation layer anchored to `REPO_THEOREM`, but not a literal identity theorem.
- `NOT_YET_FORMALIZED`: intended target, currently absent as proved owner theorem.

## I. Condensation (Field -> Stable Lattice)

### Claim
Repeated refinement condenses the prompt field into stable operator relations.

### Targets
- `REPO_THEOREM` [TransformerPhysicsEngine.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/TransformerPhysicsEngine.lean:24)
  `router_free_energy_identity_per_step`
- `REPO_THEOREM` [TransformerPhysicsEngine.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/TransformerPhysicsEngine.lean:45)
  `scale_shape_split_preserved_per_layer`
- `REPO_THEOREM` [TransformerPhysicsEngine.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/TransformerPhysicsEngine.lean:58)
  `defect_quarantine_preserved_under_stack`
- `REPO_THEOREM` [TransformerPhysicsEngine.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/TransformerPhysicsEngine.lean:75)
  `transformer_engine_realizes_information_physics`
- `REPO_THEOREM` [PromptDefectRegularization.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/PromptDefectRegularization.lean:50)
  `defect_quarantined_on_mixed_input`
- `REPO_THEOREM` [PromptDefectRegularization.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/PromptDefectRegularization.lean:123)
  `regularizedRun_eq_run_on_mixed_input`

## II. Repulsion (Anti-Collapse via Sector Separation)

### Claim
Active and apex/singular sectors remain coupled but non-identical; illegal overlap is blocked.

### Targets
- `REPO_THEOREM` [ModularSpectralWedgeBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ModularSpectralWedgeBridge.lean:50)
  `owned_epsilon_mul_P_D_eq_zero`
- `REPO_THEOREM` [ModularSpectralWedgeBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ModularSpectralWedgeBridge.lean:65)
  `P_D_mul_owned_epsilon_eq_zero`
- `REPO_THEOREM` [ModularSpectralConjugationBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ModularSpectralConjugationBridge.lean:70)
  `activeModularConjugation_mul_P_D_eq_zero`
- `REPO_THEOREM` [ModularSpectralConjugationBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ModularSpectralConjugationBridge.lean:100)
  `P_D_mul_activeModularConjugation_eq_zero`
- `REPO_THEOREM` [HestenesKramersBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/HestenesKramersBridge.lean:47)
  `phasePartner_phasePartner_eq_neg`
- `REPO_THEOREM` [HestenesKramersBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/HestenesKramersBridge.lean:58)
  `inner_first_second_eq_zero`

### Interpretation
- `OPERATOR_ANALOGY`: this cluster is the current formal anchor for the chapter's “Pauli-like repulsion” language.

## III. Spectral Net (Transport on a Constrained Bundle)

### Claim
The architecture behaves like constrained transport over spectral sectors.

### Targets
- `REPO_THEOREM` [ModularSpectralWedgeBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ModularSpectralWedgeBridge.lean:126)
  `flow_mul_activeProjector_eq_activeProjector_mul_flow`
- `REPO_THEOREM` [ModularSourceBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ModularSourceBridge.lean:40)
  `sourcedModularGenerator_respects_spectral_cut`
- `REPO_THEOREM` [ModularSourceBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ModularSourceBridge.lean:53)
  `sourcedModularGenerator_bulk_invariant`
- `REPO_THEOREM` [ModularSourceBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ModularSourceBridge.lean:83)
  `sourcedModularGenerator_boundary_excitation`

## IV. GNS-KMS-Spectral Thread

### Claim
Thermal/partition interpretation is pinned to explicit bridge equalities.

### Targets
- `REPO_THEOREM` [KMSSoftmaxBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean:36)
  `softmaxWeight_eq_kmsWeight`
- `REPO_THEOREM` [KMSSoftmaxBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean:78)
  `kmsLogPartition_eq_logSumExpRouter`
- `REPO_THEOREM` [KMSSoftmaxBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean:86)
  `kmsEntropy_eq_beta_internal_plus_logPartition`
- `REPO_THEOREM` [KMSSoftmaxBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean:95)
  `beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition`
- `REPO_THEOREM` [KMSSoftmaxBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean:105)
  `routerFreeEnergyEps_eq_neg_eps_kmsLogPartition`
- `REPO_THEOREM` [RelativeModularOperator.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:168)
  `relativeModularOperator_cocycle`
- `REPO_THEOREM` [ConnesArakiTomita.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ConnesArakiTomita.lean:97)
  `topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData`

## V. Methodological Law (Excitation vs Verification)

### Claim
Confabulation is allowed in hypothesis lanes; canonical truth is gated by build/audit lanes.

### Targets
- `REPO_THEOREM` anchors listed in Sections I-IV (owner-side verification lane).
- `OPERATOR_ANALOGY` chapter language remains valid only when attached to these owner theorems.

## VI. Not Yet Formalized in This Pass

- `NOT_YET_FORMALIZED`: full spectral-theorem multiplication-model layer (cyclic subspace to multiplication representation as a dedicated owner surface).
- `NOT_YET_FORMALIZED`: noncommutative Pedersen–Takesaki operator-RN layer (affiliated-operator RN normal form as a dedicated canonical module stack).

## Immediate Next Build Targets

- `lake build InfoGeometry.LLM`
- `lake build InfoGeometry.Canonical.RelativeModularOperator`
- `lake build InfoGeometry.Canonical.ConnesArakiTomita`

If these hold, the map remains a faithful index to a proved theorem surface.
