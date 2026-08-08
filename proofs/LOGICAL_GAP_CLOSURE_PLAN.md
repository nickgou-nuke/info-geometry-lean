# Logical Gap Closure Plan

This file is the working roadmap for turning the current architecture from
compiled conditional scaffolding into lemma-by-lemma proven combinations of
known mathematical ingredients.

Rule of the road:

- If a fact is known in the literature, it must become either an imported Lean
  theorem or a local theorem with explicit hypotheses.
- If a fact is not available in Lean yet, keep it as a named interface field and
  record exactly what would discharge it.
- Do not call a synthesis unconditional until every interface field in its
  dependency chain is theorem-provided rather than axiom-provided.

## Codebase Philosophy: Clean Finite Induction, Then Colimit

The repository should close gaps in this order:

1. Prove the statement at finite stage `n`.
2. Prove the bonding map sends the stage-`n` statement to stage `n+1`.
3. Package the result as an induction theorem over all finite stages.
4. Only then transport the invariant to the colimit.

In practice this means:

- no infinite theorem should be introduced first as a black-box axiom;
- every colimit theorem should point back to a finite induction backbone;
- analytic/operator-theoretic language should be added only after the finite
  algebraic invariant and its bonding-map compatibility are explicit.

Template:

```text
finite_stage_property n
bonding_preserves_property n
finite_induction_property : forall n, finite_stage_property n
colimit_property : property_of_colimit
```

This is the preferred route for KMS regularization, Dirac colimits, determinant
defects, and spectral bridges.

## Backbone Status

### Closed: finite Klein/Tomita trace cancellation

- File: `KreinVacuumPropagator.lean`
- Main theorem:
  - `klein_tomita_vacuum_bridge`
- Literature ingredient:
  - finite-dimensional trace cyclicity.
- Lean source:
  - `LinearMap.trace_mul_comm`
- Status:
  - Fully theorem-backed in the finite sector.
  - No KMS axiom is needed.

### Conditional: KMS bridge

- File: `KreinVacuumKMSBridge.lean`
- Current bridge:
  - `DeltaRegularizedKMSContext`
  - `cyclic_of_deltaRegularized`
  - `deltaRegularized_kms_vacuum_is_finite`
- Correct interpretation:
  - KMS is twisted-cyclic, not globally cyclic.
  - Ordinary cyclicity is recovered only after the regularized modular defect
    `sigma(A) - A` has zero pairing in the tested sector.
- Remaining local task:
  - Replace generic `kms_state` / `kms_is_cyclic` wrappers with concrete finite
    Gibbs or normal-state examples where the defect-vanishing hypothesis is
    theorem-proved.

## Step-by-Step Lemma Plan

### Phase 1: make the KMS bridge theorem-honest

1. Define a concrete finite normal state.
   - Target file: `KreinVacuumKMSBridge.lean`
   - Candidate definition:
     - `omegaRho (rho : Matrix (Fin n) (Fin n) C) (A) := Matrix.trace (rho * A)`
   - Literature ingredient:
     - finite-dimensional normal states are density-matrix traces.
   - Lean task:
     - prove linearity from matrix trace linearity.

2. Define the finite modular twist.
   - Target:
     - `sigmaRho rho A`, modeled by conjugation where invertibility assumptions
       are explicit.
   - Literature ingredient:
     - finite-dimensional modular automorphism group.
   - Lean task:
     - start with an abstract `sigma` plus finite matrix assumptions, then
       specialize later to invertible density matrices.

3. Prove finite twisted cyclicity.
   - Target theorem:
     - `omegaRho_twisted_cyclic`
   - Literature ingredient:
     - KMS condition for finite Gibbs states.
   - Lean closure criterion:
     - no axiom; all hypotheses are finite matrix identities.

4. Prove regularized defect vanishing for the Klein/Tomita tested sector.
   - Target theorem:
     - `klein_tomita_regularized_defect_vanishes`
   - Required statement:
     - `omega (B * (sigma A - A)) = 0` for the `A, B` used by the propagator
       bridge.
   - Closure criterion:
     - `deltaRegularized_kms_vacuum_is_finite_klein` is instantiated from a
       concrete finite normal state, not an abstract context.

### Phase 2: make the Dirac colimit concrete

5. Replace `DiracColimitLimit.hPair` for a nontrivial tower.
   - Target file: `DiracColimit.lean`
   - Literature ingredient:
     - algebraic/direct limits of Hilbert spaces under isometries.
   - Lean task:
     - construct a concrete finite-support colimit first.

6. Prove the Cuntz/Dirac embeddings preserve the operator.
   - Target theorem:
     - `cuntz_dirac_embedding_commutes`
   - Literature ingredient:
     - compatible inductive systems of operators.
   - Lean task:
     - connect `DiracColimitData.hD_comm` to explicit Cuntz shift maps.

7. Upgrade bounded finite model to domain-tracked unbounded model.
   - Target file:
     - new `UnboundedDiracColimit.lean`
   - Literature ingredient:
     - self-adjoint operators from compatible symmetric operators on dense
       domains.
   - Status:
     - major formalization task.

### Phase 3: determinant and Mellin bridge

8. Replace finite Mellin sums with a convergent infinite spectral zeta region.
   - Target file: `ZetaSpectralBridge.lean`
   - Literature ingredient:
     - Mellin transform of heat kernels and spectral zeta functions.
   - Lean task:
     - prove the convergent half-plane statement before analytic continuation.

9. Formalize the determinant class needed by the model.
   - Target:
     - `FredholmDeterminantBridge.lean`
   - Literature ingredient:
     - trace-class Fredholm determinant.
   - Lean task:
     - avoid pretending arbitrary bounded operators have determinants.

10. Replace `InfiniteIwasawaAnalyticityLock.h_zero_defect`.
    - Target file: `ZetaSpectralBridge.lean`
    - Required theorem:
      - finite defect cancellation is compatible with the inductive embeddings
        and survives the determinant-class limit.
    - Status:
      - model-specific; not a generic citation.

### Phase 4: zeta-zero identification

11. Prove the spectral determinant identity.
    - Target theorem:
      - `spectralDet_eq_completedZeta`
    - Literature ingredient:
      - explicit trace formula / determinant formula for the chosen operator.
    - Status:
      - this is not currently known for the repo's proposed operator.

12. Replace `BridgeCertificate.zero_to_real_spectral_parameter`.
    - Target file: `ZetaSpectralBridge.lean`
    - Required theorem:
      - zeros of the selected zeta determinant correspond exactly to
        `1/2 + i * spectrum(D_inf)`.
    - Status:
      - RH-strength.  This is the final nontrivial bridge.

13. Derive RH-style critical-line theorem as the final corollary.
    - Target:
      - `RiemannHypothesis.lean`
    - Dependency:
      - phases 2, 3, and 4.
    - Closure criterion:
      - no global RH axiom, no spectral-zero identification field.

## Immediate Next Small Step

Implement Phase 1.1 as a finite-induction block:

- Add a finite matrix normal-state trace functional.
- Prove it is linear.
- Prove ordinary finite trace cyclicity as the baseline.
- Add the stage-`n` statement for the Klein/Tomita trace cancellation.
- Add the bonding-preservation lemma for the chosen finite embedding.
- Package the finite induction theorem before any infinite KMS/colimit claim.
- Then use that as the first concrete theorem-backed instance of the
  propagator bridge, before reintroducing nontrivial modular twists.
