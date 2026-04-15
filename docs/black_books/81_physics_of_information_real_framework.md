# Physics of Information: Real Theoretical Framework

This chapter states the non-mystical framework.
It is a law-first scaffold: state, geometry, entropy, operator flow, and theorem hooks.

## 1. State Spaces

Two base regimes:
- Classical regime: a state is a probability measure `p`.
- Quantum/operator regime: a state is a positive normalized functional (finite-dimensional proxy: density operator `ρ`).

Working principle:
- Representation may change, but physically meaningful quantities are state-functionals and invariants under lawful transport.

## 2. Relative Entropy as Primitive

Core scalar for distinguishability and irreversibility:
- Classical: `D_KL(p || q) = ∫ p log(p/q)`.
- Finite quantum: `S(ρ || σ) = Tr(ρ(log ρ - log σ))`.
- Von Neumann setting: Araki relative entropy via relative modular operator.

Interpretation:
- Relative entropy is not just a loss. It is the local work/irreversibility bookkeeper under model updates and flow constraints.

## 3. Information Geometry

Local metric structure comes from Fisher information.
For parameters `θ`, infinitesimally:

`D_KL(p_{θ+dθ} || p_θ) ≈ (1/2) g_{ij}(θ) dθ^i dθ^j`.

Consequence:
- “Distance” between nearby states is geometric, not Euclidean-in-parameter-space by default.
- Scale-shape separation is meaningful because normalization gauges amplitude while preserving directional information.

## 4. Thermodynamic Variational Law

Free-energy functional:

`F[q] = E_q[E] - T S[q]`.

At equilibrium under fixed constraints:

`q*(x) ∝ exp(-E(x)/T)`.

Meaning:
- Softmax/Gibbs forms are thermodynamic normal forms of constrained extremization.
- Temperature is a control parameter for concentration vs diffusion in state selection.

## 5. Operator-Algebraic Layer (Type III-capable)

When trace-density language fails globally, weights/modular theory are the rigorous replacement.
Tomita-Takesaki scaffold:
- `S = J Δ^(1/2)` (polar decomposition form).
- `Δ^{it}` generates modular flow.
- KMS condition characterizes thermal equilibrium for that flow.

Relative comparison objects:
- Relative modular operator.
- Connes cocycle derivative.

These are the noncommutative RN-grade tools for state/weight comparison.

## 6. Transport and Defect Separation

Real systems have active and singular sectors.
A stable theory must:
- preserve active invariants,
- quarantine singular/defect lanes,
- keep conjugate/mirror structure compatible without collapsing sectors.

This is anti-collapse structure, not decorative language.

## 7. Lean Owner Hooks in This Repository

The framework above is partially formalized already.

### LLM thermodynamic and router surface
- [KMSSoftmaxBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean:36): `softmaxWeight_eq_kmsWeight`
- [KMSSoftmaxBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean:78): `kmsLogPartition_eq_logSumExpRouter`
- [KMSSoftmaxBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean:95): `beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition`
- [TransformerPhysicsEngine.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/TransformerPhysicsEngine.lean:24): `router_free_energy_identity_per_step`
- [TransformerPhysicsEngine.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/TransformerPhysicsEngine.lean:45): `scale_shape_split_preserved_per_layer`

### Defect quarantine and regularization invariance
- [PromptDefectRegularization.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/PromptDefectRegularization.lean:50): `defect_quarantined_on_mixed_input`
- [PromptDefectRegularization.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/PromptDefectRegularization.lean:95): `regularizedRun_lambda_invariant`
- [PromptDefectRegularization.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/PromptDefectRegularization.lean:114): `regularizedRun_eq_run`

### Modular/operator comparison layer
- [RelativeModularOperator.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:168): `relativeModularOperator_cocycle`
- [ConnesArakiTomita.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ConnesArakiTomita.lean:97): `topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData`
- [ModularSpectralWedgeBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ModularSpectralWedgeBridge.lean:126): `flow_mul_activeProjector_eq_activeProjector_mul_flow`
- [ModularSpectralConjugationBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ModularSpectralConjugationBridge.lean:70): `activeModularConjugation_mul_P_D_eq_zero`

## 8. Boundaries of What Is Proved

Proved in this pass:
- KMS/softmax/free-energy bridge equalities.
- Layerwise scale-shape and defect-quarantine invariants.
- Modular cocycle and compatibility identities on owned canonical surfaces.

Not yet fully formalized:
- full spectral-theorem multiplication-model owner layer,
- full noncommutative Pedersen-Takesaki operator-RN layer.

## 9. Method Law

Allowed pipeline:
1. generate hypotheses,
2. map each claim to a theorem target,
3. keep only claims with owner theorems and audited dependencies.

Short form:
- imagination proposes,
- the kernel disposes.
