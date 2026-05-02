# Sinkhorn Defect Flow Coverage Matrix

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

| Concept | Status | Anchor / Owner | Notes |
|---------|--------|----------------|-------|
| Triality MoE Algebra | `implemented` | [TrialityMoE.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/LLM/TrialityMoE.lean) | Exact two-stage residual law matching Llama 4 block form. Split of output into shared + active routed parts. |
| MoE Router Thermodynamics | `implemented` | [MixtureOfExperts.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/MixtureOfExperts.lean) | Normalization defined as gauge fixing to probability simplex. Proved valid convex combination of expert manifold. |
| Attention Softmax as Gibbs | `implemented` | [Attention.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/Attention.lean) | Attention weights rigorously proved to normalize to 1 via Gibbs distribution of the Grand Canonical ensemble. |
| Sinkhorn Flow Foundation | `implemented` | [SinkhornFoundation.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SinkhornFoundation.lean) | Rigorous modeling of alternating row/col normalization as Weyl gauge transforms. Proved monotonic Lyapunov/RN barrier contraction. |
| Sinkhorn Defect Flow | `implemented` | [SinkhornDefectFlow.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/LLM/SinkhornDefectFlow.lean) | Connects router residuals to non-equilibrium clock defects in the canonical theory. |
| Triality MoE / Canonical Bridge | `implemented` | [TrialityMoE.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/LLM/TrialityMoE.lean) | Links the LLM router-residual operator to the canonical observer-defect residual on the Drazin/KKT lane. |
| Count to Sinkhorn Flow | `implemented` | [CountSinkhornFlow.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/CountSinkhornFlow.lean) | Connects the foundational L0 count substrate directly to emergent Sinkhorn time flows. |
| Thermodynamic Routing Defects | `interface` | [SinkhornDefectFlow.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/LLM/SinkhornDefectFlow.lean) | The framework for odd-sector defects is present, but detailed consequences of `IsRouterEquilibrium` on downstream attention are partially interface-level. |
