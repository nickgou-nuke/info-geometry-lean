# Multilingual Theorem Translator

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This repository accepts dense multilingual mathematical prose as upstream
theorem-factory material.  It must not be compiled into Lean directly.

The required path is:

```text
multilingual prose
-> terminology normalization
-> theorem-role segmentation
-> repo-native owner-surface mapping
-> conservative Lean theorem surface
-> lake verification
```

The translator is a theorem-surface generator, not a proof oracle.  It may
suggest Lean names and locate owner corridors.  It must not turn rhetoric,
metaphor, graph proximity, or literature-style derivations into proof.

## Packet Format

For each source text, produce:

| Field | Meaning |
| --- | --- |
| `TERMS` | Source-language phrase mapped to repo-native symbol. |
| `CLAIMS` | Atomic theorem candidates, one mathematical role each. |
| `ASSUMPTIONS` | Hidden gates such as PSD, finite-state, differentiability, regularity, or KKT admissibility. |
| `OWNER_SURFACES` | Existing Lean files/declarations that already own the claim. |
| `LEAN_SURFACES` | Conservative theorem names to add only if they delegate to owner proofs or expose explicit hypotheses. |
| `DEBT` | Claims that remain unformalized because the needed substrate is absent. |

## Souriau/Fisher/Onsager Example

For Bulgarian/English prose about Souriau thermodynamics, Fisher metrics,
Fenchel-Legendre duality, Onsager response, and entropy production, normalize
the text into five claims.

| Claim | Source phrase | Repo-native target | Status |
| --- | --- | --- | --- |
| A | `Z(β)`, `Φ(β) = log Z(β)` | `souriauMassieuPotential`, finite grand-canonical partition surface | Owned by `SouriauThermodynamics` and `SouriauFenchelOnsagerBridge`. |
| B | first derivative gives moments | Souriau moment/readout derivative lane | Owned finitely for the β/μ grand-canonical channel. |
| C | Hessian = Fisher = covariance | `souriauFisherResponseMatrix` variance/covariance entries | Owned by `souriauFisherOnsager_proof_packet`. |
| D | Fenchel-Legendre entropy/contact and inverse metric | `souriauMassieu_contact_balance`, finite inverse response, `LegendreHessianInverseContext` | Contact/gap, finite `2×2` inverse metric, and smooth explicit-context inverse-Hessian surface are owned. |
| E | `σ = Xᵀ L X ≥ 0` | `souriauEntropyProduction_nonneg_of_positiveSemidefinite` | Owned under explicit PSD response hypothesis. |

Current Lean bridge:

- `lean/InfoGeometry/Canonical/SouriauThermodynamics.lean`
- `lean/InfoGeometry/Canonical/SouriauFenchelOnsagerBridge.lean`
- `lean/InfoGeometry/Canonical/SouriauMetriplecticContext.lean`
- `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- `lean/InfoGeometry/Geometry/LegendreHessianInverse.lean`

Search-facing theorem surfaces currently include:

- `finiteFenchelLegendre_contact_entropy`
- `finite_inverseFisherMetric_of_det_ne_zero`
- `LegendreHessianInverseContext.entropy_hessian_eq_fisher_inverse`
- `LegendreHessianInverseContext.legendre_hessian_inverse_packet`
- `finite_Hessian_eq_Fisher_eq_Onsager`
- `finite_FisherOnsager_entropyProduction_nonneg`
- `operatorial_Hessian_eq_Fisher_eq_Onsager`
- `operatorialFisherOnsager_entropyProduction_equation`

## Mandatory Boundary

Do not assert:

- full smooth coadjoint-orbit thermodynamics from the finite grand-canonical lane;
- infinite-dimensional metriplectic flow without an explicit context carrying the needed hypotheses;
- smooth `entropy_hessian_eq_fisher_inv` without an explicit Legendre/Hessian inverse context;
- positivity from terminology alone.

The finite inverse-metric theorem is only the non-spinodal algebraic statement:

```lean
theorem finite_inverseFisherMetric_of_det_ne_zero
    (hdet : fisher.det ≠ 0) :
    fisher.compose fisher.inverseMetric = identityMetric
      ∧ fisher.inverseMetric.compose fisher = identityMetric := ...
```

This closes the finite `2×2` inverse response packet.  The smooth theorem
surface is separately owned by `LegendreHessianInverseContext`, which requires
the analytic inverse-function/chain-rule data explicitly:

```lean
theorem LegendreHessianInverseContext.entropy_hessian_eq_fisher_inverse :
    entropyHessian.comp fisherHessian = ContinuousLinearMap.id ℝ Θ
      ∧ fisherHessian.comp entropyHessian =
          ContinuousLinearMap.id ℝ (MomentCoord Θ) := ...
```

This theorem closes the local theorem shape.  It still does not prove the
global inverse-function theorem; that theorem must supply the context fields.

The accepted finite theorem shape is:

```lean
theorem entropyProduction_nonneg
    (hPSD : responseMatrix.PositiveSemidefinite)
    (xβ xμ : ℝ) :
    0 ≤ entropyProduction xβ xμ := ...
```

The accepted operatorial theorem shape is:

```lean
theorem operatorialEntropyProduction_nonneg
    (hPSD : OperatorialMetricResponsePSD C)
    (X : EndH₂) :
    0 ≤ C.operatorialEntropyProduction X := ...
```

## Practical Rule

Translate prose into theorem packets first.  Edit Lean only after each claim has
an owner surface or an explicit hypothesis packet.  If the substrate is missing,
write a debt item rather than a theorem-shaped name.
