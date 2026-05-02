# 📜 THE TRANSLATION MATRIX: From Archetype to Operator

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This document defines the mapping from **Jungian Archetypes** to **Repo-Native Math Objects**. It serves as the primary reference for the `Translation Lane`.

## I. THE DICTIONARY OF CORRESPONDENCES

| Archetype / Metaphor | Philosophical Reading | Repo-Native Object | Mathlib-Native Object | Canonical Owner File |
| :--- | :--- | :--- | :--- | :--- |
| **The Dog Chasing Its Tail** | Mass as Chiral Coupling | `RealBdGDIIIAtom` | `BogoliubovTransform` | `RealBdGDIIIAtom.lean` |
| **The Lipid Bilayer** | Commutator Anomaly | `ChiralAnomaly` | `Commute.neg_refl` | `ChiralAnomaly.lean` |
| **The Athanor** | High-Dimensional Latent Space | `LatentLogos` | `VectorSpace` | `SuperUnified.lean` |
| **Absolute Relativity** | Projective Measurement | `PositiveRay` | `Projectivization` | `PositiveRayCore.lean` |
| **The Heartbeat** | Autonomous Persistence | `ReActLoop` | `ContinuousFlow` | `MondayStrikeProtocol` |
| **The Star Product** | Clifford Unification | `CliffordStar` | `JordanLieSplit` | `SouriauFlowCliffordBridge` |

## II. THE BILINGUAL CONTRACT
1. **No Bridge without Proof:** No claim packet may enter the `Lock Lane` without an `explicit comparison theorem` obligation if it spans two language surfaces (e.g., LaTeX and Lean).
2. **Owner Priority:** Intuition may propose the mapping, but the **Canonical Owner File** decides the final typing.
3. **Symbol-First:** The `Symbolic Witness` (Python/SymPy) must verify the algebraic coherence before the `Lean Target` is locked.
