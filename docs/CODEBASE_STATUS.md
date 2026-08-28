# Codebase Status

> Status: `verified active surface`
> Audited: 2026-08-28
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/REPOSITORY_BOUNDARY_POLICY.md](REPOSITORY_BOUNDARY_POLICY.md)

This file is the maintained prose status snapshot for the repository.

Last refreshed: 2026-08-28 (Europe/Sofia)

## Verified Scope Of This Refresh

This documentation repair audited the current repository structure against:

- `lakefile.lean`
- `lean/`
- `src/igf/`
- `tools/`

This refresh specifically validates a **fresh full build** of the codebase (8,130+ jobs passing cleanly with 0 errors, 0 sorries, and 0 custom axioms).

## Observed Live Surface

Lean:

- package: `infogeometry`
- entry file: `lean/InfoGeometry.lean`
- full umbrella: `lean/InfoGeometry/All.lean`
- canonical audit/architecture anchors:
  - `lean/InfoGeometry/Audit.lean`
  - `lean/InfoGeometry/Meta/`

## Capstone Theorem Closures (2026-08-28)

1. **Master Identity & Anomaly Cancellation** (`InfoGeometry.Arithmetic.UnifiedCapstone`):
   - $\det(1 - e^{-\beta H})^{-1} = \prod_{p} (1 - p^{-\beta})^{-1} = \sum_{n} n^{-\beta} = \zeta(\beta)$ for $\operatorname{Re}(\beta) > 1$.
   - Fermionic Möbius dual: $\sum_{n} \mu(n) n^{-\beta} = \zeta(\beta)^{-1}$.
   - Affine projective closure: $\zeta(\beta) \cdot \zeta(\beta)^{-1} = 1$.
   - Cayley critical line compactification: $|\mathcal{C}_{1/2}(s)|^2 = 1 \iff \operatorname{Re}(s) = 1/2$.

2. **Souriau–Bost–Connes Transition Theorem** (`InfoGeometry.GrandUnification.SouriauBostConnesTransitionTheorem`):
   - Ground state algebra isomorphic to Fibonacci fusion category $\mathcal{N}$ with $R$-matrix entries $\{e^{4\pi i/5}, e^{-2\pi i/5}\}$.
   - Order parameter is the quantum dimension $\phi = \frac{1 + \sqrt{5}}{2}$ satisfying $\phi^2 = \phi + 1$.

3. **Supergraded Superalgebra of the Cantor Crystal** (`InfoGeometry.Quantum.CantorCrystalSuperalgebraCapstone`):
   - Cuntz $\mathcal{O}_2$ grading operator $K = S_L S_L^* - S_R S_R^*$ satisfying $K^2 = 1$.
   - Bosonic projections $[P, K] = 0$ and fermionic hopping $\{T_{LR}, K\} = 0$.
   - Vanishing Witten Index in KMS state: $\text{WittenIndex}(\phi_{\text{KMS}}) = \operatorname{Tr}(K \cdot \rho) = 0$.

4. **Spectral Distance & Mass Gap Contraction** (`InfoGeometry.Analysis.SpectralDistance`):
   - Spectral gap $\lambda_{\text{gap}} = \ln 2 > 0$.
   - Strict exponential decay on excited subspace: $\|e^{-s H} v\| \le 2^{-s} \|v\| < \|v\|$ for all $s > 0$.

5. **Bost-Connes Criticality & Spontaneous Symmetry Breaking** (`InfoGeometry.Arithmetic.BostConnesCriticality`, `InfoGeometry.Canonical.BostConnesPhaseTransitionGaloisSSBCapstone`):
   - Divergence of harmonic series $\sum n^{-1} = \infty$ and prime reciprocals $\sum p^{-1} = \infty$.
   - Non-trace-class at $\beta = 1$ (Zeta pole).
   - Strict phase separation: high-temperature ($\beta \le 1$) unique KMS vs low-temperature ($\beta > 1$) Galois SSB into $\operatorname{Gal}(\mathbb{Q}^{\text{ab}}/\mathbb{Q}) \cong \hat{\mathbb{Z}}^\times$.

6. **Logarithmic Conformal Field Theory (logCFT)** (`InfoGeometry.Critical.LogCFTCritical`, `InfoGeometry.Critical.LogarithmicCFTCapstone`):
   - Virasoro generator $L_0 = h \cdot I + N$ developing a rank-2 Jordan cell with nilpotent square zero $N^2 = 0$.
   - $\mathfrak{osp}(1|2)$ superparity protection of the Jordan cell against smooth deformations.

7. **The Hilbert-Pólya Trinity** (`InfoGeometry.Arithmetic.HilbertPolyaThreeOperatorsOneObjectCapstone`):
   - Unification of the three operators: Bost-Connes Hamiltonian $H$, Hodge Laplacian $\Delta = D^2$, and chiral Dirac $D = \partial + \partial^*$.
   - $K = \log H$ acting on the fermionic Fock space on the critical line $s = 1/2 + it$.
   - Fredholm determinant $\det(1 - e^{-\beta H}) = \chi_{\text{alt}}(e^{-\beta H}) = 1/\zeta(\beta) = 0$.

8. **Thermodynamic LLM Theory Lane** (`InfoGeometry.LLM/`, 26 modules):
   - Query-Key attention as interaction energy in split-signature $Cl(1,1)$ Krein space.
   - Softmax attention weight as exact KMS/Gibbs thermal equilibrium.
   - MoE router as maximum-entropy Gibbs distribution under Bregman divergence.

## Documentation Truth Model

Current authority order:

1. `lean/` and `lakefile.lean` (The absolute truth layer, fully compiled as of 2026-07-09)
2. `src/igf/` and maintained scripts under `tools/`
3. this file
4. maintained entry docs listed in [README.md](../README.md) and [docs/README.md](README.md)
5. generated reports and reference-memory notes

## Markdown Corpus Result

The repository contains a large Markdown corpus, but most of it is not current
authority.

After the 2026-07-09 build cleanup:

- canonical docs were aligned around the currently compiling code surface.
- `docs/black_books/` remains untouched by design.

## Current Risks

- Historical handover and archive docs remain useful for provenance, but should
  not drive current edits, as many reflect pre-compilation states.
- The environment is currently stable and locked in, so future edits must preserve the `InfoGeometry.All` build matrix.

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
- **Do not “resolve” debt with wording.** Progress must be structural, not just textual.
- **Do not remove debt labels** unless there is a native explicit Lean proof term checked by the kernel closing that specific debt.
- **Real progress** = replacing certificate/witness fields with theorem-backed native derivations.
