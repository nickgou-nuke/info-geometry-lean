# Native spectral sign and overlap chiral algebra: source contract

Date: 2026-11-17.

Status: independent mathematical/source review. Native acceptance of the repository candidates is pending; no build or declaration-axiom audit was performed for this ledger.

## Source and existing formalization

Nathaniel Craig, A gauge-invariant measure for lattice chiral fermions, arXiv:2610.09093v1, 6 October 2026.

Primary source: https://arxiv.org/abs/2610.09093v1

The uploaded 126-page PDF has SHA-256:

    45c8d3eaecb57f220a444192220464af64f00e3a15cab1d50c4719f62e934382

Sections 1-6, 9, 12 and the conclusions were read, together with the ordered-trace and scaling discussion in Sections 7.2-7.3. Equations on PDF pages 25-26 and 49-50 were checked visually. The supplied PDF and its full text extraction remain preserved in the task workspace. The PDF itself is not duplicated into this repository; its immutable version link, attachment identity, and digest are recorded in `docs/sources/native_matrix_overlap_20261117.json`. The integration review additionally checked the operator formulas on PDF page 14 visually. Printed page numbers in these sections are PDF page indices minus three.

Section 12, printed pages 59-60 / PDF pages 62-63, reports an existing sixteen-module Lean formalization of the mathematical companion for the SU(5) construction and its restriction to the four Standard Model groups. It reports warning-free compilation, axiom checks, and kernel replay, with a separate correspondence review of the formal statements and assumptions. This is an existing author formalization, not an absent proof. The present repository extension must be distinguished from that formalization and checked on this repository's own pinned toolchain. The author's verification has not been independently rerun in this review.

## Selected native target

Use an actual finite matrix H over a Mathlib RCLike field, with:

- H self-adjoint.
- H invertible.
- Gamma self-adjoint.
- Gamma * Gamma = 1.

Construct epsilon using Mathlib's actual continuous functional calculus with the real sign function applied to H. The finite matrix spectrum makes the sign function continuous on that spectrum, including at a possible isolated zero. Invertibility excludes zero and is used to prove that the sign squares to one. The intended native consequences are:

    epsilon† = epsilon
    epsilon * epsilon = 1.

Define the dimensionless, unit-spacing overlap operator:

    D = 1 + Gamma * epsilon.

No commutation hypothesis between Gamma and H, or between Gamma and epsilon, is allowed or needed. The matrix algebra retains its original noncommutative multiplication.

The source formulas are equations (1.2)-(1.7), printed pages 2-3 / PDF pages 5-6, and especially (2.6)-(2.9), printed page 11 / PDF page 14.

## Exact algebra and signs

The intended statements are:

    D† = 1 + epsilon * Gamma = Gamma * D * Gamma
    Gamma * D + D * Gamma = D * Gamma * D

The second equation is the Ginsparg-Wilson identity at unit lattice spacing. It follows by ordered multiplication and the two involution identities, not by commuting Gamma and epsilon.

The modified chirality is:

    GammaHat = Gamma * (1 - D) = -epsilon.

Thus the projectors and intertwining identities are:

    PHatMinus = (1 - GammaHat)/2 = (1 + epsilon)/2
    PHatPlus  = (1 + GammaHat)/2 = (1 - epsilon)/2
    PPlus     = (1 + Gamma)/2
    PMinus    = (1 - Gamma)/2

    D * GammaHat = -Gamma * D
    D * PHatMinus = PPlus * D


The existing `ChiralInvolution` and PR #395 Ginsparg-Wilson owners supply the paired-projector and intertwining algebra. This change exposes the actual positive spectral projector directly and proves that it equals the right projector of the constructed negative spectral sign.

The plus sign in PHatMinus = (1 + epsilon)/2 is essential: the paper's modified chirality is minus the sign of the Hermitian Wilson operator. A minus label on the fermion chirality projector does not mean that it selects the negative spectrum of H.

At physical spacing a the paper writes D_a = (1 + Gamma*epsilon)/a and the right-hand side of the Ginsparg-Wilson relation acquires a factor a. The selected native target uses the unit-spacing normalization and should not silently mix the two conventions.

## Concrete noncommuting witness

Over the real or complex 2-by-2 matrix algebra, take:

    Gamma = [[1,0],[0,-1]]
    H     = [[0,1],[1,0]].

Both are self-adjoint involutions, so H is invertible and its actual spectral sign is H. They anticommute:

    Gamma * H = [[0,1],[-1,0]]
    H * Gamma = [[0,-1],[1,0]].

The resulting overlap operator is:

    D  = [[1,1],[-1,1]]
    D† = [[1,-1],[1,1]]
    D† * D = 2 * I.

This is a genuinely non-self-adjoint operator with no Gamma-H commutation. In the complex instance its eigenvalues are 1+i and 1-i, consistent with the overlap circle.

A separate scope check is H = -Gamma: H is still an invertible self-adjoint involution but D = 0. Therefore the spectral gap or invertibility of H does not justify assuming D invertible or excluding overlap zero modes. The paper explicitly distinguishes these operators in Figure 3, printed page 12 / PDF page 15.

## Relation to the finite comparison and measure construction

The selected native target supplies legitimate chiral projectors. It does not by itself prove Section 5.

Lemma 5.1, printed pages 23-24 / PDF pages 26-27, assumes a smooth family of gapped Hermitian operators on one fixed finite-dimensional complex Hilbert space over a common open field domain. For their positive spectral projectors it defines:

    b_eta = i * integral_0^1 Tr(P_s * [partial_s P_s, delta_eta P_s]) ds
    Omega_s(eta,zeta) = i * Tr(P_s * [delta_eta P_s, delta_zeta P_s]).

The conclusions are:

    d b = Omega_1 - Omega_0
    exp(i * integral_loop b) = T_1(loop) / T_0(loop).

The return phase is the determinant on the transported chiral subspace, encoded by equation (4.16):

    T(loop) = det(1 - P_0 + P_0 * Q_1),

where equation (4.15) defines Kato transport by:

    derivative Q_t = [derivative P_t, P_t] * Q_t
    Q_0 = 1.

The full transport determinant det(Q_1) is not this subspace phase. The interpolation cylinder gives the holonomy comparison even for noncontractible loops; its orientation fixes the positive exponent and the ratio T_1/T_0.

For the paper's left-multiplication link variations, field-independent generators obey [delta_eta,delta_zeta] = -delta_[eta,zeta]. Consequently equation (4.18) contains:

    delta_eta L_zeta - delta_zeta L_eta + L_[eta,zeta] = Omega(eta,zeta).

This bracket term cannot be discarded by treating the noncommutative variations as commuting derivatives.

The finite comparison telescopes over successive lattices in equations (6.12)-(6.13), printed pages 30-31 / PDF pages 33-34. The further measure construction separately requires:

- An actual coarse/fine isometric embedding, fixed in the chosen component coordinates, and cancellation of the fixed added determinant factors.
- A uniform gap throughout the interpolating operators, not merely at the two endpoints.
- Convergence and exponential locality of the comparison current and its derivatives.
- Ordered color-trace anomaly cancellation and the covariant divergence identity.
- Vanishing residual curvature and fine-lattice loop phase.
- The global auxiliary connection, antiunitary pairing, and phase bounds of Section 9.
- Determinant-line reconstruction with trivial corrected holonomy on every closed loop.

These are not consequences of the isolated Ginsparg-Wilson algebra.

## Explicit boundaries

The selected finite result is applicable over RCLike fields. Section 5's determinant curvature and U(1) phase, however, are complex-Hilbert data. Any later real-only bridge must preserve the fixed complex structure and the correct complex or phase-weighted trace; replacing it by ordinary real trace would discard the phase.

No current, locality estimate, volume-uniform gap, differentiable spectral family, determinant holonomy, global fermion measure, or continuum quantum field theory is asserted by the selected owner.

The auxiliary refinement h = 3^(-n) in the paper holds the original physical lattice and overlap operator fixed. It is not an interacting continuum limit. Section 13, printed page 60 / PDF page 63, expressly leaves the interacting continuum theory open and identifies reflection positivity compatible with admissibility as further work. The Wilson-operator spectral gap is not a physical mass-gap theorem.

The native implementation must use the actual spectral functional calculus and actual matrix products, introduce no new axioms or proof placeholders, and be accepted only after checks on its exact integrated source and maintained dependency closure.

## Native owners and dependency direction

The immutable main baseline is `08c34e03f610b452e03422037949196dc7d92d6d`. This draft is stacked on PR #395, head `7378582cd5a458a39a99ceb8720d04c5a14e3ac1`, branch `codex/lattice-chiral-projector-20261117`. Lean `v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain unchanged.

| Owner | Carrier and role | Constructed dependency |
|---|---|---|
| New `Analysis/MatrixSpectralSign.lean` | Full `Matrix n n 𝕜`, finite index and `RCLike 𝕜` | Native continuous functional calculus and the Hermitian spectral theorem |
| Reused `OperatorAlgebra/GinspargWilson.lean` from #395 | Existing `ChiralInvolution` in an associative real algebra | Ordered GW and half-projector identities from two involutions |
| New `Geometry/MatrixOverlapDirac.lean` | Actual finite matrices | Constructs the negative spectral-sign involution, then invokes the existing owner |

The compatibility map is explicit. `negativeSignInvolution H hH hunit` has field `chi = -spectralSign H`, and its square proof is derived from actual CFC. Upstream's `1 - gamma.chi * epsilon.chi` consequently equals the paper's `1 + Γ * sign H`. Upstream `epsilon.Pright` equals `(1 + sign H)/2`; `overlapDirac_mul_Pright` is the paper's fermion-sector intertwiner. No spectral sign, eigenbasis, or square-one conclusion is supplied as unproved input data.

The initial search snapshot preceded #395's publication. After its appearance in the final remote check, its exact source was inspected and the overlapping new `Algebra/OverlapDirac.lean` was removed. The branch preserves the first draft checkpoint while integrating the parent branch, so the resulting PR diff contains only the two distinct new owners. The source-search record documents this superseding discovery. Parent #395's pending native status remains a dependency boundary.

The author already provides a much larger formalization, described in the primary companion report. Its newer-toolchain archive was neither inspected nor replayed here. This independently authored finite integration does not certify the author's global construction.

## Publication and acceptance boundary

Publication is a draft source checkpoint. Only an actual successful native compilation and compiled declaration-axiom report for the exact published bytes can mark the new owners kernel verified. Source scans, independent mathematical review, and a queued workflow are separate evidence. Root-package and broader integration acceptance remain separate gates.

The source API in this change does not separately expose normality `D†D = DD† = D + D†` or the analogous positive modified-projector intertwiner. They are mathematical consequences, not additional compiled declarations claimed by this change.
