# Hestenes phase, bilinears, and real flow: attachment reconciliation

## Provenance and acceptance

This note reconciles the mathematical claims in the three attachments received
on 2026-11-17: `Pasted text(20261117-081715).txt` (phase, Fourier, and uncertainty),
`Pasted text (2)(7).txt` (loxodromic corners and modular flow), and
`Pasted text (3)(2).txt` (spinor bilinears and stability). Their narrative and
assertions of verification are intake, not proof evidence.

The source baseline is `08c34e03f610b452e03422037949196dc7d92d6d`; the initial
seven-target implementation and the two additional owners are in draft PR #376.
The nine target owners remain pending kernel verification. Source review,
semantic review, compilation, and axiom inspection are separate acceptance
steps. This note adds no proof scope. The implementation contracts remain in
[Operator volume, observable covariance, and Schwartz uncertainty](OPERATOR_VOLUME_WAVEPACKET_UNCERTAINTY.md).

## Corrected claims

### Fourier phase order and Dirac signs

For `I² = -1`, `θ = k·x`, and `E₋ = cos θ - I sin θ`, direct differentiation
gives

\[
D E_-=-k\sin\theta-kI\cos\theta=-kI E_-.
\]

If `kI = -Ik`, the reordered identity is `-kI E₋ = I E₊ k`. The attachment's
`D E₋ = -kI E₊` is false: at `θ = π/2` its right side is `+k`, while the
derivative is `-k`. The anticommutation identity concerns composition
`D ∘ L_I = -L_I ∘ D`; the derivative of the constant element `I` is zero.

Associativity gives `D(ψ C) = (Dψ) C` for every constant right factor `C` when
`D` is the stated left constant-coefficient derivative. For a constant
amplitude `A` and `B² = -1`,

\[
D(Ae^{-B\theta})=-kABe^{-B\theta}.
\]

The extra condition `[B,γ₀]=0` permits the same exponential to factor through
the displayed mass term. It does not establish the impossibility of a Fourier
transform with another phase. Fourier inversion, differentiation under the
integral, and spacetime spectral claims require their own analytic hypotheses.

For signature `+---`, the displayed equation `Dψ B = m ψ γ₀` gives
`D²ψ = m² ψ (γ₀B)²` under constant-right-factor compatibility. Thus a commuting
spatial `B` gives the negative sign, while anticommuting `I₄` gives the positive
sign. Identifying `D²` with the wave operator requires the actual differential
domain and commuting mixed derivatives. These calculations do not classify all
real Dirac formulations or prove physical symmetry breaking. Lorentz covariance
must transform the coordinates/frame together with the spinor; commutation of
left and right multiplication alone does not establish it.

### Positive and indefinite pairings; the null-boundary counterexample

Keep the reversion pairing `K(ψ,φ) = scalar(ψ reverse φ)` separate from the
observer pairing `G(ψ,φ) = scalar(ψ γ₀ reverse φ γ₀)`. The former has an
indefinite signature: `K(1,1)=1`, `K(σ₁,σ₁)=-1`, and `K(1,σ₁)=0` already
refute a positive Cauchy--Schwarz bound for `K`. A positive pairing supports
Bessel/Gram inequalities once its identification with a native inner product
is proved. Positivity on a projected state requires `Pψ ≠ 0`.

Zero scalar reversion norm does not imply a null Dirac current. The explicit
counterexample `ψ = 1 + I₄` satisfies

\[
\psi\widetilde\psi=2I_4,\qquad
\psi\gamma_0\widetilde\psi=2\gamma_0,\qquad
(\psi\gamma_0\widetilde\psi)^2=4.
\]

Consequently the proposed `β = π/2` Weyl/null boundary is false. Under the
usual scalar--pseudoscalar Fierz identity, a null current requires both scalar
and pseudoscalar invariants to vanish. The observer density is not generally
the rest density `ρ`; a boosted rotor contributes the observer time component.

### Covariance, conservation, and boundedness are distinct obligations

For a Lorentz rotor, the current transforms as
`J(Rψ) = R J(ψ) reverse R`. Its invariant square and its components are
different readouts. A timelike vector `(cosh r, sinh r, 0, 0)` has square `1`
while its time component grows without bound. Thus causal covariance and
positive observer density do not imply a uniform boost bound.

An algebraic identity such as `J² = Ω₁² + Ω₂²` does not establish
`∂_μ J^μ = 0`, conservation of integrated hypersurface flux, an energy lower
bound, or stability under perturbations. Those require an equation, regularity,
boundary/integrability conditions, and the corresponding dynamical estimates.
In the historical `Clifford/HestenesDirac` owner, `mass_clock_law`,
`current_conserved`, and `spin_plane_transported` are supplied fields; the
extraction theorems do not derive those laws from a PDE.

### Contracting corners remain invertible at finite time

The repository convention is `P+ = (1+ε)/2`, `uPlus A = P+ A P-`, and
`uMinus A = P- A P+`. Its actual real bounded-operator conjugation group obeys

\[
\operatorname{Ad}_t(u_+A)=e^{2t}u_+A,\qquad
\operatorname{Ad}_t(u_-A)=e^{-2t}u_-A.
\]

For a nonzero corner, norm contraction occurs precisely at `t ≤ 0` for
`uPlus`, and `0 ≤ t` for `uMinus`; norm preservation occurs precisely at zero.
The attachment uses the opposite projector labels, so signs must be transported
with those labels. Every finite-time map still has inverse `Ad_(-t)`. Growth
over an unbounded time interval is compatible with boundedness of each map.
Restricting a group to a contractive half-line does not construct irreversible
dynamics, Hardy spaces, or Gamow resonances.

The name `Cl11LorentzAction.modularFlow` denotes a hyperbolic channel boost on
`H →L[ℝ] H`. A Tomita--Takesaki modular automorphism group requires a specified
von Neumann algebra, a faithful normal state or faithful normal semifinite
weight, and the corresponding representation. Native unitary conjugation
and C-star automorphisms preserve the C-star norm, but norm preservation alone
does not imply periodic motion or a discrete spectrum. No identification of
these different carriers follows from their shared name. A norm pulled back
through a representation need not be definite unless faithfulness is supplied.

Geometric Lorentz boosts can implement wedge modular flow in a unitary
Hilbert-space representation. The finite nonunitary spinor-matrix norm growth
above therefore does not exclude geometric boost modular flow on another
carrier. For the construction and this distinction, see Sorce,
[*A short proof of Tomita's theorem*](https://arxiv.org/html/2309.16762v3),
and Witten, [*Notes on Some Entanglement Properties of Quantum Field Theory*,
section 5.3](https://arxiv.org/html/1803.04993v6).

Reversion also needs its actual multiplication order. If an anti-involution
`r` swaps `P+` and `P-`, then

\[
r(P_+AP_-)=P_+r(A)P_-.
\]

It preserves this off-diagonal corner and swaps diagonal corners. A positive
Hilbert adjoint fixing orthogonal projectors exchanges off-diagonal corners
instead. Reversion on a Clifford algebra and conjugation of its endomorphism
algebra are separate operations.

### Real phase and uncertainty convention

For a real linear isometry `J` satisfying `J²=-id`, fix
`C_ab=⟨v_a,v_b⟩` and `K_ab=⟨Jv_a,v_b⟩`. Then
`⟨Ju,v⟩=-⟨u,Jv⟩`, and `[[C,-K],[K,C]]` is exactly the real Gram matrix of
`(v_a,Jv_a)`. Native Bessel gives `C_ab²+K_ab² ≤ C_aa C_bb`.

For actual symmetric real linear observables commuting with `J`, with
`v_a=A_aψ-⟨ψ,A_aψ⟩ψ`, the convention gives

\[
K_{ab}=-\tfrac12\langle\psi,J([A_a,A_b]\psi)\rangle.
\]

The vector formula uses the unit-state convention: the usual centered covariance
interpretation requires `⟨ψ,ψ⟩=1`. The Gram and phase identities themselves
hold for arbitrary `ψ`.

Changing to `⟨v_a,Jv_b⟩` reverses this sign. The attachment alternates between
the conventions; the squared bound alone hides the difference. A statistical
Cramér--Rao interpretation additionally requires a score identity and estimator
conditions. It is not supplied by Gram positivity.

## Native reuse map

Paths below are relative to `lean/InfoGeometry`; declaration names are scoped
by the named owner unless stated otherwise.

| Owner | Exact reusable surface and boundary |
|---|---|
| [Clifford/STAOperators](../lean/InfoGeometry/Clifford/STAOperators.lean) | `leftMul_rightMul_commute`, `rightMul_square_eq_neg`, `leftGamma_rightPhase_commute`: associative two-sided action; no analytic Fourier theorem. |
| [Canonical/HestenesPauliEvenClifford](../lean/InfoGeometry/Canonical/HestenesPauliEvenClifford.lean) and [HestenesCartanPhaseTransport](../lean/InfoGeometry/Canonical/HestenesCartanPhaseTransport.lean) | `clPlusPauliAlgEquiv`, `evenRealification_pseudoscalar`, `spacetimePseudoscalar_commutes`: actual even Clifford algebra and faithful real phase transport; the latter is a new PR target. |
| [Canonical/HestenesHermitianAdjoint](../lean/InfoGeometry/Canonical/HestenesHermitianAdjoint.lean) and [HestenesPauliEvenAdjoint](../lean/InfoGeometry/Canonical/HestenesPauliEvenAdjoint.lean) | `hestenesAdjoint`, `hestenesHermitianAdjoint`: observer adjoint and transported matrix adjoint. Pairing identification and positivity require the corresponding bridge. |
| [Canonical/ParaComplexNeutralForm](../lean/InfoGeometry/Canonical/ParaComplexNeutralForm.lean) | `plus_isotropic`, `minus_isotropic`, `form_self_eq_cross_pairing_sum`: require `AntiCompatible`; `NondegenerateDatum` assumes its nondegeneracy hypotheses. |
| [Geometry/RealDoubleWittNPFlow](../lean/InfoGeometry/Geometry/RealDoubleWittNPFlow.lean) | `wittBoost_preserves_plane_form`, `entropyFlow_preserves_causalForm`: conservation of the specified neutral forms. |
| [Canonical/KKTCore](../lean/InfoGeometry/Canonical/KKTCore.lean) and [Cl11LorentzAction](../lean/InfoGeometry/Canonical/Cl11LorentzAction.lean) | `decompose`, `modularAdjointFlow_scales_uPlus`, `modularAdjointFlow_scales_uMinus`, `modularAdjointFlow_add`, `modularAdjointFlow_fixes_gZeroPart`: actual real Peirce corners and conjugation group. |
| [Canonical/ModularFlowIsometry](../lean/InfoGeometry/Canonical/ModularFlowIsometry.lean) | `unitaryConjugation_norm` uses native `unitary C` in a C-star algebra; `flow_preserves_pulledNorm` depends on the supplied representation/intertwining data. |
| [QuantumGeometry/FiniteObservableGram](../lean/InfoGeometry/QuantumGeometry/FiniteObservableGram.lean) and [FiniteObservableGramCongruence](../lean/InfoGeometry/QuantumGeometry/FiniteObservableGramCongruence.lean) | `uncertaintyGram_posSemidef`, `uncertaintyGram_im`, `real_uncertainty_block_posSemidef`, `two_observable_uncertainty`: actual finite complex observables; new PR targets. |
| [Analysis/SchwartzUncertainty](../lean/InfoGeometry/Analysis/SchwartzUncertainty.lean) | `real_inner_position_deriv` is real; `norm_sq_le_four_pi_mul_position_mul_frequency` uses native complex Fourier/Plancherel on the real line with kernel `exp(-2π i x ξ)`; new PR target. |
| [QuantumGeometry/RealPhaseObservableGram](../lean/InfoGeometry/QuantumGeometry/RealPhaseObservableGram.lean) | `real_block_eq_gram`, `inner_sq_add_phase_inner_sq_le`, `phase_inner_eq_commutator`: arbitrary real orthogonal phase, actual symmetric observables. Uses native `Matrix.posSemidef_gram` and `Orthonormal.sum_inner_products_le`; validation pending. |
| [Canonical/Cl11LorentzCornerBounds](../lean/InfoGeometry/Canonical/Cl11LorentzCornerBounds.lean) | `norm_modularAdjointFlow_uPlus`, `norm_modularAdjointFlow_uMinus`, their `_le_iff` and `_eq_iff` forms, and `modularAdjointFlow_neg_apply`: native positive operator norms and finite-time inverse; validation pending. |

The fixed doubled-carrier Bessel result already exists as
`Canonical.OperatorialUncertainty.inner_sq_add_complex_i_inner_sq_le`.
Mathlib's `mellin_eq_fourier` already owns the logarithmic Mellin/Fourier
change of variables; the repository imports it through
`Analysis/LaplaceFourierComparison`.

## Remaining precise obligations

1. Prove the concrete even-Clifford reversion/observer pairing identities and
   construct the corresponding native positive inner product and phase isometry.
   A faithful algebra representation alone does not identify its module pairing.
2. Construct the common spinor function space, differential operator domain,
   Lorentz/frame action, Fourier intertwining, and boundary conditions needed
   for a Dirac square, current conservation, or hypersurface flux theorem.
3. Connect the real abstract Gram theorem to those concrete spinor observables;
   supply statistical score, normalization, and unbiasedness hypotheses for any
   Cramér--Rao application.
4. Supply a specific state/weight and a star-preserving isometric representation
   for any asserted modular/KMS identification. Construct the actual spaces,
   semigroups, and generator domains before making Hardy/resonance claims.
5. Prove any balanced tensor scalar actions, transport maps, and universal
   property before interpreting a dimension count as a multiparticle model.
   Real tensor products are associative, and a conceptual dependency diagram
   does not prove uniqueness of a physical synthesis.

These obligations remain explicit; none is replaced by a structure field
asserting the requested conclusion.
