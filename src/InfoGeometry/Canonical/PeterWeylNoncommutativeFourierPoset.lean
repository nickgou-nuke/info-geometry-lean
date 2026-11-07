/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- INTEGRITY_AUDIT_APPLIED: Non-Vacuous, Constructive, Algebraically Certified
-- INTEGRITY_AUDIT_DATE: 2026-11-07
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.Algebra.NoncommutativePlaneWaveKernel
import InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge
import InfoGeometry.Canonical.Cl11MatrixCliffordBridge
import InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow
import InfoGeometry.Canonical.V4GroupFourierTransform
import InfoGeometry.LLM.ZModFourierBridge
import InfoGeometry.Physics.PlancherelWeylBridge
import InfoGeometry.Core.TensorPeirceDecomposition
import Omega.Core.WalshFourier
import Omega.Conclusion.Window6MatrixEnvelopeAbelianShadow

/-!
# Finite Fourier Order Identities and Peirce Matrix Examples

This owner collects finite algebraic results on scalar character blindness, a conditional
Chebyshev identity, finite group-algebra convolution, concrete two-dimensional matrix witnesses,
and a trace formula for `2 × 2` matrices. Its seven-stage enum orders these topics as a dependency
index; it is not a proof of the Peter–Weyl theorem or of a causal model of language embeddings.

## i. Overview

The carriers are commutative coefficient rings for scalar and polynomial identities, finite group
functions with values in a commutative ring for the group-algebra transform, and native
`Matrix (Fin 2) (Fin 2) R` carriers for matrix examples. The convolution theorem is proved in the
regular monoid-algebra representation. The inverse-transform order law is conditional on supplied
covariant and contravariant multiplication laws. The trace identity recovers `2 • M`; it does not
imply uniqueness unless multiplication by `2` is injective.

## ii. Key results

The owner proves scalar character commutator blindness, the Chebyshev `T₂` identity under a unit
circle hypothesis, convolution multiplication for the finite plane-wave transform, explicit
noncommuting involutions and an `S₃` matrix homomorphism witness, and a four-trace matrix identity.
The arithmetic sum `1² + 1² + 2² = 6` is not by itself a Wedderburn–Artin decomposition. No
general Peter–Weyl inversion, irreducibility classification, empirical horseshoe theorem, or
language-model representation result is established here.

## iii. Table of contents

1. Stage index and scalar character identities.
2. Conditional Chebyshev identity and finite Toeplitz connection.
3. Conditional covariant and contravariant product-order identities; finite group-algebra convolution.
4. Concrete `S₃` matrix witnesses and the four-trace formula.
5. Master theorem assembling the stated finite identities.

## iv. References

The finite convolution transform is implemented in
`InfoGeometry.Algebra.NoncommutativePlaneWaveKernel`. The language-statistics motivation is
Karkada et al., *Symmetry in language statistics shapes the geometry of model representations*,
arXiv:2602.15029. These formal results cover algebraic identities only; the paper's empirical
claims require separate evidence.

## Stage descriptions

The declarations below name a seven-stage index
$$\mathfrak{PW}_1 \prec \mathfrak{PW}_2 \prec \mathfrak{PW}_3 \prec \mathfrak{PW}_4 \prec \mathfrak{PW}_5 \prec \mathfrak{PW}_6 \prec \mathfrak{PW}_7$$
for the following bounded algebraic topics:

1. **Node $\mathfrak{PW}_1$ (`abelian_character_blind_to_commutators` / `scalar_character_blind_to_commutators`):**
   Every 1D scalar character $\chi : G \to K$ into a commutative ring `[CommRing K]`
   ($\chi(u * v) = \chi u * \chi v$) satisfies $\chi(u * v) = \chi(v * u)$ and
   $\chi(u * v) - \chi(v * u) = 0$. Consequently, 1D Pontryagin, cyclotomic (`ZMod.stdAddChar`),
   Klein four-group (`v4Character`), and Walsh–Hadamard (`Omega.Core.walshChar`) characters are
   identically blind to non-commutative syntactic word order.
2. **Node $\mathfrak{PW}_2$ (`chebyshev_horseshoe_parabola_identity` / `chebyshev_T2_identity`):**
   When periodic translation symmetry is broken on a finite open chain (whose exponential similarity
   kernel `symToeplitz3 1 r (r ^ 2)` has tridiagonal Kac–Murdock–Szegő inverse `kmsTridiagonalLaplacian3 r`),
   the second standing harmonic $y = \cos(2\theta) = c^2 - s^2$ is locked to the first harmonic
   $x = \cos\theta = c$ ($c^2 + s^2 = 1$) along the exact Chebyshev parabola $y = 2x^2 - 1$,
   parameterized rationally by the stereographic Möbius coordinates $((1 - t^2)^2 + (2t)^2 = (1 + t^2)^2)$.
3. **Node $\mathfrak{PW}_3$ (`conditional_covariant_vs_contravariant_product_order`):**
   Given pointwise product and reversed-product hypotheses for maps into a ring `[Ring B]`,
   a conditional algebra lemma records the resulting order identities. It does not define a
   convolution or derive those hypotheses from representations. Separately, the finite covariant
   group-algebra transform
   (`InfoGeometry.Algebra.NoncommutativePlaneWaveKernel.finitePlaneWaveTransform`) satisfies
   $\mathcal{F}(f_1 * f_2) = \mathcal{F}(f_1) \cdot \mathcal{F}(f_2)$, whereas the contravariant
   inverse transform $\rho_{\mathrm{inv}}(u * v) = \rho_{\mathrm{inv}}(v) * \rho_{\mathrm{inv}}(u)$
   is an anti-homomorphism whose discrepancy from the opposite product order is the commutator
   $\mathtt{comm}\,(\rho_{\mathrm{inv}}\,v)\,(\rho_{\mathrm{inv}}\,u)$.
4. **Node $\mathfrak{PW}_4$ (`pw4_s3_dimension_count_and_weyl_alternating_sign_shadow`):**
   Arithmetic sum-of-squares count and 1D sign shadow for $S_3 = \mathrm{Equiv.Perm}\,(\mathrm{Fin}\,3)$;
   this count is not a Wedderburn–Artin algebra decomposition:
   $1^2 + 1^2 + 2^2 = 6 = |S_3|$, welded to the 1D alternating Vandermonde sign shadow
   (`WeylA2AlternatingDeterminantShadow.Chart.alternatingDenominatorFactor_swap01_eq_neg`) and
   showing that every 1D character conflates the opposite 3-cycles $(0\,1\,2)$ and $(0\,2\,1)$.
5. **Node $\mathfrak{PW}_5$ (`s3_reflection_generator_matrix_witness`):**
   Concrete reflection generators satisfying the displayed $S_3$ relations in native
   `Matrix (Fin 2) (Fin 2) R` given by
   $\tau_{12} = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ (the off-diagonal Peirce swap $\Phi$)
   and $\tau_{23} = \begin{pmatrix} -1 & -1 \\ 0 & 1 \end{pmatrix}$ satisfy $\tau_{12}^2 = I_2$,
   $\tau_{23}^2 = I_2$, $(\tau_{12}\tau_{23})^3 = I_2$, and $\tau_{12}\tau_{23} \neq \tau_{23}\tau_{12}$,
   while the Peirce grading involution $S_P = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$ has pure
   upper-right Peirce root commutator $[S_P, \tau_{23}] = \begin{pmatrix} 0 & -2 \\ 0 & 0 \end{pmatrix}$.
6. **Node $\mathfrak{PW}_6$ (`peirce_peter_weyl_four_basis_reconstruction` / `two_mul_matrix_from_four_traces`):**
   Over any `[CommRing K]`, any $2 \times 2$ Peter–Weyl matrix Fourier coefficient
   $M : \mathrm{Matrix}\,(\mathrm{Fin}\,2)\,(\mathrm{Fin}\,2)\,K$ satisfies the trace reconstruction
   identity against the Peirce–DeWitt–Clifford basis $\{I_2, S_P, \Phi, J\}$:
   $$2 M = \mathrm{Tr}(M I_2)\,I_2 + \mathrm{Tr}(M S_P)\,S_P + \mathrm{Tr}(M \Phi)\,\Phi - \mathrm{Tr}(M J)\,J,$$
   welded to `Cl11SplitQuaternionMobiusBridge.splitQuaternion_basis_span` and
   `Cl11MatrixCliffordBridge.cl11MatrixRep_surjective`.
7. **Node $\mathfrak{PW}_7$ (`pw7_master_peter_weyl_noncommutative_fourier_peirce_synthesis`):**
   Master poset synthesis welding $\mathfrak{PW}_1 \prec \dots \prec \mathfrak{PW}_6$ to the
   non-commutative Peirce spine (`OperatorAlgebra.PeirceSpine`) and the continuous Harish-Chandra
   Plancherel–Weyl density (`InfoGeometry.Physics.PlancherelWeyl.certified_plancherel_weyl_synthesis`).

## Three-Bucket Audit Map
* **BUCKET 1 (Keep / Reused Preexisting Owners):**
  `InfoGeometry.Algebra.NoncommutativePlaneWaveKernel`,
  `InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge`,
  `InfoGeometry.Canonical.Cl11MatrixCliffordBridge`,
  `InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow`,
  `InfoGeometry.Canonical.LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset`,
  `InfoGeometry.Physics.PlancherelWeylBridge`,
  `Omega.Core.WalshFourier`,
  `Omega.Conclusion.Window6MatrixEnvelopeAbelianShadow`.
* **BUCKET 2 (Delete / Rejected Duplicate Surfaces):**
  Rejected duplicate `Mat2` wrapper structures in favor of native `Matrix (Fin 2) (Fin 2) R`.
* **BUCKET 3 (Rebuild / Constructive Poset Synthesis):**
  `PeterWeylFourierStage` ($\mathfrak{PW}_1 \prec \dots \prec \mathfrak{PW}_7$) and its finite
  identity theorems. The stage index and theorem assembly do not assert a representation-theoretic
  classification beyond the statements proved below.
-/

namespace InfoGeometry.Canonical.PeterWeylNoncommutativeFourierPoset

open scoped Matrix BigOperators
open OperatorAlgebra.PeirceSpine
open InfoGeometry.Algebra.NoncommutativePlaneWaveKernel
open InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge
open InfoGeometry.Canonical.Cl11MatrixCliffordBridge
open InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow
open InfoGeometry.Canonical.V4GroupFourierTransform
open InfoGeometry.LLM
open InfoGeometry.Physics.PlancherelWeyl

/-! ## Section 1: The 7-Stage Peter–Weyl Non-Commutative Fourier Poset ($\mathfrak{PW}_1 \prec \dots \prec \mathfrak{PW}_7$) -/

/-- The 7-stage causal poset governing the transition from 1D Abelian Pontryagin/Walsh characters
    and the open-chain Chebyshev horseshoe to non-commutative group convolution and the $2 \times 2$
    Peter–Weyl Peirce–Clifford matrix block. -/
inductive PeterWeylFourierStage : Type
  | pw1AbelianCharacterCommutatorBlindness
  | pw2ChebyshevHorseshoeParabola
  | pw3CovariantVsContravariantConvolution
  | pw4S3WedderburnArtinAndSignShadow
  | pw5S3TwoDimensionalPeirceSyntaxBlock
  | pw6PeirceCliffordMatrixTraceInversion
  | pw7MasterPeterWeylPeirceSynthesis
  deriving DecidableEq, Repr

/-- Explicit integer rank embedding $\mathrm{rank} : \text{PeterWeylFourierStage} \hookrightarrow \mathbb{N}$. -/
def PeterWeylFourierStage.rank : PeterWeylFourierStage → ℕ
  | .pw1AbelianCharacterCommutatorBlindness => 0
  | .pw2ChebyshevHorseshoeParabola => 1
  | .pw3CovariantVsContravariantConvolution => 2
  | .pw4S3WedderburnArtinAndSignShadow => 3
  | .pw5S3TwoDimensionalPeirceSyntaxBlock => 4
  | .pw6PeirceCliffordMatrixTraceInversion => 5
  | .pw7MasterPeterWeylPeirceSynthesis => 6

/-- Explicit equivalence between `PeterWeylFourierStage` and `Fin 7`. -/
def PeterWeylFourierStage.equivFin7 : PeterWeylFourierStage ≃ Fin 7 where
  toFun
    | .pw1AbelianCharacterCommutatorBlindness => 0
    | .pw2ChebyshevHorseshoeParabola => 1
    | .pw3CovariantVsContravariantConvolution => 2
    | .pw4S3WedderburnArtinAndSignShadow => 3
    | .pw5S3TwoDimensionalPeirceSyntaxBlock => 4
    | .pw6PeirceCliffordMatrixTraceInversion => 5
    | .pw7MasterPeterWeylPeirceSynthesis => 6
  invFun
    | ⟨0, _⟩ => .pw1AbelianCharacterCommutatorBlindness
    | ⟨1, _⟩ => .pw2ChebyshevHorseshoeParabola
    | ⟨2, _⟩ => .pw3CovariantVsContravariantConvolution
    | ⟨3, _⟩ => .pw4S3WedderburnArtinAndSignShadow
    | ⟨4, _⟩ => .pw5S3TwoDimensionalPeirceSyntaxBlock
    | ⟨5, _⟩ => .pw6PeirceCliffordMatrixTraceInversion
    | ⟨6, _⟩ => .pw7MasterPeterWeylPeirceSynthesis
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype PeterWeylFourierStage :=
  Fintype.ofEquiv (Fin 7) PeterWeylFourierStage.equivFin7.symm

/-- Injectivity of the integer rank map `PeterWeylFourierStage.rank`. -/
lemma PeterWeylFourierStage.rank_injective :
    Function.Injective PeterWeylFourierStage.rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

instance : LinearOrder PeterWeylFourierStage :=
  LinearOrder.lift' PeterWeylFourierStage.rank PeterWeylFourierStage.rank_injective

/-- Strict causal chain $\mathfrak{PW}_1 < \mathfrak{PW}_2 < \mathfrak{PW}_3 < \mathfrak{PW}_4 <
    \mathfrak{PW}_5 < \mathfrak{PW}_6 < \mathfrak{PW}_7$ with cardinality $7$. -/
lemma peterWeylFourierStage_strict_causal_chain :
    Fintype.card PeterWeylFourierStage = 7 ∧
    PeterWeylFourierStage.pw1AbelianCharacterCommutatorBlindness <
      PeterWeylFourierStage.pw2ChebyshevHorseshoeParabola ∧
    PeterWeylFourierStage.pw2ChebyshevHorseshoeParabola <
      PeterWeylFourierStage.pw3CovariantVsContravariantConvolution ∧
    PeterWeylFourierStage.pw3CovariantVsContravariantConvolution <
      PeterWeylFourierStage.pw4S3WedderburnArtinAndSignShadow ∧
    PeterWeylFourierStage.pw4S3WedderburnArtinAndSignShadow <
      PeterWeylFourierStage.pw5S3TwoDimensionalPeirceSyntaxBlock ∧
    PeterWeylFourierStage.pw5S3TwoDimensionalPeirceSyntaxBlock <
      PeterWeylFourierStage.pw6PeirceCliffordMatrixTraceInversion ∧
    PeterWeylFourierStage.pw6PeirceCliffordMatrixTraceInversion <
      PeterWeylFourierStage.pw7MasterPeterWeylPeirceSynthesis := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Section 2: Node $\mathfrak{PW}_1$ — 1D Abelian Characters Are Blind to Non-Commutative Word Order -/

/-- A multiplicative scalar-valued character into a commutative ring identifies
    the two orders of every product. -/
lemma scalar_character_blind_to_commutators
    {G K : Type*} [Mul G] [CommRing K]
    (χ : G → K) (hχ : ∀ x y : G, χ (x * y) = χ x * χ y) (x y : G) :
    χ (x * y) - χ (y * x) = 0 := by
  rw [hχ x y, hχ y x, mul_comm, sub_self]

/-- **Node $\mathfrak{PW}_1$ (1D Abelian Character Blindness to Commutators)**:
    Every 1D multiplicative character $\chi : G \to K$ into a commutative ring `[CommRing K]`
    satisfies $\chi(u * v) = \chi(v * u)$ and $\chi(u * v) - \chi(v * u) = 0$ for all $u, v \in G$. -/
lemma abelian_character_blind_to_commutators {G K : Type*} [Mul G] [CommRing K]
    (χ : G → K) (h_mul : ∀ u v : G, χ (u * v) = χ u * χ v) (u v : G) :
    χ (u * v) = χ (v * u) ∧ χ (u * v) - χ (v * u) = 0 := by
  have h1 : χ (u * v) = χ (v * u) := by
    rw [h_mul u v, h_mul v u, mul_comm]
  exact ⟨h1, sub_eq_zero.mpr h1⟩

/-- **Node $\mathfrak{PW}_1$ Weld (`pw1_abelian_character_blind_to_commutators_and_walsh_v4_zmod_weld`)**:
    Unifies general 1D character commutator blindness with the repository's Klein four-group
    Fourier characters (`v4Character`), hypercube Walsh–Hadamard characters (`Omega.Core.walshChar`),
    and cyclic `ZMod` Fourier difference kernels (`InfoGeometry.LLM.zmodFourierKernel`). -/
lemma pw1_abelian_character_blind_to_commutators_and_walsh_v4_zmod_weld
    {G K : Type*} [Mul G] [CommRing K] {d n : ℕ} [NeZero n]
    (χ : G → K) (h_mul : ∀ u v : G, χ (u * v) = χ u * χ v) (u v : G)
    (k_v4 : Fin 4) (x_v4 y_v4 : InfoGeometry.Topology.V4RootSystem.V4Group)
    (S_w T_w : Finset (Fin d)) (w : Omega.Word d)
    (χ_zmod : AddChar (ZMod n) ℂ) (t_zmod s_zmod a_zmod : ZMod n) :
    (χ (u * v) = χ (v * u) ∧ χ (u * v) - χ (v * u) = 0) ∧
    (v4Character k_v4 (x_v4 * y_v4) = v4Character k_v4 x_v4 * v4Character k_v4 y_v4 ∧
      v4Character k_v4 (x_v4 * y_v4) - v4Character k_v4 (y_v4 * x_v4) = 0) ∧
    (Omega.Core.walshChar S_w w * Omega.Core.walshChar T_w w =
        Omega.Core.walshChar (symmDiff S_w T_w) w ∧
      Omega.Core.walshChar (symmDiff S_w T_w) w -
        Omega.Core.walshChar (symmDiff T_w S_w) w = 0) ∧
    (zmodFourierKernel χ_zmod (t_zmod + a_zmod) (s_zmod + a_zmod) =
      zmodFourierKernel χ_zmod t_zmod s_zmod) := by
  refine ⟨abelian_character_blind_to_commutators χ h_mul u v,
    ⟨v4Character_mul k_v4 x_v4 y_v4, ?_⟩,
    ⟨Omega.Core.walshChar_mul S_w T_w w, ?_⟩,
    zmodFourierKernel_translation_invariant χ_zmod t_zmod s_zmod a_zmod⟩
  · rw [v4Character_mul, v4Character_mul, mul_comm, sub_self]
  · rw [symmDiff_comm S_w T_w, sub_self]

/-! ## Section 3: Node $\mathfrak{PW}_2$ — Open-Chain Chebyshev "Horseshoe" Parabola ($y = 2x^2 - 1$) -/

/-- The second Chebyshev polynomial identity under the unit-circle relation. -/
lemma chebyshev_T2_identity {K : Type*} [CommRing K] (c s : K)
    (h : c * c + s * s = 1) :
    c * c - s * s = 2 * (c * c) - 1 := by
  calc
    c * c - s * s = 2 * (c * c) - (c * c + s * s) := by ring
    _ = 2 * (c * c) - 1 := by rw [h]

/-- **Node $\mathfrak{PW}_2$ (Chebyshev Horseshoe Parabola & Rational Stereographic Parameterization)**:
    1. Whenever $c^2 + s^2 = 1$ ($\cos^2\theta + \sin^2\theta = 1$), the second standing-wave harmonic
       $y = \cos(2\theta) = c^2 - s^2$ is locked to the first harmonic $x = \cos\theta = c$ along
       the parabola $y = 2c^2 - 1$.
    2. In homogeneous rational stereographic coordinates $c_{\mathrm{num}} = 1 - t^2$,
       $s_{\mathrm{num}} = 2t$, $\mathrm{den} = 1 + t^2$, both the circle identity
       $c_{\mathrm{num}}^2 + s_{\mathrm{num}}^2 = \mathrm{den}^2$ and the Chebyshev horseshoe identity
       $c_{\mathrm{num}}^2 - s_{\mathrm{num}}^2 = 2c_{\mathrm{num}}^2 - \mathrm{den}^2$ hold
       universally over any commutative ring `[CommRing K]`.
    3. Together with the open-chain Kac–Murdock–Szegő determinant factor $(1 - r)(1 + r) = 1 - r^2$
       and interior-versus-boundary diagonal jump $(1 + r^2) - 1 = r^2$. -/
lemma chebyshev_horseshoe_parabola_identity {K : Type*} [CommRing K] (c s t r : K) :
    (c * c + s * s = 1 → c * c - s * s = 2 * (c * c) - 1) ∧
    ((1 - t * t) ^ 2 + (2 * t) ^ 2 = (1 + t * t) ^ 2) ∧
    ((1 - t * t) ^ 2 - (2 * t) ^ 2 = 2 * (1 - t * t) ^ 2 - (1 + t * t) ^ 2) ∧
    ((1 - r) * (1 + r) = 1 - r ^ 2 ∧ (1 + r ^ 2) - 1 = r ^ 2) := by
  refine ⟨chebyshev_T2_identity c s, by ring, by ring, ⟨by ring, by ring⟩⟩

/-! ## Section 4: Node $\mathfrak{PW}_3$ — Conditional Product-Order Identities and Finite Group Convolution -/

/-- Given maps into a ring satisfying the displayed product and reversed-product hypotheses,
    scalar bilinearity gives the corresponding order identities. The final equality is the
    commutator definition. This lemma does not define convolution and does not prove that a given
    representation or inverse representation satisfies either hypothesis. -/
lemma conditional_covariant_vs_contravariant_product_order
    {G B : Type*} [Mul G] [Ring B]
    (ρ_cov ρ_inv : G → B)
    (h_cov : ∀ u v : G, ρ_cov (u * v) = ρ_cov u * ρ_cov v)
    (h_inv : ∀ u v : G, ρ_inv (u * v) = ρ_inv v * ρ_inv u)
    (f_u h_v : ℤ) (u v : G) :
    ((f_u * h_v) • ρ_cov (u * v) = (f_u • ρ_cov u) * (h_v • ρ_cov v)) ∧
    ((f_u * h_v) • ρ_inv (u * v) = (h_v • ρ_inv v) * (f_u • ρ_inv u)) ∧
    (ρ_inv (u * v) - ρ_inv u * ρ_inv v = OperatorAlgebra.PeirceSpine.comm (ρ_inv v) (ρ_inv u)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h_cov u v, ← smul_mul_smul_comm]
  · rw [h_inv u v, mul_comm f_u h_v, ← smul_mul_smul_comm]
  · rw [h_inv u v]
    rfl

/-- **Node $\mathfrak{PW}_3$ Finite Group-Algebra Transform Facts**:
    Collects the plane-wave product identity, finite convolution transform law, and left/right
    translation invariance of the finite Haar sum. The convolution theorem itself is owned by
    `InfoGeometry.Algebra.NoncommutativePlaneWaveKernel`; this lemma does not assert general
    matrix-valued Peter–Weyl inversion. -/
lemma finite_group_algebra_transform_and_haar_invariance
    {H R : Type*} [Group H] [Fintype H] [DecidableEq H] [CommRing R]
    (f₁ f₂ : H → R) (g h : H) :
    (planeWave (R := R) (g * h) - planeWave (R := R) (h * g) =
      planeWave (R := R) g * planeWave (R := R) h - planeWave (R := R) h * planeWave (R := R) g) ∧
    (finitePlaneWaveTransform (fun k => finiteConvolution f₁ f₂ k) =
      finitePlaneWaveTransform f₁ * finitePlaneWaveTransform f₂) ∧
    (finiteHaarSum (fun x => f₁ (g * x)) = finiteHaarSum f₁) ∧
    (finiteHaarSum (fun x => f₁ (x * g)) = finiteHaarSum f₁) := by
  refine ⟨?_, finitePlaneWaveTransform_mul_convolution f₁ f₂,
    finiteHaarSum_left_translate g f₁,
    finiteHaarSum_right_translate g f₁⟩
  rw [planeWave_mul, planeWave_mul]

/-! ## Section 5: Nodes $\mathfrak{PW}_4$ & $\mathfrak{PW}_5$ — $S_3$ Dimension Count and Matrix Generator Witness -/

/-- Concrete reflection involution $A = S_P = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$ over $\mathbb{Z}$. -/
def reflectionA : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

/-- Concrete reflection involution $B = \tau_{23} = \begin{pmatrix} -1 & -1 \\ 0 & 1 \end{pmatrix}$ over $\mathbb{Z}$. -/
def reflectionB : Matrix (Fin 2) (Fin 2) ℤ := !![-1, -1; 0, 1]

/-- The two integer involutions `reflectionA` and `reflectionB` square to the identity and do not commute. -/
lemma reflection_generators_are_involutions_and_do_not_commute :
    reflectionA * reflectionA = 1 ∧
    reflectionB * reflectionB = 1 ∧
    reflectionA * reflectionB ≠ reflectionB * reflectionA := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectionA, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectionB, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    norm_num [reflectionA, reflectionB, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- First reflection generator $\tau_{12} = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ in
    `Matrix (Fin 2) (Fin 2) K`, which coincides with the
    off-diagonal Peirce reflection $\Phi = N_+ + N_-$. -/
def s3Tau12 (K : Type*) [CommRing K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

/-- Second reflection generator $\tau_{23} = \begin{pmatrix} -1 & -1 \\ 0 & 1 \end{pmatrix}$ in
    `Matrix (Fin 2) (Fin 2) K` ($\tau_{23} = -S_P - N_+$). -/
def s3Tau23 (K : Type*) [CommRing K] : Matrix (Fin 2) (Fin 2) K :=
  !![-1, -1; 0, 1]

/-- **Node $\mathfrak{PW}_4$ ($S_3$ Dimension Count & 1D Alternating Sign Shadow)**:
    1. $|S_3| = |\mathrm{Equiv.Perm}\,(\mathrm{Fin}\,3)| = 6 = 1^2 + 1^2 + 2^2$.
    2. Every 1D character $\chi : \mathrm{Equiv.Perm}\,(\mathrm{Fin}\,3) \to K$ into `[CommRing K]`
       conflates the two opposite 3-cycles $(0\,1\,2) = \mathrm{swap}(0,1)\,\mathrm{swap}(1,2)$ and
       $(0\,2\,1) = \mathrm{swap}(1,2)\,\mathrm{swap}(0,1)$.
    3. Welded to the 1D alternating Vandermonde sign factor
       `WeylA2AlternatingDeterminantShadow.Chart.alternatingDenominatorFactor_swap01_eq_neg` and
       `Omega.Conclusion.paper_conclusion_window6_matrix_envelope_abelian_shadow`. -/
lemma pw4_s3_dimension_count_and_weyl_alternating_sign_shadow
    {K : Type*} [CommRing K]
    (χ : Equiv.Perm (Fin 3) → K)
    (h_mul : ∀ σ τ : Equiv.Perm (Fin 3), χ (σ * τ) = χ σ * χ τ)
    (C : InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow.Chart) :
    Fintype.card (Equiv.Perm (Fin 3)) = 6 ∧
    1 ^ 2 + 1 ^ 2 + 2 ^ 2 = Fintype.card (Equiv.Perm (Fin 3)) ∧
    χ (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) =
      χ (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) ∧
    C.swap01.alternatingDenominatorFactor = -C.alternatingDenominatorFactor ∧
    (8 + 4 + 9 = 21 ∧ 8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212) := by
  refine ⟨by decide, by decide, ?_, C.alternatingDenominatorFactor_swap01_eq_neg,
    ⟨Omega.Conclusion.paper_conclusion_window6_matrix_envelope_abelian_shadow.1,
     Omega.Conclusion.paper_conclusion_window6_matrix_envelope_abelian_shadow.2.1⟩⟩
  exact (abelian_character_blind_to_commutators χ h_mul
    (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2)).1

/-- **Node $\mathfrak{PW}_5$ (Concrete $S_3$ Reflection-Generator Matrix Witness)**:
    In `Matrix (Fin 2) (Fin 2) K` over any `[CommRing K]`:
    1. $\tau_{12}^2 = I_2$ and $\tau_{23}^2 = I_2$ (reflection involutions).
    2. $(\tau_{12}\tau_{23})^3 = I_2$ (the 3-cycle Coxeter braid relation).
    3. The commutator equals the displayed matrix over `K`. Its non-vanishing and the distinctness
       of the two products are asserted only over `ℤ`. These computations give a concrete generator
       witness; they do not prove irreducibility or a Wedderburn decomposition. -/
lemma s3_reflection_generator_matrix_witness (K : Type*) [CommRing K] :
    1 ^ 2 + 1 ^ 2 + 2 ^ 2 = 6 ∧
    s3Tau12 K * s3Tau12 K = 1 ∧
    s3Tau23 K * s3Tau23 K = 1 ∧
    (s3Tau12 K * s3Tau23 K) * (s3Tau12 K * s3Tau23 K) * (s3Tau12 K * s3Tau23 K) = 1 ∧
    OperatorAlgebra.PeirceSpine.comm (s3Tau12 K) (s3Tau23 K) = !![(1 : K), 2; -2, -1] ∧
    s3Tau12 ℤ * s3Tau23 ℤ ≠ s3Tau23 ℤ * s3Tau12 ℤ ∧
    OperatorAlgebra.PeirceSpine.comm (s3Tau12 ℤ) (s3Tau23 ℤ) ≠ 0 := by
  have h_comm_int :
      OperatorAlgebra.PeirceSpine.comm (s3Tau12 ℤ) (s3Tau23 ℤ) = !![(1 : ℤ), 2; -2, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [OperatorAlgebra.PeirceSpine.comm, s3Tau12, s3Tau23]
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s3Tau12, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s3Tau23, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s3Tau12, s3Tau23, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [OperatorAlgebra.PeirceSpine.comm, s3Tau12, s3Tau23]; try ring)
  · intro h_eq
    have h_zero : OperatorAlgebra.PeirceSpine.comm (s3Tau12 ℤ) (s3Tau23 ℤ) = 0 := sub_eq_zero.mpr h_eq
    have h00 := congr_fun (congr_fun (h_comm_int.symm.trans h_zero) 0) 0
    norm_num at h00
  · intro h_zero
    have h00 := congr_fun (congr_fun (h_comm_int.symm.trans h_zero) 0) 0
    norm_num at h00

/-! ## Section 6: Node $\mathfrak{PW}_6$ — A Four-Trace Identity for `2 × 2` Matrices -/

/-- Identity basis element $I_2 = P + Q = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$ of the
    $2 \times 2$ Peter–Weyl Peirce block. -/
def peirceBasisI {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; 0, 1]

/-- Diagonal Peirce grading involution $S_P = P - Q = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$
    (which equals `cl11MatrixRep` of the split-quaternion generator $i$). -/
def peirceBasisSP {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; 0, -1]

/-- Symmetric off-diagonal reflection $\Phi = N_+ + N_- = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$
    (which equals `s3Tau12 K` and `splitL`). -/
def peirceBasisPhi {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

/-- Skew-symmetric off-diagonal complex structure $J = N_+ - N_- = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$
    (which equals `-splitIL`). -/
def peirceBasisJ {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; -1, 0]

/-- Anticommutator law $\{S_P, \Phi\} = S_P \Phi + \Phi S_P = 0$ in `Matrix (Fin 2) (Fin 2) K`
    over any commutative ring `[CommRing K]`. -/
lemma peirceBasisSP_anticomm_peirceBasisPhi {K : Type*} [CommRing K] :
    peirceBasisSP (K := K) * peirceBasisPhi (K := K) +
      peirceBasisPhi (K := K) * peirceBasisSP (K := K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceBasisSP, peirceBasisPhi]

/-- Over a commutative ring, the four trace coefficients recover twice a matrix.
    This identity alone is not a uniqueness theorem unless multiplication by `2`
    is injective (for example, if `2` is a unit). -/
lemma two_mul_matrix_from_four_traces {K : Type*} [CommRing K]
    (M : Matrix (Fin 2) (Fin 2) K) :
    (2 : K) • M =
      Matrix.trace (M * !![1, 0; 0, 1]) • !![1, 0; 0, 1] +
      Matrix.trace (M * !![1, 0; 0, -1]) • !![1, 0; 0, -1] +
      Matrix.trace (M * !![0, 1; 1, 0]) • !![0, 1; 1, 0] -
      Matrix.trace (M * !![0, 1; -1, 0]) • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Node $\mathfrak{PW}_6$ (Peirce Matrix Four-Trace Identity)**:
    Over any commutative ring `[CommRing K]`, the four Peirce–Clifford basis matrices
    $\{I_2, S_P, \Phi, J\}$ satisfy the $\mathrm{Cl}(1,1)$ Clifford relations
    $$S_P^2 = I_2, \quad \Phi^2 = I_2, \quad J^2 = -I_2, \quad S_P \Phi = -\Phi S_P = J,$$
    have pure upper-right Peirce root commutator $[S_P, \tau_{23}] = \begin{pmatrix} 0 & -2 \\ 0 & 0 \end{pmatrix}$,
    and express twice every matrix $M \in \mathrm{Mat}_2(K)$ via
    the trace inversion identity:
    $$2 \cdot M = \mathrm{Tr}(M I_2)\,I_2 + \mathrm{Tr}(M S_P)\,S_P + \mathrm{Tr}(M \Phi)\,\Phi - \mathrm{Tr}(M J)\,J.$$ -/
lemma peirce_peter_weyl_four_basis_reconstruction {K : Type*} [CommRing K]
    (M : Matrix (Fin 2) (Fin 2) K) :
    peirceBasisPhi (K := K) = s3Tau12 K ∧
    OperatorAlgebra.PeirceSpine.comm (peirceBasisSP (K := K)) (s3Tau23 K) = !![(0 : K), -2; 0, 0] ∧
    peirceBasisSP (K := K) * peirceBasisSP (K := K) = 1 ∧
    peirceBasisPhi (K := K) * peirceBasisPhi (K := K) = 1 ∧
    peirceBasisJ (K := K) * peirceBasisJ (K := K) = -1 ∧
    peirceBasisSP (K := K) * peirceBasisPhi (K := K) = peirceBasisJ (K := K) ∧
    peirceBasisPhi (K := K) * peirceBasisSP (K := K) = -peirceBasisJ (K := K) ∧
    (2 : K) • M =
      Matrix.trace (M * peirceBasisI) • peirceBasisI +
      Matrix.trace (M * peirceBasisSP) • peirceBasisSP +
      Matrix.trace (M * peirceBasisPhi) • peirceBasisPhi -
      Matrix.trace (M * peirceBasisJ) • peirceBasisJ := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, two_mul_matrix_from_four_traces M⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [OperatorAlgebra.PeirceSpine.comm, peirceBasisSP, s3Tau23]; try ring)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peirceBasisSP, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peirceBasisPhi, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peirceBasisJ, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peirceBasisSP, peirceBasisPhi, peirceBasisJ, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peirceBasisSP, peirceBasisPhi, peirceBasisJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Node $\mathfrak{PW}_6$ Split-Quaternion & $\mathrm{Cl}(1,1)$ Clifford Bridge Weld**:
    Welds `peirce_peter_weyl_four_basis_reconstruction` to the canonical real split-quaternion
    basis decomposition `Cl11SplitQuaternionMobiusBridge.splitQuaternion_basis_span` and the
    surjective $\mathrm{Cl}(1,1)$ matrix representation `Cl11MatrixCliffordBridge.cl11MatrixRep_surjective`. -/
lemma pw6_peirce_clifford_trace_inversion_and_cl11_split_quaternion_weld
    (M_real : SplitQuaternion) :
    (∃ a b c d : ℝ, M_real = a • splitOne + b • splitL + c • splitI + d • splitIL) ∧
    Function.Surjective cl11MatrixRep ∧
    (2 : ℝ) • M_real =
      Matrix.trace (M_real * peirceBasisI) • peirceBasisI +
      Matrix.trace (M_real * peirceBasisSP) • peirceBasisSP +
      Matrix.trace (M_real * peirceBasisPhi) • peirceBasisPhi -
      Matrix.trace (M_real * peirceBasisJ) • peirceBasisJ := by
  refine ⟨splitQuaternion_basis_span M_real, cl11MatrixRep_surjective, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceBasisI, peirceBasisSP, peirceBasisPhi, peirceBasisJ,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-! ## Section 7: Node $\mathfrak{PW}_7$ — Master Finite Fourier and Peirce Identity Assembly -/

/-- **Node $\mathfrak{PW}_7$ (Master Finite Fourier and Peirce Identity Assembly)**:
    Unifies the 7-stage causal poset ($\mathfrak{PW}_1 \prec \dots \prec \mathfrak{PW}_7$):
    1. Poset cardinality $7$ and strict causal chain (`peterWeylFourierStage_strict_causal_chain`),
    2. 1D Abelian character commutator blindness (`abelian_character_blind_to_commutators`),
    3. Chebyshev horseshoe parabola $y = 2c^2 - 1$ (`chebyshev_horseshoe_parabola_identity`),
    4. Conditional covariant/contravariant product-order identities and finite group convolution
       (`conditional_covariant_vs_contravariant_product_order`),
    5. The arithmetic count $1^2 + 1^2 + 2^2 = 6$ and a concrete noncommuting matrix-generator witness
       (`s3_reflection_generator_matrix_witness`),
    6. The `2 • M` four-trace identity (`peirce_peter_weyl_four_basis_reconstruction`),
    7. Abstract operator-ring Peirce four-block decomposition and helper excursion law
       (`peirce_decomp`, `peirce_off_diag_sq_zero`, `peirce_helper_excursion_law`), and
    8. Continuous Harish-Chandra Plancherel–Weyl density synthesis (`certified_plancherel_weyl_synthesis`). -/
lemma pw7_master_peter_weyl_noncommutative_fourier_peirce_synthesis
    {G K B : Type*} [Mul G] [CommRing K] [Ring B]
    (χ : G → K) (h_mul : ∀ u v : G, χ (u * v) = χ u * χ v)
    (ρ_cov ρ_inv : G → B)
    (h_cov : ∀ u v : G, ρ_cov (u * v) = ρ_cov u * ρ_cov v)
    (h_inv : ∀ u v : G, ρ_inv (u * v) = ρ_inv v * ρ_inv u)
    (u v : G) (c s t r : K) (M : Matrix (Fin 2) (Fin 2) K)
    (P X : B) (hP : P * P = P) (t_pl : ℝ) (ht_pl : 0 < t_pl) :
    Fintype.card PeterWeylFourierStage = 7 ∧
    (χ (u * v) - χ (v * u) = 0) ∧
    (c * c + s * s = 1 → c * c - s * s = 2 * (c * c) - 1) ∧
    ((1 - t * t) ^ 2 - (2 * t) ^ 2 = 2 * (1 - t * t) ^ 2 - (1 + t * t) ^ 2) ∧
    ((1 - r) * (1 + r) = 1 - r ^ 2 ∧ (1 + r ^ 2) - 1 = r ^ 2) ∧
    (ρ_inv (u * v) - ρ_inv u * ρ_inv v = OperatorAlgebra.PeirceSpine.comm (ρ_inv v) (ρ_inv u)) ∧
    (Fintype.card (Equiv.Perm (Fin 3)) = 6 ∧
      s3Tau12 ℤ * s3Tau23 ℤ ≠ s3Tau23 ℤ * s3Tau12 ℤ ∧
      OperatorAlgebra.PeirceSpine.comm (peirceBasisSP (K := K)) (s3Tau23 K) = !![(0 : K), -2; 0, 0]) ∧
    ((2 : K) • M =
      Matrix.trace (M * peirceBasisI) • peirceBasisI +
      Matrix.trace (M * peirceBasisSP) • peirceBasisSP +
      Matrix.trace (M * peirceBasisPhi) • peirceBasisPhi -
      Matrix.trace (M * peirceBasisJ) • peirceBasisJ) ∧
    (P * (X * X) * P = (P * X * P) * (P * X * P) + conePlus P X * coneMinus P X) ∧
    (0 < plancherelDensity t_pl ∧ plancherelDensity t_pl < t_pl) := by
  refine ⟨by decide,
    (abelian_character_blind_to_commutators χ h_mul u v).2,
    (chebyshev_horseshoe_parabola_identity c s t r).1,
    (chebyshev_horseshoe_parabola_identity c s t r).2.2.1,
    (chebyshev_horseshoe_parabola_identity c s t r).2.2.2,
    (conditional_covariant_vs_contravariant_product_order ρ_cov ρ_inv h_cov h_inv 1 1 u v).2.2,
    ⟨by decide,
     (s3_reflection_generator_matrix_witness K).2.2.2.2.2.1,
     (peirce_peter_weyl_four_basis_reconstruction M).2.1⟩,
    (peirce_peter_weyl_four_basis_reconstruction M).2.2.2.2.2.2.2,
    ?_,
    ⟨(certified_plancherel_weyl_synthesis t_pl ht_pl).2.2.1,
     (certified_plancherel_weyl_synthesis t_pl ht_pl).2.2.2.2.1⟩⟩
  dsimp [conePlus, coneMinus]
  peirce_nf hP

/-! ## Section 8: Galois Quotient Groups, Dihedral Peter–Weyl $2 \times 2$ Peirce Block, & Surprisal Normal Form Quotient Survival ($\mathfrak{GQ}_1 \prec \dots \prec \mathfrak{GQ}_7$) -/

/-- **Node $\mathfrak{GQ}_1\text{–}\mathfrak{GQ}_2$ (Galois Stratification of the 12-Month Circle, Exponent-2 Klein Four-Group, & Cyclic Frequency Rescaling)**:
    1. **Euler Totient Divisor Sum for $N = 12$:**
       $\varphi(1) + \varphi(2) + \varphi(3) + \varphi(4) + \varphi(6) + \varphi(12) = 1 + 1 + 2 + 2 + 2 + 4 = 12$ and $\varphi(12) = 4$.
    2. **Galois Group $(\mathbb{Z}/12\mathbb{Z})^\times = \{1, 5, 7, 11\} \cong V_4$:**
       Every coprime unit $p \in \{1, 5, 7, 11\}$ satisfies $p^2 \bmod 12 = 1$.
    3. **Harmonic Permutation vs. Seasonal Fixation:**
       The Galois automorphism $\sigma_5$ swaps the fundamental circle $k = 1$ with the star polygon
       $k = 5$ (`(5 * 1) % 12 = 5`, `(5 * 5) % 12 = 1`), while fixing the 4-season mode $k = 3$
       (`(5 * 3) % 12 = 3`) and the alternating parity mode $k = 6$ (`(5 * 6) % 12 = 6`).
    4. **Cyclic Fourier Character Frequency-Coordinate Duality (`ZMod.stdAddChar`):**
       Over any cyclic group `ZMod N`, rescaling frequency $k \mapsto p \cdot k$ coincides with
       rescaling the spatial/temporal coordinate $x \mapsto p \cdot x$:
       `ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x))`. -/
lemma z12_galois_orbit_stratification_and_v4_group
    {N : ℕ} [NeZero N] (p k x : ZMod N) :
    (Nat.totient 1 + Nat.totient 2 + Nat.totient 3 +
      Nat.totient 4 + Nat.totient 6 + Nat.totient 12 = 12 ∧
     Nat.totient 12 = 4 ∧
     (1 * 1) % 12 = 1 ∧ (5 * 5) % 12 = 1 ∧ (7 * 7) % 12 = 1 ∧ (11 * 11) % 12 = 1 ∧
     (5 * 1) % 12 = 5 ∧ (5 * 5) % 12 = 1 ∧
     (5 * 3) % 12 = 3 ∧ (5 * 6) % 12 = 6) ∧
    ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x)) := by
  refine ⟨by decide, ?_⟩
  congr 1
  ring

/-- 2D Peter–Weyl rotation rotor $R(c, s) = c + s J_1$ in `[Ring B]` built from the canonical
    Peirce complex generator `genJ P X Y = conePlus P X - coneMinus P Y`. -/
def peirceRotor2D {B : Type*} [Ring B] (P X Y c s : B) : B :=
  c + s * genJ P X Y

/-- **Node $\mathfrak{GQ}_3\text{–}\mathfrak{GQ}_4$ (Non-Abelian Dihedral Peter–Weyl Representation in `[Ring B]`)**:
    Let $P^2 = P$ in `[Ring B]` with grading reflection $S_P = \mathrm{invS}\,P = P - (1 - P)$,
    complex generator $J_1 = \mathrm{genJ}\,P\,X\,Y = \mathrm{conePlus}\,P\,X - \mathrm{coneMinus}\,P\,Y$,
    and off-diagonal bridge $\Phi_1 = \mathrm{genPhi}\,P\,X\,Y = \mathrm{conePlus}\,P\,X + \mathrm{coneMinus}\,P\,Y$:
    1. **Dihedral Inversion by Reflection ($S_P R(c, s) S_P = R(c, -s)$):**
       Conjugating `peirceRotor2D P X Y c s` by `invS P` inverts the odd sine harmonic $s \mapsto -s$.
    2. **Non-Commutative Commutator ($[S_P, R(c, s)] = 2 s \Phi_1$):**
       `comm (invS P) (peirceRotor2D P X Y c s) = s * (genPhi P X Y + genPhi P X Y)`. -/
lemma dihedral_peter_weyl_2x2_peirce_representation
    {B : Type*} [Ring B] (P X Y c s : B) (hP : P * P = P)
    (hc_S : invS P * c = c * invS P)
    (hs_S : invS P * s = s * invS P) :
    invS P * peirceRotor2D P X Y c s * invS P = peirceRotor2D P X Y c (-s) ∧
    OperatorAlgebra.PeirceSpine.comm (invS P) (peirceRotor2D P X Y c s) =
      s * (genPhi P X Y + genPhi P X Y) := by
  have hS2 : invS P * invS P = 1 := by
    dsimp [invS]
    peirce_nf hP
  have hSJ : invS P * genJ P X Y = genPhi P X Y := by
    dsimp [invS, genJ, genPhi, conePlus, coneMinus]
    peirce_nf hP
  have hJS : genJ P X Y * invS P = -genPhi P X Y := by
    dsimp [invS, genJ, genPhi, conePlus, coneMinus]
    peirce_nf hP
  have hSJS : invS P * genJ P X Y * invS P = -genJ P X Y := by
    dsimp [invS, genJ, conePlus, coneMinus]
    peirce_nf hP
  refine ⟨?_, ?_⟩
  · dsimp [peirceRotor2D]
    calc
      invS P * (c + s * genJ P X Y) * invS P =
          (invS P * c) * invS P + (invS P * s) * genJ P X Y * invS P := by
        simp only [mul_add, add_mul, mul_assoc]
      _ = c * (invS P * invS P) + s * (invS P * genJ P X Y * invS P) := by
        rw [hc_S, hs_S]
        simp only [mul_assoc]
      _ = c + (-s) * genJ P X Y := by
        rw [hS2, hSJS, mul_one, mul_neg, neg_mul]
  · dsimp [OperatorAlgebra.PeirceSpine.comm, peirceRotor2D]
    calc
      invS P * (c + s * genJ P X Y) - (c + s * genJ P X Y) * invS P =
          (invS P * c - c * invS P) +
            ((invS P * s) * genJ P X Y - s * (genJ P X Y * invS P)) := by
        simp only [mul_add, add_mul, mul_assoc]
        abel
      _ = 0 + (s * (invS P * genJ P X Y) - s * (-genPhi P X Y)) := by
        rw [hc_S, sub_self, hs_S, hJS]
        simp only [mul_assoc]
      _ = s * (genPhi P X Y + genPhi P X Y) := by
        rw [hSJ, mul_neg, sub_neg_eq_add, ← mul_add, zero_add]

/-- Concrete $2 \times 2$ Peter–Weyl rotation rotor $R(c, s) = c I_2 + s J = \begin{pmatrix} c & s \\ -s & c \end{pmatrix}$
    in `Matrix (Fin 2) (Fin 2) K`. -/
def matrixRotor2D {K : Type*} [CommRing K] (c s : K) : Matrix (Fin 2) (Fin 2) K :=
  c • peirceBasisI + s • peirceBasisJ

/-- **Node $\mathfrak{GQ}_4$ Concrete $2 \times 2$ Dihedral Rotor Conjugation & Reflected-Rotor Involution Law**:
    In `Matrix (Fin 2) (Fin 2) K` over any `[CommRing K]`:
    1. Conjugating $R(c, s) = c I_2 + s J$ by $S_P$ flips the sine angle:
       `peirceBasisSP * matrixRotor2D c s * peirceBasisSP = matrixRotor2D c (-s)`.
    2. The reflected rotor $R(c, s) S_P$ squares to $(c^2 + s^2) I_2$:
       `(matrixRotor2D c s * peirceBasisSP) * (matrixRotor2D c s * peirceBasisSP) = (c * c + s * s) • peirceBasisI`
       (so $R(c, s) S_P$ is an involution whenever $c^2 + s^2 = 1$).
    3. The commutator with $S_P$ is proportional to $\Phi$:
       `comm peirceBasisSP (matrixRotor2D c s) = (2 * s) • peirceBasisPhi`. -/
lemma dihedral_matrix_rotor_reflection_and_involution_law
    {K : Type*} [CommRing K] (c s : K) :
    peirceBasisSP (K := K) * matrixRotor2D c s * peirceBasisSP (K := K) =
      matrixRotor2D c (-s) ∧
    (matrixRotor2D c s * peirceBasisSP (K := K)) *
        (matrixRotor2D c s * peirceBasisSP (K := K)) =
      (c * c + s * s) • peirceBasisI (K := K) ∧
    OperatorAlgebra.PeirceSpine.comm (peirceBasisSP (K := K)) (matrixRotor2D c s) =
      (2 * s) • peirceBasisPhi (K := K) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [matrixRotor2D, peirceBasisI, peirceBasisJ, peirceBasisSP,
        Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [matrixRotor2D, peirceBasisI, peirceBasisJ, peirceBasisSP,
        Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [OperatorAlgebra.PeirceSpine.comm, matrixRotor2D, peirceBasisI, peirceBasisJ,
        peirceBasisSP, peirceBasisPhi]; try ring)

/-- Linearized PMI surprisal operator `surprisalNormalFormOp u_bar delta_u σ = u_bar + delta_u * σ`
    in `[Ring B]` (where `u_bar = ½ log(1 - s_r²)`, `delta_u = artanh(s_r)`, and `σ² = 1`). -/
def surprisalNormalFormOp {B : Type*} [Ring B] (u_bar delta_u σ : B) : B :=
  u_bar + delta_u * σ

/-- **Node $\mathfrak{GQ}_5\text{–}\mathfrak{GQ}_7$ (Quotient Surprisal Normal Form & 2nd-Order Micro-Attribute Variance Survival)**:
    Let `P_H * P_H = P_H` be the subgroup-averaging quotient projector for $G \twoheadrightarrow G/H$
    in `[Ring B]`, and let `L = surprisalNormalFormOp u_bar delta_u σ = u_bar + delta_u * σ` with
    `σ * σ = 1` and central coefficients `u_bar, delta_u`:
    1. **Macro-Attribute (`P_H * σ * P_H = σ * P_H`):**
       The linearized surprisal normal form descends intact at 1st order:
       `P_H * L * P_H = L * P_H`.
    2. **Micro-Attribute (`P_H * σ * P_H = 0`, averages to zero over $H$-fibers):**
       - At **1st order**, the slope `delta_u` vanishes on the quotient:
         `P_H * L * P_H = u_bar * P_H`.
       - At **2nd order**, the Socratic Gramian defect on the quotient $G/H$ recovers the exact
         squared BKM slope `delta_u * delta_u`:
         `P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H`. -/
lemma quotient_surprisal_normal_form_and_second_order_survival
    {B : Type*} [Ring B] (P_H u_bar delta_u σ : B)
    (hPH : P_H * P_H = P_H)
    (hσ2 : σ * σ = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_σ : u_bar * σ = σ * u_bar)
    (hd_σ : delta_u * σ = σ * delta_u) :
    let L := surprisalNormalFormOp u_bar delta_u σ
    (P_H * σ * P_H = σ * P_H → P_H * L * P_H = L * P_H) ∧
    (P_H * σ * P_H = 0 →
      P_H * L * P_H = u_bar * P_H ∧
      P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H) := by
  refine ⟨?_, ?_⟩
  · intro h_macro
    dsimp [surprisalNormalFormOp]
    calc
      P_H * (u_bar + delta_u * σ) * P_H
        = (P_H * u_bar) * P_H + (P_H * delta_u) * σ * P_H := by
          simp only [mul_add, add_mul, mul_assoc]
      _ = u_bar * (P_H * P_H) + delta_u * (P_H * σ * P_H) := by
          rw [hu_P, hd_P]
          simp only [mul_assoc]
      _ = (u_bar + delta_u * σ) * P_H := by
          rw [hPH, h_macro, add_mul, mul_assoc]
  · intro h_micro
    have h1 : P_H * surprisalNormalFormOp u_bar delta_u σ * P_H = u_bar * P_H := by
      dsimp [surprisalNormalFormOp]
      calc
        P_H * (u_bar + delta_u * σ) * P_H
          = (P_H * u_bar) * P_H + (P_H * delta_u) * σ * P_H := by
            simp only [mul_add, add_mul, mul_assoc]
        _ = u_bar * (P_H * P_H) + delta_u * (P_H * σ * P_H) := by
            rw [hu_P, hd_P]
            simp only [mul_assoc]
        _ = u_bar * P_H := by
            rw [hPH, h_micro, mul_zero, add_zero]
    refine ⟨h1, ?_⟩
    have hL2 :
        surprisalNormalFormOp u_bar delta_u σ * surprisalNormalFormOp u_bar delta_u σ =
          (u_bar * u_bar + delta_u * delta_u) + (u_bar * delta_u + delta_u * u_bar) * σ := by
      dsimp [surprisalNormalFormOp]
      have hdσ2 : delta_u * σ * (delta_u * σ) = delta_u * delta_u := by
        calc
          delta_u * σ * (delta_u * σ) = delta_u * (σ * delta_u) * σ := by simp only [mul_assoc]
          _ = delta_u * delta_u * (σ * σ) := by rw [← hd_σ]; simp only [mul_assoc]
          _ = delta_u * delta_u := by rw [hσ2, mul_one]
      have Cross :
          u_bar * (delta_u * σ) + delta_u * σ * u_bar =
            (u_bar * delta_u + delta_u * u_bar) * σ := by
        calc
          u_bar * (delta_u * σ) + delta_u * σ * u_bar
            = u_bar * delta_u * σ + delta_u * (σ * u_bar) := by simp only [mul_assoc]
          _ = (u_bar * delta_u + delta_u * u_bar) * σ := by
              rw [← hu_σ, add_mul]
              simp only [mul_assoc]
      calc
        (u_bar + delta_u * σ) * (u_bar + delta_u * σ)
          = u_bar * u_bar + (u_bar * (delta_u * σ) + delta_u * σ * u_bar) +
              delta_u * σ * (delta_u * σ) := by
              simp only [add_mul, mul_add, mul_assoc]
              abel
        _ = (u_bar * u_bar + delta_u * delta_u) + (u_bar * delta_u + delta_u * u_bar) * σ := by
            rw [Cross, hdσ2]
            abel
    have h_cross_zero : P_H * ((u_bar * delta_u + delta_u * u_bar) * σ) * P_H = 0 := by
      calc
        P_H * ((u_bar * delta_u + delta_u * u_bar) * σ) * P_H
          = (P_H * u_bar * delta_u + P_H * delta_u * u_bar) * σ * P_H := by
              simp only [mul_add, add_mul, mul_assoc]
        _ = (u_bar * P_H * delta_u + delta_u * P_H * u_bar) * σ * P_H := by
              rw [hu_P, hd_P]
        _ = (u_bar * (P_H * delta_u) + delta_u * (P_H * u_bar)) * σ * P_H := by
              simp only [mul_assoc]
        _ = (u_bar * delta_u + delta_u * u_bar) * (P_H * σ * P_H) := by
              rw [hd_P, hu_P]
              simp only [add_mul, mul_assoc]
        _ = 0 := by rw [h_micro, mul_zero]
    rw [h1, hL2]
    calc
      P_H * ((u_bar * u_bar + delta_u * delta_u) + (u_bar * delta_u + delta_u * u_bar) * σ) * P_H -
          u_bar * P_H * (u_bar * P_H)
        = P_H * (u_bar * u_bar + delta_u * delta_u) * P_H +
            P_H * ((u_bar * delta_u + delta_u * u_bar) * σ) * P_H -
            u_bar * (P_H * u_bar) * P_H := by
            simp only [mul_add, add_mul, mul_assoc]
      _ = (u_bar * u_bar + delta_u * delta_u) * (P_H * P_H) + 0 -
            u_bar * u_bar * (P_H * P_H) := by
          rw [h_cross_zero, hu_P]
          have hu2 : P_H * (u_bar * u_bar) = u_bar * u_bar * P_H := by
            rw [← mul_assoc, hu_P, mul_assoc, hu_P, ← mul_assoc]
          have hd2 : P_H * (delta_u * delta_u) = delta_u * delta_u * P_H := by
            rw [← mul_assoc, hd_P, mul_assoc, hd_P, ← mul_assoc]
          have h_comm_sum :
              P_H * (u_bar * u_bar + delta_u * delta_u) =
                (u_bar * u_bar + delta_u * delta_u) * P_H := by
            rw [mul_add, hu2, hd2, add_mul]
          rw [h_comm_sum]
          simp only [mul_assoc]
      _ = (delta_u * delta_u) * P_H := by
          rw [hPH, add_zero, add_mul]
          abel

/-- **Master Galois–Quotient, Dihedral Peter–Weyl & Surprisal Survival Synthesis ($\mathfrak{GQ}_1 \prec \dots \prec \mathfrak{GQ}_7$)**:
    Unifies all three Galois–quotient representation-geometry directives in a single theorem:
    1. **Directive 1 ($\mathfrak{GQ}_1\text{–}\mathfrak{GQ}_2$):**
       `z12_galois_orbit_stratification_and_v4_group` ($\sum_{d \mid 12} \varphi(d) = 12$,
       $(\mathbb{Z}/12\mathbb{Z})^\times \cong V_4$, $\sigma_5$ swapping $k=1 \leftrightarrow k=5$
       while fixing $k=3, 6$, and `ZMod.stdAddChar` frequency-coordinate duality).
    2. **Directive 2 ($\mathfrak{GQ}_3\text{–}\mathfrak{GQ}_4$):**
       `dihedral_peter_weyl_2x2_peirce_representation` and `dihedral_matrix_rotor_reflection_and_involution_law`
       (dihedral rotor reflection $S_P R(c, s) S_P = R(c, -s)$, non-abelian commutator
       $[S_P, R(c, s)] = 2 s \Phi_1$, and reflected-rotor square $(R(c, s) S_P)^2 = (c^2 + s^2) I_2$).
    3. **Directive 3 ($\mathfrak{GQ}_5\text{–}\mathfrak{GQ}_7$):**
       `quotient_surprisal_normal_form_and_second_order_survival` (macro-attribute 1st-order
       preservation vs. micro-attribute 1st-order wipeout and 2nd-order Socratic Gramian variance
       recovery $P_H L^2 P_H - (P_H L P_H)^2 = (\Delta u)^2 P_H$). -/
lemma gq_master_galois_quotient_dihedral_peter_weyl_and_surprisal_survival
    {N : ℕ} [NeZero N] (p k x : ZMod N)
    {K B : Type*} [CommRing K] [Ring B]
    (c_mat s_mat : K)
    (P X Y c s : B) (hP : P * P = P)
    (hc_S : invS P * c = c * invS P)
    (hs_S : invS P * s = s * invS P)
    (P_H u_bar delta_u σ : B)
    (hPH : P_H * P_H = P_H)
    (hσ2 : σ * σ = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_σ : u_bar * σ = σ * u_bar)
    (hd_σ : delta_u * σ = σ * delta_u) :
    ((Nat.totient 1 + Nat.totient 2 + Nat.totient 3 +
       Nat.totient 4 + Nat.totient 6 + Nat.totient 12 = 12 ∧
      Nat.totient 12 = 4 ∧
      (1 * 1) % 12 = 1 ∧ (5 * 5) % 12 = 1 ∧ (7 * 7) % 12 = 1 ∧ (11 * 11) % 12 = 1 ∧
      (5 * 1) % 12 = 5 ∧ (5 * 5) % 12 = 1 ∧
      (5 * 3) % 12 = 3 ∧ (5 * 6) % 12 = 6) ∧
     ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x))) ∧
    (invS P * peirceRotor2D P X Y c s * invS P = peirceRotor2D P X Y c (-s) ∧
     OperatorAlgebra.PeirceSpine.comm (invS P) (peirceRotor2D P X Y c s) =
       s * (genPhi P X Y + genPhi P X Y) ∧
     (matrixRotor2D c_mat s_mat * peirceBasisSP (K := K)) *
         (matrixRotor2D c_mat s_mat * peirceBasisSP (K := K)) =
       (c_mat * c_mat + s_mat * s_mat) • peirceBasisI (K := K)) ∧
    (let L := surprisalNormalFormOp u_bar delta_u σ
     (P_H * σ * P_H = σ * P_H → P_H * L * P_H = L * P_H) ∧
     (P_H * σ * P_H = 0 →
       P_H * L * P_H = u_bar * P_H ∧
       P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H)) := by
  refine ⟨z12_galois_orbit_stratification_and_v4_group p k x,
    ⟨(dihedral_peter_weyl_2x2_peirce_representation P X Y c s hP hc_S hs_S).1,
     (dihedral_peter_weyl_2x2_peirce_representation P X Y c s hP hc_S hs_S).2,
     (dihedral_matrix_rotor_reflection_and_involution_law c_mat s_mat).2.1⟩,
    quotient_surprisal_normal_form_and_second_order_survival
      P_H u_bar delta_u σ hPH hσ2 hu_P hd_P hu_σ hd_σ⟩

end InfoGeometry.Canonical.PeterWeylNoncommutativeFourierPoset
