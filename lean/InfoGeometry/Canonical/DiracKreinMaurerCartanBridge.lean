import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

import InfoGeometry.Clifford.CrawfordDiracBispinorDensities

/-!
# Dirac Conjugation as Krein Fundamental Symmetry and Maurer-Cartan Symmetric Space Decomposition

This module formalizes the exact bridge identifying Dirac spinor conjugation with the Krein
fundamental symmetry and establishing the symmetric space Maurer-Cartan structure of the
Dirac Clifford bundle:

1. **The Krein Metric of Relativistic Spacetime**:
   - The Dirac adjoint $\bar{\psi} \phi = \psi^\dagger \gamma^0 \phi$ is not an ad-hoc fix
     for covariance; it is *identically* the inner product $\langle \psi, \phi \rangle_\eta$
     on a Krein space $\mathcal{K} = \mathbb{C}^{(2,2)}$ with fundamental symmetry $\eta = \gamma^0$.
   - $\gamma^0$ satisfies $\eta^2 = 1$ and $\eta^\dagger = \eta$ (`kreinEta_sq`, `gamma0_hermitian`).
   - The spatial Dirac gamma matrices are Hilbert-anti-Hermitian: $(\gamma^k)^\dagger = -\gamma^k$
     (`gamma1_anti_hermitian`, `gamma2_anti_hermitian`, `gamma3_anti_hermitian`).

2. **The Fundamental Theorem of Relativistic Observables**:
   - Under the Krein adjoint $A^\sharp = \eta A^\dagger \eta = \gamma^0 A^\dagger \gamma^0$,
     ALL FOUR Dirac gamma matrices $\gamma^\mu$ are self-adjoint in the Krein metric:
     $(\gamma^\mu)^\sharp = \gamma^\mu$ (`dirac_gamma_all_krein_self_adjoint`).

3. **Lorentz Group as the Krein-Unitary Group $\mathrm{U}(\mathcal{K})$**:
   - The defining Lorentz condition $\gamma^0 \Lambda^\dagger \gamma^0 = \Lambda^{-1}$ is
     mathematically identical to Krein unitarity: $\Lambda^\sharp \Lambda = 1$
     (`lorentz_is_krein_unitary`).

4. **Cartan Involution and Symmetric Space Decomposition**:
   - The Krein fundamental symmetry induces the Cartan involution $\theta(X) = \gamma^0 X \gamma^0$
     satisfying $\theta^2 = \mathrm{id}$ and preserving Lie commutators (`cartanInvolution_involutive`,
     `cartanInvolution_bracket`).
   - The Lie algebra decomposes into even (gauge/spin connection) $\mathfrak{k}$ and
     odd (soldered tetrad/matter) $\mathfrak{p}$ eigenspaces:
     $[\mathfrak{k}, \mathfrak{k}] \subseteq \mathfrak{k}$,
     $[\mathfrak{k}, \mathfrak{p}] \subseteq \mathfrak{p}$,
     $[\mathfrak{p}, \mathfrak{p}] \subseteq \mathfrak{k}$
     (`symmetric_space_bracket_kk`, `symmetric_space_bracket_kp`, `symmetric_space_bracket_pp`).

5. **Maurer-Cartan Structural Equations**:
   - The canonical projections $\mathfrak{k}(X) = \frac{1}{2}(X + \theta(X))$ and
     $\mathfrak{p}(X) = \frac{1}{2}(X - \theta(X))$ yield complete decomposition $X = \mathfrak{k}(X) + \mathfrak{p}(X)$
     (`cartan_decomposition_sum`).
   - The commutator of matter fields generates zero torsion in $\mathfrak{p}$
     (`maurer_cartan_matter_matter_torsion_free`) and generates pure gauge curvature in $\mathfrak{k}$
     (`maurer_cartan_matter_matter_curvature_full`).
-/

namespace InfoGeometry.Canonical.DiracKreinMaurerCartan

open InfoGeometry.Clifford.CrawfordDiracBispinorDensities
open scoped Matrix

noncomputable section

/-!
### 1. The Krein Fundamental Symmetry η = γ⁰ and Dirac Conjugation
-/

/-- The Krein fundamental symmetry on 4D Dirac spinor space is identically γ⁰. -/
def kreinEta : DiracMatrix := gamma0

/-- γ⁰ is an involution: (γ⁰)² = 1. -/
theorem kreinEta_sq : kreinEta * kreinEta = 1 :=
  gamma0_mul_self

/-- γ⁰ is Hermitian (self-adjoint in the Hilbert sense). -/
theorem gamma0_hermitian : gamma0ᴴ = gamma0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma0, Matrix.conjTranspose]

/-- Spatial γ¹ is anti-Hermitian in the Hilbert sense: (γ¹)† = -γ¹. -/
theorem gamma1_anti_hermitian : gamma1ᴴ = -gamma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma1, Matrix.conjTranspose]

/-- Spatial γ² is anti-Hermitian in the Hilbert sense: (γ²)† = -γ². -/
theorem gamma2_anti_hermitian : gamma2ᴴ = -gamma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma2, Matrix.conjTranspose]

/-- Spatial γ³ is anti-Hermitian in the Hilbert sense: (γ³)† = -γ³. -/
theorem gamma3_anti_hermitian : gamma3ᴴ = -gamma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma3, Matrix.conjTranspose]

/-- The Krein adjoint of an operator A acting on Dirac spinors:
    A♯ = η A† η = γ⁰ A† γ⁰. -/
def kreinAdjoint (A : DiracMatrix) : DiracMatrix :=
  gamma0 * Aᴴ * gamma0

/-- Krein Adjoint Involution: (A♯)♯ = A. -/
theorem kreinAdjoint_involutive (A : DiracMatrix) :
    kreinAdjoint (kreinAdjoint A) = A := by
  dsimp [kreinAdjoint]
  simp only [Matrix.conjTranspose_mul, gamma0_hermitian, Matrix.conjTranspose_conjTranspose]
  change gamma0 * (gamma0 * (A * gamma0)) * gamma0 = A
  rw [← Matrix.mul_assoc gamma0 gamma0 (A * gamma0), gamma0_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc A gamma0 gamma0, gamma0_mul_self, Matrix.mul_one]

/-- Krein-Hermiticity of γ⁰: (γ⁰)♯ = γ⁰. -/
theorem gamma0_krein_self_adjoint : kreinAdjoint gamma0 = gamma0 := by
  dsimp [kreinAdjoint]
  rw [gamma0_hermitian]
  calc gamma0 * gamma0 * gamma0
    _ = 1 * gamma0 := by rw [gamma0_mul_self]
    _ = gamma0 := Matrix.one_mul gamma0

/-- Krein-Hermiticity of γ¹: (γ¹)♯ = γ¹. -/
theorem gamma1_krein_self_adjoint : kreinAdjoint gamma1 = gamma1 := by
  dsimp [kreinAdjoint]
  rw [gamma1_anti_hermitian]
  have h_anticomm : gamma0 * gamma1 = - (gamma1 * gamma0) :=
    eq_neg_of_add_eq_zero_left gamma0_gamma1_anticomm
  calc gamma0 * (-gamma1) * gamma0
    _ = - (gamma0 * gamma1 * gamma0) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul]
    _ = - (- (gamma1 * gamma0) * gamma0) := by rw [h_anticomm]
    _ = gamma1 := by
      simp only [Matrix.neg_mul, neg_neg, Matrix.mul_assoc, gamma0_mul_self, Matrix.mul_one]

/-- Krein-Hermiticity of γ²: (γ²)♯ = γ². -/
theorem gamma2_krein_self_adjoint : kreinAdjoint gamma2 = gamma2 := by
  dsimp [kreinAdjoint]
  rw [gamma2_anti_hermitian]
  have h_anticomm : gamma0 * gamma2 = - (gamma2 * gamma0) :=
    eq_neg_of_add_eq_zero_left gamma0_gamma2_anticomm
  calc gamma0 * (-gamma2) * gamma0
    _ = - (gamma0 * gamma2 * gamma0) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul]
    _ = - (- (gamma2 * gamma0) * gamma0) := by rw [h_anticomm]
    _ = gamma2 := by
      simp only [Matrix.neg_mul, neg_neg, Matrix.mul_assoc, gamma0_mul_self, Matrix.mul_one]

/-- Krein-Hermiticity of γ³: (γ³)♯ = γ³. -/
theorem gamma3_krein_self_adjoint : kreinAdjoint gamma3 = gamma3 := by
  dsimp [kreinAdjoint]
  rw [gamma3_anti_hermitian]
  have h_anticomm : gamma0 * gamma3 = - (gamma3 * gamma0) :=
    eq_neg_of_add_eq_zero_left gamma0_gamma3_anticomm
  calc gamma0 * (-gamma3) * gamma0
    _ = - (gamma0 * gamma3 * gamma0) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul]
    _ = - (- (gamma3 * gamma0) * gamma0) := by rw [h_anticomm]
    _ = gamma3 := by
      simp only [Matrix.neg_mul, neg_neg, Matrix.mul_assoc, gamma0_mul_self, Matrix.mul_one]

/-- The Fundamental Theorem of Relativistic Observables:
    Every Dirac gamma matrix γ^μ is self-adjoint in the Krein metric η = γ⁰! -/
theorem dirac_gamma_all_krein_self_adjoint (mu : Fin 4) :
    kreinAdjoint (gamma mu) = gamma mu := by
  fin_cases mu
  · exact gamma0_krein_self_adjoint
  · exact gamma1_krein_self_adjoint
  · exact gamma2_krein_self_adjoint
  · exact gamma3_krein_self_adjoint

/-!
### 2. Lorentz Group as the Krein-Unitary Group U(K)
-/

/-- An operator Λ is Krein-unitary if Λ♯ Λ = 1. -/
def isKreinUnitary (Lambda : DiracMatrix) : Prop :=
  kreinAdjoint Lambda * Lambda = 1

/-- Lorentz condition in standard physics: γ⁰ Λ† γ⁰ = Λ⁻¹.
    This is mathematically IDENTICAL to Krein unitarity: Λ♯ Λ = 1! -/
theorem lorentz_is_krein_unitary (Lambda Lambda_inv : DiracMatrix)
    (h_left_inv : Lambda_inv * Lambda = 1) (h_lorentz : gamma0 * Lambdaᴴ * gamma0 = Lambda_inv) :
    isKreinUnitary Lambda := by
  dsimp [isKreinUnitary, kreinAdjoint]
  rw [h_lorentz, h_left_inv]

/-!
### 3. The Cartan Involution and Maurer-Cartan Symmetric Space Decomposition
-/

/-- The Cartan involution induced by the Krein fundamental symmetry: θ(X) = γ⁰ X γ⁰. -/
def cartanInvolution (X : DiracMatrix) : DiracMatrix :=
  gamma0 * X * gamma0

/-- The Cartan involution is an automorphism of squaring: θ(θ(X)) = X. -/
theorem cartanInvolution_involutive (X : DiracMatrix) :
    cartanInvolution (cartanInvolution X) = X := by
  dsimp [cartanInvolution]
  rw [Matrix.mul_assoc gamma0 X gamma0]
  rw [← Matrix.mul_assoc gamma0 gamma0 (X * gamma0), gamma0_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc X gamma0 gamma0, gamma0_mul_self, Matrix.mul_one]

/-- Commutator bracket on Dirac matrices: [X, Y] = X Y - Y X. -/
def diracBracket (X Y : DiracMatrix) : DiracMatrix :=
  X * Y - Y * X

/-- The Cartan involution preserves matrix commutators: θ([X, Y]) = [θ(X), θ(Y)]. -/
theorem cartanInvolution_bracket (X Y : DiracMatrix) :
    cartanInvolution (diracBracket X Y) = diracBracket (cartanInvolution X) (cartanInvolution Y) := by
  dsimp [cartanInvolution, diracBracket]
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  have h (A B : DiracMatrix) : (gamma0 * A * gamma0) * (gamma0 * B * gamma0) = gamma0 * (A * B) * gamma0 := by
    calc (gamma0 * A * gamma0) * (gamma0 * B * gamma0)
      _ = gamma0 * A * (gamma0 * (gamma0 * (B * gamma0))) := by
        simp only [Matrix.mul_assoc]
      _ = gamma0 * A * ((gamma0 * gamma0) * (B * gamma0)) := by
        rw [← Matrix.mul_assoc gamma0 gamma0 (B * gamma0)]
      _ = gamma0 * A * (1 * (B * gamma0)) := by rw [gamma0_mul_self]
      _ = gamma0 * A * (B * gamma0) := by rw [Matrix.one_mul]
      _ = gamma0 * (A * B) * gamma0 := by simp only [Matrix.mul_assoc]
  rw [h X Y, h Y X]

/-- Even subspace condition (Gauge / Spin connection sector): θ(K) = +K. -/
def isKreinEven (K : DiracMatrix) : Prop :=
  cartanInvolution K = K

/-- Odd subspace condition (Soldered tetrad / matter sector): θ(P) = -P. -/
def isKreinOdd (P : DiracMatrix) : Prop :=
  cartanInvolution P = -P

/-- Symmetric space grading: [k, k] ⊆ k. -/
theorem symmetric_space_bracket_kk (K1 K2 : DiracMatrix)
    (h1 : isKreinEven K1) (h2 : isKreinEven K2) :
    isKreinEven (diracBracket K1 K2) := by
  dsimp [isKreinEven] at *
  rw [cartanInvolution_bracket, h1, h2]

/-- Symmetric space grading: [k, p] ⊆ p. -/
theorem symmetric_space_bracket_kp (K P : DiracMatrix)
    (hK : isKreinEven K) (hP : isKreinOdd P) :
    isKreinOdd (diracBracket K P) := by
  dsimp [isKreinEven, isKreinOdd] at *
  rw [cartanInvolution_bracket, hK, hP]
  dsimp [diracBracket]
  simp only [Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
  abel

/-- Symmetric space grading: [p, p] ⊆ k.
    The commutator of two soldered matter fields generates gauge curvature! -/
theorem symmetric_space_bracket_pp (P1 P2 : DiracMatrix)
    (h1 : isKreinOdd P1) (h2 : isKreinOdd P2) :
    isKreinEven (diracBracket P1 P2) := by
  dsimp [isKreinEven, isKreinOdd] at *
  rw [cartanInvolution_bracket, h1, h2]
  dsimp [diracBracket]
  simp only [neg_mul_neg]

/-!
### 4. Exact Projectors and Maurer-Cartan Curvature Splitting
-/

/-- Projection onto the even (compact/gauge) Lie subalgebra k: k(X) = 1/2 * (X + θ(X)). -/
def cartanEvenProj (X : DiracMatrix) : DiracMatrix :=
  (1 / 2 : ℂ) • (X + cartanInvolution X)

/-- Projection onto the odd (non-compact/matter) subspace p: p(X) = 1/2 * (X - θ(X)). -/
def cartanOddProj (X : DiracMatrix) : DiracMatrix :=
  (1 / 2 : ℂ) • (X - cartanInvolution X)

/-- The even projector produces an even element: θ(k(X)) = k(X). -/
theorem cartanEvenProj_is_even (X : DiracMatrix) :
    isKreinEven (cartanEvenProj X) := by
  dsimp [isKreinEven, cartanEvenProj, cartanInvolution]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  have h_inv : gamma0 * (gamma0 * X * gamma0) * gamma0 = X := by
    rw [Matrix.mul_assoc gamma0 X gamma0]
    rw [← Matrix.mul_assoc gamma0 gamma0 (X * gamma0), gamma0_mul_self, Matrix.one_mul]
    rw [Matrix.mul_assoc X gamma0 gamma0, gamma0_mul_self, Matrix.mul_one]
  rw [h_inv]
  rw [add_comm]

/-- The odd projector produces an odd element: θ(p(X)) = -p(X). -/
theorem cartanOddProj_is_odd (X : DiracMatrix) :
    isKreinOdd (cartanOddProj X) := by
  dsimp [isKreinOdd, cartanOddProj, cartanInvolution]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
  have h_inv : gamma0 * (gamma0 * X * gamma0) * gamma0 = X := by
    rw [Matrix.mul_assoc gamma0 X gamma0]
    rw [← Matrix.mul_assoc gamma0 gamma0 (X * gamma0), gamma0_mul_self, Matrix.one_mul]
    rw [Matrix.mul_assoc X gamma0 gamma0, gamma0_mul_self, Matrix.mul_one]
  rw [h_inv]
  simp only [← smul_neg]
  congr 1
  abel

/-- Completeness of the Cartan decomposition: X = k(X) + p(X). -/
theorem cartan_decomposition_sum (X : DiracMatrix) :
    cartanEvenProj X + cartanOddProj X = X := by
  dsimp [cartanEvenProj, cartanOddProj]
  rw [← smul_add]
  have h : (X + cartanInvolution X) + (X - cartanInvolution X) = (2 : ℂ) • X := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [h]
  rw [smul_smul]
  have h_half : (1 / 2 : ℂ) * 2 = 1 := by ring
  rw [h_half, one_smul]

/-- Maurer-Cartan Torsion-Free Condition:
    The matter-matter commutator [P1, P2] has ZERO projection in the matter subspace p! -/
theorem maurer_cartan_matter_matter_torsion_free (P1 P2 : DiracMatrix)
    (h1 : isKreinOdd P1) (h2 : isKreinOdd P2) :
    cartanOddProj (diracBracket P1 P2) = 0 := by
  have h_even : isKreinEven (diracBracket P1 P2) :=
    symmetric_space_bracket_pp P1 P2 h1 h2
  dsimp [cartanOddProj]
  dsimp [isKreinEven] at h_even
  rw [h_even]
  simp only [sub_self, smul_zero]

/-- Maurer-Cartan Curvature Generation:
    The matter-matter commutator [P1, P2] projects ENTIRELY into the gauge curvature algebra k! -/
theorem maurer_cartan_matter_matter_curvature_full (P1 P2 : DiracMatrix)
    (h1 : isKreinOdd P1) (h2 : isKreinOdd P2) :
    cartanEvenProj (diracBracket P1 P2) = diracBracket P1 P2 := by
  have h_even : isKreinEven (diracBracket P1 P2) :=
    symmetric_space_bracket_pp P1 P2 h1 h2
  dsimp [cartanEvenProj]
  dsimp [isKreinEven] at h_even
  rw [h_even]
  have h_two : diracBracket P1 P2 + diracBracket P1 P2 = (2 : ℂ) • diracBracket P1 P2 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [h_two, smul_smul]
  have h_half : (1 / 2 : ℂ) * 2 = 1 := by ring
  rw [h_half, one_smul]

/-!
### 5. Master Synthesis Packet
-/

/-- Master synthesis packet binding the Krein metric, all-gamma self-adjointness,
    Lorentz Krein unitarity, Cartan involution, and Maurer-Cartan symmetric space structure. -/
structure DiracKreinMaurerCartanPacket where
  eta_sq : kreinEta * kreinEta = 1
  gamma_all_krein_self_adjoint : ∀ mu : Fin 4, kreinAdjoint (gamma mu) = gamma mu
  adjoint_involutive : ∀ A : DiracMatrix, kreinAdjoint (kreinAdjoint A) = A
  lorentz_unitary : ∀ (Lambda Lambda_inv : DiracMatrix),
    Lambda_inv * Lambda = 1 → gamma0 * Lambdaᴴ * gamma0 = Lambda_inv → isKreinUnitary Lambda
  cartan_involutive : ∀ X : DiracMatrix, cartanInvolution (cartanInvolution X) = X
  bracket_kk : ∀ (K1 K2 : DiracMatrix), isKreinEven K1 → isKreinEven K2 → isKreinEven (diracBracket K1 K2)
  bracket_kp : ∀ (K P : DiracMatrix), isKreinEven K → isKreinOdd P → isKreinOdd (diracBracket K P)
  bracket_pp : ∀ (P1 P2 : DiracMatrix), isKreinOdd P1 → isKreinOdd P2 → isKreinEven (diracBracket P1 P2)
  cartan_sum : ∀ X : DiracMatrix, cartanEvenProj X + cartanOddProj X = X
  torsion_free : ∀ (P1 P2 : DiracMatrix), isKreinOdd P1 → isKreinOdd P2 →
    cartanOddProj (diracBracket P1 P2) = 0
  curvature_full : ∀ (P1 P2 : DiracMatrix), isKreinOdd P1 → isKreinOdd P2 →
    cartanEvenProj (diracBracket P1 P2) = diracBracket P1 P2

/-- Canonical instantiation of the Dirac-Krein Maurer-Cartan packet. -/
def makeDiracKreinMaurerCartanPacket : DiracKreinMaurerCartanPacket where
  eta_sq := kreinEta_sq
  gamma_all_krein_self_adjoint := dirac_gamma_all_krein_self_adjoint
  adjoint_involutive := kreinAdjoint_involutive
  lorentz_unitary := lorentz_is_krein_unitary
  cartan_involutive := cartanInvolution_involutive
  bracket_kk := symmetric_space_bracket_kk
  bracket_kp := symmetric_space_bracket_kp
  bracket_pp := symmetric_space_bracket_pp
  cartan_sum := cartan_decomposition_sum
  torsion_free := maurer_cartan_matter_matter_torsion_free
  curvature_full := maurer_cartan_matter_matter_curvature_full

/-- Definitional kernel certification of the Dirac-Krein Maurer-Cartan packet. -/
theorem dirac_krein_maurer_cartan_certified :
    (makeDiracKreinMaurerCartanPacket).eta_sq = gamma0_mul_self := rfl

end

end InfoGeometry.Canonical.DiracKreinMaurerCartan
