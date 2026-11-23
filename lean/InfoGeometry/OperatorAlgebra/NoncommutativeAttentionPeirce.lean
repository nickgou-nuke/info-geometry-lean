/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-!
# Peirce decomposition of noncommutative operator affinities

The coefficient ring is arbitrary and may be noncommutative.  The results are
about the full operator algebra `Matrix (Fin 2) (Fin 2) A`; they do not assert
analytic attention, positivity, or a Hilbert-space interpretation.
-/

namespace InfoGeometry.OperatorAlgebra.NoncommutativeAttentionPeirce

open Matrix

variable {A : Type*} [Ring A]

abbrev Op₂ (A : Type*) := Matrix (Fin 2) (Fin 2) A

def pPlus : Op₂ A := !![1, 0; 0, 0]
def pMinus : Op₂ A := !![0, 0; 0, 1]

def channelPlusMinus (X : Op₂ A) : Op₂ A := pPlus * X * pMinus
def channelMinusPlus (X : Op₂ A) : Op₂ A := pMinus * X * pPlus
def evenPart (X : Op₂ A) : Op₂ A := !![X 0 0, 0; 0, X 1 1]
def oddPart (X : Op₂ A) : Op₂ A := !![0, X 0 1; X 1 0, 0]

theorem evenPart_eq_sandwich (X : Op₂ A) :
    evenPart X = pPlus * X * pPlus + pMinus * X * pMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [evenPart, pPlus, pMinus, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem oddPart_eq_sandwich (X : Op₂ A) :
    oddPart X = pPlus * X * pMinus + pMinus * X * pPlus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [oddPart, pPlus, pMinus, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

/-- The four operator corners reconstruct every matrix. -/
theorem peirce_four_channel_decomposition (X : Op₂ A) :
    pPlus * X * pPlus + pMinus * X * pMinus +
      pPlus * X * pMinus + pMinus * X * pPlus = X := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pPlus, pMinus, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
      Fin.sum_univ_succ]

/-- The diagonal and off-diagonal Peirce projections are complementary. -/
theorem even_odd_decomposition (X : Op₂ A) : evenPart X + oddPart X = X := by
  rw [Matrix.eta_fin_two X]
  ext i j; fin_cases i <;> fin_cases j <;> simp [evenPart, oddPart]

/-- The even Peirce component is an idempotent projection. -/
theorem evenPart_idempotent (X : Op₂ A) :
    evenPart (evenPart X) = evenPart X := by
  rw [Matrix.eta_fin_two X]
  ext i j; fin_cases i <;> fin_cases j <;> simp [evenPart]

/-- The odd Peirce component is an idempotent projection. -/
theorem oddPart_idempotent (X : Op₂ A) :
    oddPart (oddPart X) = oddPart X := by
  rw [Matrix.eta_fin_two X]
  ext i j; fin_cases i <;> fin_cases j <;> simp [oddPart]

/-- The even and odd Peirce projections have disjoint images in either order. -/
theorem evenPart_oddPart_zero (X : Op₂ A) :
    evenPart (oddPart X) = 0 := by
  rw [Matrix.eta_fin_two X]
  ext i j; fin_cases i <;> fin_cases j <;> simp [evenPart, oddPart]

theorem oddPart_evenPart_zero (X : Op₂ A) :
    oddPart (evenPart X) = 0 := by
  rw [Matrix.eta_fin_two X]
  ext i j; fin_cases i <;> fin_cases j <;> simp [evenPart, oddPart]

/-- Products of even operators remain even. -/
theorem even_mul_even (X Y : Op₂ A) :
    evenPart (evenPart X * evenPart Y) = evenPart X * evenPart Y := by
  rw [Matrix.eta_fin_two X, Matrix.eta_fin_two Y]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [evenPart]

/-- Products of even and odd operators remain odd, with order preserved. -/
theorem even_mul_odd (X Y : Op₂ A) :
    evenPart X * oddPart Y = oddPart (evenPart X * oddPart Y) := by
  rw [Matrix.eta_fin_two X, Matrix.eta_fin_two Y]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [evenPart, oddPart]

/-- Products of odd and even operators remain odd, with order preserved. -/
theorem odd_mul_even (X Y : Op₂ A) :
    oddPart X * evenPart Y = oddPart (oddPart X * evenPart Y) := by
  rw [Matrix.eta_fin_two X, Matrix.eta_fin_two Y]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [evenPart, oddPart]

/-- Products of two odd operators lie in the even sector. -/
theorem odd_mul_odd (X Y : Op₂ A) :
    oddPart X * oddPart Y = evenPart (oddPart X * oddPart Y) := by
  rw [Matrix.eta_fin_two X, Matrix.eta_fin_two Y]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [evenPart, oddPart]

/-- The even output of a product is the even-even plus odd-odd contribution. -/
theorem evenPart_product (X Y : Op₂ A) :
    evenPart (X * Y) = evenPart X * evenPart Y + oddPart X * oddPart Y := by
  rw [Matrix.eta_fin_two X, Matrix.eta_fin_two Y]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [evenPart, oddPart]; abel

/-- The odd output of a product is the even-odd plus odd-even contribution. -/
theorem oddPart_product (X Y : Op₂ A) :
    oddPart (X * Y) = evenPart X * oddPart Y + oddPart X * evenPart Y := by
  rw [Matrix.eta_fin_two X, Matrix.eta_fin_two Y]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [evenPart, oddPart]; abel

/-- Each single cross-channel operator is square-zero. -/
theorem cross_channel_square_zero (X : Op₂ A) :
    channelPlusMinus X * channelPlusMinus X = 0 ∧
      channelMinusPlus X * channelMinusPlus X = 0 := by
  constructor <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [channelPlusMinus, channelMinusPlus, pPlus, pMinus,
        Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ])

/-- Two alternating cross-channel steps return to the corresponding diagonal corner. -/
theorem alternating_cross_channel_returns_to_corner (X Y : Op₂ A) :
    channelPlusMinus X * channelMinusPlus Y = pPlus * X * pMinus * Y * pPlus ∧
      channelMinusPlus X * channelPlusMinus Y = pMinus * X * pPlus * Y * pMinus := by
  constructor <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [channelPlusMinus, channelMinusPlus, pPlus, pMinus,
        Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ])

/-- Removing the upper-right channel gives a lower-triangular operator. -/
def causalPart (X : Op₂ A) : Op₂ A := !![X 0 0, 0; X 1 0, X 1 1]

lemma mul_apply_01 (X Y : Op₂ A) :
    (X * Y) 0 1 = X 0 0 * Y 0 1 + X 0 1 * Y 1 1 := by
  rw [Matrix.eta_fin_two X, Matrix.eta_fin_two Y, Matrix.mul_fin_two]
  rfl

/-- The causal matrices form a genuine subring of the noncommutative operator
ring: the defining vanishing condition is the upper-right operator channel. -/
def causalSubring : Subring (Op₂ A) where
  carrier := {X | X 0 1 = 0}
  zero_mem' := rfl
  one_mem' := rfl
  add_mem' := by
    intro X Y hX hY
    change X 0 1 + Y 0 1 = 0
    rw [hX, hY, add_zero]
  neg_mem' := by
    intro X hX
    change -X 0 1 = 0
    rw [hX, neg_zero]
  mul_mem' := by
    intro X Y hX hY
    change (X * Y) 0 1 = 0
    rw [mul_apply_01, hX, hY]
    simp

/-- Causal masking lands in the triangular subring. -/
theorem causalPart_mem (X : Op₂ A) : causalPart X ∈ causalSubring := by
  change (causalPart X) 0 1 = 0
  rfl

/-- Causal masking fixes exactly the lower-triangular operators. -/
theorem causalPart_eq_self_iff (X : Op₂ A) :
    causalPart X = X ↔ X ∈ causalSubring := by
  constructor
  · intro h
    rw [← h]
    exact causalPart_mem X
  · intro h
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · change X 0 1 = 0 at h
      simp [causalPart, h]
    · rfl
    · rfl

/-- The causal projection is idempotent. -/
theorem causalPart_idempotent (X : Op₂ A) : causalPart (causalPart X) = causalPart X := by
  apply (causalPart_eq_self_iff (causalPart X)).2
  exact causalPart_mem X

/-- The lower-triangular operators form a multiplicatively closed subalgebra. -/
theorem causalPart_mul_closed (X Y : Op₂ A) :
    causalPart (causalPart X * causalPart Y) = causalPart X * causalPart Y := by
  rw [Matrix.eta_fin_two (causalPart X), Matrix.eta_fin_two (causalPart Y)]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [causalPart]

def affinity [StarRing A] (Q K : Op₂ A) : Op₂ A := Q * Kᴴ

def symmetricAffinity [StarRing A] (Q K : Op₂ A) : Op₂ A :=
  affinity Q K + affinity K Q

def skewAffinity [StarRing A] (Q K : Op₂ A) : Op₂ A :=
  affinity Q K - affinity K Q

def omega : Op₂ A := !![0, -1; 1, 0]

/-- The positive Peirce projection and the symplectic matrix do not commute.
This is a concrete noncommutativity witness in `M₂(A)` for every nontrivial
coefficient ring; it does not assert that every matrix pair fails to commute. -/
theorem pPlus_omega_noncommute [Nontrivial A] :
    (pPlus : Op₂ A) * omega ≠ omega * pPlus := by
  intro h
  have h01 : ((pPlus : Op₂ A) * (omega : Op₂ A)) 0 1 =
      ((omega : Op₂ A) * (pPlus : Op₂ A)) 0 1 :=
    congrArg (fun M : Op₂ A => M 0 1) h
  have hl : ((pPlus : Op₂ A) * (omega : Op₂ A)) 0 1 = (-(1 : A)) := by
    simp [pPlus, omega, Matrix.mul_apply, Fin.sum_univ_two]
  have hr : ((omega : Op₂ A) * (pPlus : Op₂ A)) 0 1 = (0 : A) := by
    simp [pPlus, omega, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hl, hr] at h01
  have hone : (1 : A) = 0 := by
    calc
      (1 : A) = -(-(1 : A)) := by simp
      _ = -(0 : A) := congrArg Neg.neg h01
      _ = 0 := by simp
  exact one_ne_zero hone

def symplecticAffinity [StarRing A] (Q K : Op₂ A) : Op₂ A := Q * omega * Kᴴ

/-- The adjoint of the noncommutative affinity swaps its two arguments. -/
theorem affinity_adjoint [StarRing A] (Q K : Op₂ A) :
    (affinity Q K)ᴴ = affinity K Q := by
  change (Q * Kᴴ)ᴴ = K * Qᴴ
  rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-- The Hermitian and skew-Hermitian affinity sectors reconstruct twice the affinity. -/
theorem affinity_polar_decomposition [StarRing A] (Q K : Op₂ A) :
    (affinity Q K + affinity K Q) + (affinity Q K - affinity K Q) =
      affinity Q K + affinity Q K := by
  noncomm_ring

/-- Peirce even affinity splits into matching-parity query/key terms. -/
theorem affinity_even_factorization [StarRing A] (Q K : Op₂ A) :
    evenPart (affinity Q K) =
      affinity (evenPart Q) (evenPart K) + affinity (oddPart Q) (oddPart K) := by
  rw [Matrix.eta_fin_two Q, Matrix.eta_fin_two K]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [affinity, evenPart, oddPart, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]; abel

/-- Peirce odd affinity splits into the two mixed-parity query/key terms. -/
theorem affinity_odd_factorization [StarRing A] (Q K : Op₂ A) :
    oddPart (affinity Q K) =
      affinity (evenPart Q) (oddPart K) + affinity (oddPart Q) (evenPart K) := by
  rw [Matrix.eta_fin_two Q, Matrix.eta_fin_two K]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [affinity, evenPart, oddPart, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]; abel

theorem omega_skew_adjoint [StarRing A] : (omega : Op₂ A)ᴴ = -omega := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [omega]

theorem symplecticAffinity_adjoint [StarRing A] (Q K : Op₂ A) :
    (symplecticAffinity Q K)ᴴ = -symplecticAffinity K Q := by
  dsimp [symplecticAffinity]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    omega_skew_adjoint]
  noncomm_ring

def mellinSqueeze [StarRing A] (u : Aˣ) : Op₂ A :=
  !![(u : A), 0; 0, star (↑u⁻¹ : A)]

def mellinDualSqueeze [StarRing A] (u : Aˣ) : Op₂ A :=
  !![star (↑u⁻¹ : A), 0; 0, (u : A)]

theorem mellinSqueeze_preserves_omega [StarRing A] (u : Aˣ) :
    (mellinSqueeze u)ᴴ * omega * mellinSqueeze u = omega := by
  have h₁ : star (u : A) * star (↑u⁻¹ : A) = 1 := by
    rw [← star_mul, Units.inv_mul, star_one]
  have h₂ : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [mellinSqueeze, omega, Matrix.mul_apply,
      Fin.sum_univ_succ, h₁, h₂]

theorem mellinSqueeze_dual_biorthogonal [StarRing A] (u : Aˣ) :
    mellinSqueeze u * (mellinDualSqueeze u)ᴴ = 1 := by
  have h₁ : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  have h₂ : star (↑u⁻¹ : A) * star (u : A) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [mellinSqueeze, mellinDualSqueeze, Matrix.mul_apply,
      Fin.sum_univ_succ, h₁, h₂]

theorem symplecticAffinity_squeeze_invariant [StarRing A]
    (Q K : Op₂ A) (u : Aˣ) :
    symplecticAffinity (Q * (mellinSqueeze u)ᴴ) (K * (mellinSqueeze u)ᴴ) =
      symplecticAffinity Q K := by
  simp only [symplecticAffinity, conjTranspose_mul, conjTranspose_conjTranspose]
  calc
    Q * (mellinSqueeze u)ᴴ * omega * (mellinSqueeze u * Kᴴ) =
        Q * ((mellinSqueeze u)ᴴ * omega * mellinSqueeze u) * Kᴴ := by noncomm_ring
    _ = Q * omega * Kᴴ := by rw [mellinSqueeze_preserves_omega]

theorem affinity_biorthogonal_squeeze_invariant [StarRing A]
    (Q K : Op₂ A) (u : Aˣ) :
    affinity (Q * mellinSqueeze u) (K * mellinDualSqueeze u) = affinity Q K := by
  simp only [affinity, conjTranspose_mul]
  calc
    Q * mellinSqueeze u * ((mellinDualSqueeze u)ᴴ * Kᴴ) =
        Q * (mellinSqueeze u * (mellinDualSqueeze u)ᴴ) * Kᴴ := by noncomm_ring
    _ = Q * Kᴴ := by rw [mellinSqueeze_dual_biorthogonal]; simp

theorem causalPart_eq_peirce (X : Op₂ A) :
    causalPart X = evenPart X + channelMinusPlus X := by
  rw [evenPart_eq_sandwich]
  unfold channelMinusPlus
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [causalPart, pPlus, pMinus, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

/-! ### Four-mode operator transform

The coefficient maps below take values in the diagonal copy of `A` inside
`M₂(A)`.  This makes their commutation with the fixed Clifford basis an
actual matrix identity, without assuming that coefficients in `A` commute
with one another.
-/

def fiberEmbed (a : A) : Op₂ A := !![a, 0; 0, a]
def gamma : Op₂ A := !![1, 0; 0, -1]
def sigma : Op₂ A := !![0, 1; 1, 0]

def modeI (M : Op₂ A) : Op₂ A := fiberEmbed (M 0 0 + M 1 1)
def modeGamma (M : Op₂ A) : Op₂ A := fiberEmbed (M 0 0 - M 1 1)
def modeSigma (M : Op₂ A) : Op₂ A := fiberEmbed (M 0 1 + M 1 0)
def modeOmega (M : Op₂ A) : Op₂ A := fiberEmbed (M 1 0 - M 0 1)

/-- The scalar and grading mode maps commute with conjugate transpose. -/
theorem modeI_adjoint [StarRing A] (M : Op₂ A) :
    (modeI M)ᴴ = modeI Mᴴ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [modeI, fiberEmbed, Matrix.conjTranspose_apply]

theorem modeGamma_adjoint [StarRing A] (M : Op₂ A) :
    (modeGamma M)ᴴ = modeGamma Mᴴ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [modeGamma, fiberEmbed, Matrix.conjTranspose_apply]

/-- The symmetric off-diagonal mode commutes with conjugate transpose. -/
theorem modeSigma_adjoint [StarRing A] (M : Op₂ A) :
    (modeSigma M)ᴴ = modeSigma Mᴴ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [modeSigma, fiberEmbed, Matrix.conjTranspose_apply] <;> abel

/-- The oriented off-diagonal mode changes sign under conjugate transpose. -/
theorem modeOmega_adjoint [StarRing A] (M : Op₂ A) :
    (modeOmega M)ᴴ = -modeOmega Mᴴ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [modeOmega, fiberEmbed, Matrix.conjTranspose_apply]

theorem fiberEmbed_commutes_gamma (a : A) : fiberEmbed a * gamma = gamma * fiberEmbed a := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [fiberEmbed, gamma]

theorem fiberEmbed_commutes_sigma (a : A) : fiberEmbed a * sigma = sigma * fiberEmbed a := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [fiberEmbed, sigma]

theorem fiberEmbed_commutes_omega (a : A) : fiberEmbed a * omega = omega * fiberEmbed a := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [fiberEmbed, omega]

theorem four_mode_reconstruction (M : Op₂ A) :
    modeI M * 1 + modeGamma M * gamma + modeSigma M * sigma + modeOmega M * omega = M + M := by
  rw [Matrix.eta_fin_two M]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [modeI, modeGamma, modeSigma, modeOmega, fiberEmbed,
      gamma, sigma, omega] <;> abel

def convI (W V : Op₂ A) : Op₂ A :=
  modeI W * modeI V + modeGamma W * modeGamma V +
    modeSigma W * modeSigma V - modeOmega W * modeOmega V

def convGamma (W V : Op₂ A) : Op₂ A :=
  modeI W * modeGamma V + modeGamma W * modeI V +
    modeSigma W * modeOmega V - modeOmega W * modeSigma V

def convSigma (W V : Op₂ A) : Op₂ A :=
  modeI W * modeSigma V + modeSigma W * modeI V -
    modeGamma W * modeOmega V + modeOmega W * modeGamma V

def convOmega (W V : Op₂ A) : Op₂ A :=
  modeI W * modeOmega V + modeOmega W * modeI V -
    modeGamma W * modeSigma V + modeSigma W * modeGamma V

theorem four_mode_attention_convolution (W V : Op₂ A) :
    convI W V * 1 + convGamma W V * gamma + convSigma W V * sigma +
      convOmega W V * omega = (W + W) * (V + V) := by
  rw [Matrix.eta_fin_two W, Matrix.eta_fin_two V]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [convI, convGamma, convSigma, convOmega, modeI, modeGamma,
      modeSigma, modeOmega, fiberEmbed, gamma, sigma, omega] <;> noncomm_ring

end InfoGeometry.OperatorAlgebra.NoncommutativeAttentionPeirce
