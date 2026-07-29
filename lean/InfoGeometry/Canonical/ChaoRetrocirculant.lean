import Mathlib.Tactic

/-!
# Chao retrocirculant spectral sockets

Formalization scaffold for Chong-Yun Chao, "On a Type of Circulants",
Linear Algebra Appl. 6, 241--248 (1973).

The paper studies matrices `Pσ C`, where `C` is circulant and `Pσ` is a
permutation matrix.  This file keeps the Fourier diagonalization theorem as an
explicit finite certificate and proves the elementary block identities behind
Chao's eigenvalue readout.
-/

namespace InfoGeometry.Canonical.ChaoRetrocirculant

noncomputable section

universe u

/-- A finite permutation of `Fin n`, written as an equivalence. -/
abbrev FinPerm (n : ℕ) := Equiv.Perm (Fin n)

/-- A permutation is involutive. -/
def IsInvolution {n : ℕ} (σ : FinPerm n) : Prop :=
  ∀ i : Fin n, σ (σ i) = i

/-- Fixed index of an involutive permutation. -/
def IsFixed {n : ℕ} (σ : FinPerm n) (i : Fin n) : Prop :=
  σ i = i

/-- Two-cycle pair of an involutive permutation. -/
def IsTwoCycle {n : ℕ} (σ : FinPerm n) (i j : Fin n) : Prop :=
  i ≠ j ∧ σ i = j ∧ σ j = i

/--
An additive permutation of the cyclic index monoid `Fin n`.

This is the concrete algebraic content of the additive-automorphism
hypothesis in Chao's permutation theorem.  The additive equivalence is a
Mathlib owner of both the homomorphism law and bijectivity; the final equality
identifies its underlying permutation with `σ`.
-/
def IsAdditivePermutation {n : ℕ} (σ : FinPerm n) : Prop :=
  ∃ e : AddEquiv (Fin n) (Fin n), ∀ i : Fin n, e i = σ i

/-- Matrix of a finite permutation acting on coordinate vectors. -/
def permutationMatrix {n : ℕ} (σ : FinPerm n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if σ j = i then 1 else 0

/-- Entrywise Fourier-side retrocirculant normal form `Pσ D`. -/
def retroEntry {n : ℕ} (σ : FinPerm n) (μ : Fin n → ℂ) (r c : Fin n) : ℂ :=
  if σ c = r then μ c else 0

/-- The fixed-index diagonal entry of `Pσ D` is `μ i`. -/
theorem retroEntry_fixed
    {n : ℕ} (σ : FinPerm n) (μ : Fin n → ℂ) {i : Fin n}
    (hi : IsFixed σ i) :
    retroEntry σ μ i i = μ i := by
  unfold retroEntry
  rw [hi]
  simp

/-- On a two-cycle, the `i,j` off-diagonal entry is `μ j`. -/
theorem retroEntry_twoCycle_ij
    {n : ℕ} (σ : FinPerm n) (μ : Fin n → ℂ) {i j : Fin n}
    (hij : IsTwoCycle σ i j) :
    retroEntry σ μ i j = μ j := by
  rcases hij with ⟨hne, hij, hji⟩
  simp [retroEntry, hji]

/-- On a two-cycle, the `j,i` off-diagonal entry is `μ i`. -/
theorem retroEntry_twoCycle_ji
    {n : ℕ} (σ : FinPerm n) (μ : Fin n → ℂ) {i j : Fin n}
    (hij : IsTwoCycle σ i j) :
    retroEntry σ μ j i = μ i := by
  rcases hij with ⟨hne, hij, hji⟩
  simp [retroEntry, hij]

/-- The `i,i` entry vanishes on a nontrivial two-cycle. -/
theorem retroEntry_twoCycle_ii_zero
    {n : ℕ} (σ : FinPerm n) (μ : Fin n → ℂ) {i j : Fin n}
    (hij : IsTwoCycle σ i j) :
    retroEntry σ μ i i = 0 := by
  rcases hij with ⟨hne, hij, hji⟩
  unfold retroEntry
  rw [hij]
  simp [hne.symm]

/-- The `j,j` entry vanishes on a nontrivial two-cycle. -/
theorem retroEntry_twoCycle_jj_zero
    {n : ℕ} (σ : FinPerm n) (μ : Fin n → ℂ) {i j : Fin n}
    (hij : IsTwoCycle σ i j) :
    retroEntry σ μ j j = 0 := by
  rcases hij with ⟨hne, hij, hji⟩
  unfold retroEntry
  rw [hji]
  simp [hne]

/-- Characteristic polynomial of the two-cycle `2 × 2` block. -/
def twoCycleCharacteristic (a b lam : ℂ) : ℂ :=
  lam ^ 2 - a * b

/-- Determinant identity for the Chao two-cycle block `[[ -λ, b ], [ a, -λ ]]`. -/
theorem twoCycle_det_identity (a b lam : ℂ) :
    (-lam) * (-lam) - b * a = twoCycleCharacteristic a b lam := by
  simp [twoCycleCharacteristic]
  ring

/-- If `λ² = a b`, then `λ` is a two-cycle spectral root. -/
theorem twoCycle_root_of_sq_eq_mul {a b lam : ℂ} (h : lam ^ 2 = a * b) :
    twoCycleCharacteristic a b lam = 0 := by
  simp [twoCycleCharacteristic, h]

/-- Fourier commutation certificate from Chao Theorem 1. -/
structure FourierPermutationCommutationCertificate (n : ℕ) where
  σ : FinPerm n
  isAdditiveAutomorphism : IsAdditivePermutation σ
  orderTwo : IsInvolution σ
  fourierMatrix : Matrix (Fin n) (Fin n) ℂ
  commutesWithFourier :
    permutationMatrix σ * fourierMatrix = fourierMatrix * permutationMatrix σ
  theorem1_forward :
    (permutationMatrix σ * fourierMatrix = fourierMatrix * permutationMatrix σ) →
      IsAdditivePermutation σ ∧ IsInvolution σ
  theorem1_backward :
    IsAdditivePermutation σ ∧ IsInvolution σ →
      permutationMatrix σ * fourierMatrix = fourierMatrix * permutationMatrix σ

namespace FourierPermutationCommutationCertificate

variable {n : ℕ} (C : FourierPermutationCommutationCertificate n)

/-- Chao Theorem 1 forward readout. -/
theorem automorphism_and_orderTwo_of_commutes
    (h : permutationMatrix C.σ * C.fourierMatrix =
      C.fourierMatrix * permutationMatrix C.σ) :
    IsAdditivePermutation C.σ ∧ IsInvolution C.σ :=
  C.theorem1_forward h

/-- Chao Theorem 1 backward readout. -/
theorem commutes_of_automorphism_and_orderTwo
    (h : IsAdditivePermutation C.σ ∧ IsInvolution C.σ) :
    permutationMatrix C.σ * C.fourierMatrix =
      C.fourierMatrix * permutationMatrix C.σ :=
  C.theorem1_backward h

end FourierPermutationCommutationCertificate

/-- Chao spectral certificate for `Pσ C`/`C Pσ` after Fourier diagonalization. -/
structure ChaoRetrocirculantSpectralCertificate (n : ℕ) where
  σ : FinPerm n
  μ : Fin n → ℂ
  orderTwo : IsInvolution σ
  isEigenvalue : ℂ → Prop
  fixed_eigenvalue : ∀ k : Fin n, IsFixed σ k → isEigenvalue (μ k)
  twoCycle_eigenvalue : ∀ i j : Fin n, IsTwoCycle σ i j →
    ∀ lam : ℂ, lam ^ 2 = μ i * μ j → isEigenvalue lam
  /-- The permutation/circulant products have the same characteristic polynomial. -/
  cp_same_spectrum :
    Matrix.charpoly (permutationMatrix σ * Matrix.diagonal μ) =
      Matrix.charpoly (Matrix.diagonal μ * permutationMatrix σ)

namespace ChaoRetrocirculantSpectralCertificate

variable {n : ℕ} (S : ChaoRetrocirculantSpectralCertificate n)

theorem cp_same_spectrum_holds :
    Matrix.charpoly (permutationMatrix S.σ * Matrix.diagonal S.μ) =
      Matrix.charpoly (Matrix.diagonal S.μ * permutationMatrix S.σ) := by
  exact Matrix.charpoly_mul_comm _ _

/-- Fixed points contribute eigenvalue `μ k`. -/
theorem fixed_readout {k : Fin n} (hk : IsFixed S.σ k) :
    S.isEigenvalue (S.μ k) :=
  S.fixed_eigenvalue k hk

/-- Two-cycles contribute every supplied square root of `μ i μ j`. -/
theorem twoCycle_root_readout {i j : Fin n} (hij : IsTwoCycle S.σ i j)
    {lam : ℂ} (hlam : lam ^ 2 = S.μ i * S.μ j) :
    S.isEigenvalue lam :=
  S.twoCycle_eigenvalue i j hij lam hlam

end ChaoRetrocirculantSpectralCertificate

end

end InfoGeometry.Canonical.ChaoRetrocirculant
