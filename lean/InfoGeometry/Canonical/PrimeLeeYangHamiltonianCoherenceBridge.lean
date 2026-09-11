import InfoGeometry.Canonical.PrimeLeeYangFerromagnet
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Prime-chain realization and Ising Hamiltonian coherence

This owner supplies the two finite coherence facts needed before a Lee--Yang
polynomial owner: prime inputs canonically produce positive logarithmic
weights, and the collective quadratic Hamiltonian is separated from its
deleted-diagonal self-energy.  The latter is constant only under an explicit
Ising-spin hypothesis.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeLeeYangHamiltonianCoherenceBridge

open PrimeLeeYangFerromagnet

def diagonalSelfEnergy {N : ℕ} (D : FinitePrimeChainData N)
    (lam : ℝ) (σ : Fin N → ℝ) : ℝ :=
  - (lam / 4) * ∑ i, (D.ell i * σ i) ^ 2

def offDiagonalCollectiveEnergy {N : ℕ} (D : FinitePrimeChainData N)
    (lam : ℝ) (σ : Fin N → ℝ) : ℝ :=
  - (lam / 4) * (∑ i, D.ell i * σ i) ^ 2 - diagonalSelfEnergy D lam σ

theorem spinHamiltonian_eq_offDiagonal_add_self_and_field
    {N : ℕ} (D : FinitePrimeChainData N) (lam w : ℝ)
    (σ : Fin N → ℝ) :
    D.spinHamiltonian lam w σ =
      offDiagonalCollectiveEnergy D lam σ + diagonalSelfEnergy D lam σ +
        (w / 2) * ∑ i, D.ell i * σ i := by
  unfold PrimeLeeYangFerromagnet.FinitePrimeChainData.spinHamiltonian
    offDiagonalCollectiveEnergy
  ring

theorem diagonalSelfEnergy_eq_constant_of_ising
    {N : ℕ} (D : FinitePrimeChainData N) (lam : ℝ)
    {σ : Fin N → ℝ} (hσ : IsIsingSpin σ) :
    diagonalSelfEnergy D lam σ =
      - (lam / 4) * ∑ i, (D.ell i) ^ 2 := by
  unfold diagonalSelfEnergy
  congr 2
  funext i
  rw [mul_pow, hσ i, mul_one]

theorem spinHamiltonian_eq_offDiagonal_add_constant_of_ising
    {N : ℕ} (D : FinitePrimeChainData N) (lam w : ℝ)
    {σ : Fin N → ℝ} (hσ : IsIsingSpin σ) :
    D.spinHamiltonian lam w σ =
      offDiagonalCollectiveEnergy D lam σ - (lam / 4) * ∑ i, (D.ell i) ^ 2 +
        (w / 2) * ∑ i, D.ell i * σ i := by
  rw [spinHamiltonian_eq_offDiagonal_add_self_and_field,
    diagonalSelfEnergy_eq_constant_of_ising D lam hσ]
  ring

theorem centeredMagnetization_neg
    {N : ℕ} (D : FinitePrimeChainData N) (σ : Fin N → ℝ) :
    D.centeredMagnetization (fun i => -σ i) =
      -D.centeredMagnetization σ := by
  unfold FinitePrimeChainData.centeredMagnetization
  simp only [mul_neg, Finset.sum_neg_distrib]

end InfoGeometry.Canonical.PrimeLeeYangHamiltonianCoherenceBridge
