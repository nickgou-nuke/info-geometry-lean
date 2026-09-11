import InfoGeometry.Canonical.PrimePartitionPolynomials
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PrimeLeeYangHamiltonianCoherenceBridge

/-!
# Boolean partition configurations as genuine Ising spins

The partition-polynomial owner uses `Bool` configurations, while the finite
Hamiltonian owner uses real spins.  This file supplies only their explicit
finite readback; it does not assert a Lee--Yang circle theorem.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeLeeYangBooleanIsingCoherenceBridge

open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimePartitionPolynomials

variable {N : ℕ}

/-- Real Ising spin obtained from a Boolean partition configuration. -/
def boolIsingSpin (σ : SpinConfig N) : Fin N → ℝ :=
  fun i => spinSign (σ i)

@[simp]
theorem boolIsingSpin_true (σ : SpinConfig N) (i : Fin N)
    (h : σ i = true) : boolIsingSpin σ i = 1 := by
  simp [boolIsingSpin, h]

@[simp]
theorem boolIsingSpin_false (σ : SpinConfig N) (i : Fin N)
    (h : σ i = false) : boolIsingSpin σ i = -1 := by
  simp [boolIsingSpin, h]

/-- Every Boolean configuration is an Ising spin configuration. -/
theorem boolIsingSpin_isIsingSpin (σ : SpinConfig N) :
    IsIsingSpin (boolIsingSpin σ) := by
  intro i
  cases h : σ i <;> simp [boolIsingSpin, h]

/-- The partition interaction is exactly the coupling quadratic readout. -/
theorem interactionEnergy_eq_coupling_readout
    (D : FinitePrimeChainData N) (lam : ℝ) (σ : SpinConfig N) :
    interactionEnergy D lam σ =
      ∑ i : Fin N, ∑ j : Fin N,
        D.spinCoupling lam i j * boolIsingSpin σ i * boolIsingSpin σ j := by
  rfl

/-- The Boolean interaction readout is the pair part of the Ising Hamiltonian,
up to the explicit diagonal self-energy and the external field. -/
theorem spinHamiltonian_boolIsingSpin_eq_interactionEnergy
    (D : FinitePrimeChainData N) (lam w : ℝ) (σ : SpinConfig N) :
    D.spinHamiltonian lam w (boolIsingSpin σ) =
      - (1 / 2 : ℝ) * interactionEnergy D lam σ
        + (w / 2) * ∑ i : Fin N, D.ell i * boolIsingSpin σ i
        - (lam / 4) * ∑ i : Fin N, (D.ell i) ^ 2 := by
  have h := FinitePrimeChainData.spinHamiltonian_ising_decomposition D lam w
    (boolIsingSpin σ)
    (boolIsingSpin_isIsingSpin σ)
  simpa [interactionEnergy, boolIsingSpin] using h

/-! The deleted-diagonal interaction and the centered quadratic readout have
different normalizations.  This identity records the exact finite correction
instead of identifying them by convention. -/

theorem interactionEnergy_eq_collective_square_sub_diagonal
    (D : FinitePrimeChainData N) (lam : ℝ) (σ : SpinConfig N) :
    interactionEnergy D lam σ =
      (lam / 2) * (∑ i : Fin N, D.ell i * boolIsingSpin σ i) ^ 2
        - (lam / 2) * ∑ i : Fin N, (D.ell i) ^ 2 := by
  have h := FinitePrimeChainData.spinHamiltonian_ising_decomposition D lam 0
    (boolIsingSpin σ)
    (boolIsingSpin_isIsingSpin σ)
  have hread :
      (∑ i : Fin N, ∑ j : Fin N,
        D.spinCoupling lam i j * boolIsingSpin σ i * boolIsingSpin σ j) =
        interactionEnergy D lam σ := by
    rfl
  rw [hread] at h
  dsimp [PrimeLeeYangFerromagnet.FinitePrimeChainData.spinHamiltonian] at h
  linarith

end InfoGeometry.Canonical.PrimeLeeYangBooleanIsingCoherenceBridge
