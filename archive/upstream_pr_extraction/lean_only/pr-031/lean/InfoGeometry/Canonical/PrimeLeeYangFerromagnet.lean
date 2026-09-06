import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

/-!
# InfoGeometry.Canonical.PrimeLeeYangFerromagnet

Finite ferromagnetic prime-chain anchor.

This file owns the small, theorem-safe surface for the rank-one interaction
matrix

`Jᵢⱼ = (λ / 2) log(pᵢ) log(pⱼ)`

with the Ising diagonal deleted by convention.  It proves the finite
ferromagnetic condition from supplied positivity of the prime logarithms.

The richer centered-chain development lives in
`PrimeLeeYangFerromagneticChain`.  This file gives the compact interface used
by the Lee--Yang/RH bridge layer.  It does not assert Lee--Yang stability,
analytic convergence to completed `xi`, or RH.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeLeeYangFerromagnet

open PrimeLeeYangFerromagneticChain

/--
Finite prime-chain data.

The logarithm positivity is stored explicitly so this anchor remains
independent of scalar-complex coercion proof obligations.
-/
@[rep_depth thermo]
structure FinitePrimeChainData
    (N : ℕ) where
  p : Fin N → ℕ
  prime : ∀ i, Nat.Prime (p i)
  ell : Fin N → ℝ
  ell_eq_log : ∀ i, ell i = Real.log ((p i : ℝ))
  ell_pos : ∀ i, 0 < ell i

namespace FinitePrimeChainData

variable {N : ℕ}
variable (D : FinitePrimeChainData N)

/--
The corresponding existing centered-chain packet, with coupling scale `λ`.

This bridge keeps the compact anchor compatible with the fuller
`PrimeFerromagneticChain` API.
-/
@[rep_depth thermo]
def toPrimeFerromagneticChain
    (lam : ℝ)
    (hLam : 0 ≤ lam) :
    PrimeFerromagneticChain N where
  prime := D.p
  prime_isPrime := D.prime
  kappa := lam
  kappa_nonneg := hLam

/--
Centered logarithmic magnetization

`A(σ) = 1/2 ∑ᵢ log(pᵢ) σᵢ`.

The particle-hole map `σ ↦ -σ` sends this readout to its negative.
-/
@[rep_depth thermo]
def centeredMagnetization
    (σ : Fin N → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, D.ell i * σ i

/-- Rank-one spin coupling with the Ising diagonal deleted. -/
@[rep_depth thermo]
def spinCoupling
    (lam : ℝ)
    (i j : Fin N) : ℝ :=
  if i = j then 0 else (lam / 2) * D.ell i * D.ell j

/-- Off-diagonal coupling has the advertised rank-one formula. -/
@[rep_depth thermo]
theorem spinCoupling_eq_rankOne_of_ne
    (lam : ℝ)
    {i j : Fin N}
    (hij : i ≠ j) :
    D.spinCoupling lam i j = (lam / 2) * D.ell i * D.ell j := by
  unfold spinCoupling
  simp [hij]

/-- Diagonal entries are deleted by Ising convention. -/
@[rep_depth thermo]
theorem spinCoupling_self
    (lam : ℝ)
    (i : Fin N) :
    D.spinCoupling lam i i = 0 := by
  unfold spinCoupling
  simp

/-- Ferromagnetic nonnegativity of the finite prime-chain couplings. -/
@[rep_depth thermo]
theorem spinCoupling_nonneg
    {lam : ℝ}
    (hLam : 0 ≤ lam)
    (i j : Fin N) :
    0 ≤ D.spinCoupling lam i j := by
  unfold spinCoupling
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]
    have hLam2 : 0 ≤ lam / 2 := by
      exact div_nonneg hLam (by norm_num)
    exact mul_nonneg
      (mul_nonneg hLam2 (le_of_lt (D.ell_pos i)))
      (le_of_lt (D.ell_pos j))

/-- Strict ferromagnetic positivity off the diagonal. -/
@[rep_depth thermo]
theorem spinCoupling_pos_of_ne
    {lam : ℝ}
    (hLam : 0 < lam)
    {i j : Fin N}
    (hij : i ≠ j) :
    0 < D.spinCoupling lam i j := by
  unfold spinCoupling
  simp [hij]
  have hLam2 : 0 < lam / 2 := by
    exact div_pos hLam (by norm_num)
  exact mul_pos
    (mul_pos hLam2 (D.ell_pos i))
    (D.ell_pos j)

/-- Symmetry of the finite prime-chain coupling matrix. -/
@[rep_depth thermo]
theorem spinCoupling_symm
    (lam : ℝ)
    (i j : Fin N) :
    D.spinCoupling lam i j = D.spinCoupling lam j i := by
  unfold spinCoupling
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := by
      intro h
      exact hij h.symm
    simp [hij, hji]
    ring

/--
Full rank-one matrix before deleting the diagonal:
`J_full = (λ/2) ell ellᵀ`.
-/
@[rep_depth thermo]
def fullRankOneCoupling
    (lam : ℝ)
    (i j : Fin N) : ℝ :=
  (lam / 2) * D.ell i * D.ell j

/-- Cross-minor identity for the full rank-one coupling matrix. -/
@[rep_depth thermo]
theorem fullRankOneCoupling_cross_minor
    (lam : ℝ)
    (i j r t : Fin N) :
    D.fullRankOneCoupling lam i j * D.fullRankOneCoupling lam r t =
      D.fullRankOneCoupling lam i t * D.fullRankOneCoupling lam r j := by
  unfold fullRankOneCoupling
  ring

/--
Finite Lee--Yang Hamiltonian in spin variables:

`H(σ; w) = -(λ/4)(∑ᵢ ellᵢ σᵢ)^2 + (w/2)∑ᵢ ellᵢ σᵢ`.

The sign convention is chosen so that the pair interaction is ferromagnetic.
-/
@[rep_depth thermo]
def spinHamiltonian
    (lam w : ℝ)
    (σ : Fin N → ℝ) : ℝ :=
  - (lam / 4) * (∑ i, D.ell i * σ i) ^ 2
    + (w / 2) * ∑ i, D.ell i * σ i

/-- The owner target follows from the explicit finite matrix elements. -/
theorem primeLeeYangFerromagnetOwnerTarget :
    ∀ {N : ℕ} (D : FinitePrimeChainData N) {lam : ℝ},
      0 ≤ lam →
        ∀ i j : Fin N,
          0 ≤ D.spinCoupling lam i j ∧
            D.spinCoupling lam i j = D.spinCoupling lam j i ∧
              D.spinCoupling lam i i = 0 := by
  intro N D lam hLam i j
  exact ⟨D.spinCoupling_nonneg hLam i j, D.spinCoupling_symm lam i j,
    D.spinCoupling_self lam i⟩

end FinitePrimeChainData

end InfoGeometry.Canonical.PrimeLeeYangFerromagnet
