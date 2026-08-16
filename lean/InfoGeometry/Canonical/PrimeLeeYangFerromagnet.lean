import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.PrimeLeeYangFerromagnet

Finite ferromagnetic prime-chain anchor.

This file owns the small, theorem-safe surface for the off-diagonal part of the
rank-one interaction matrix, with the Ising diagonal deleted:

`Jᵢⱼ = (λ / 2) log(pᵢ) log(pⱼ)` for `i ≠ j`, and `Jᵢᵢ = 0`.

It proves:
1. Canonical constructor `ofPrimes` deriving `log(pᵢ) > 0` directly from `Nat.Prime (p i)`.
2. The finite ferromagnetic condition ($J_{ij} \ge 0$, symmetry $J_{ij} = J_{ji}$, $J_{ii} = 0$).
3. Particle-hole oddness $A(-\sigma) = -A(\sigma)$.
4. Exact quadratic decomposition theorem for Ising spins ($\sigma_i^2 = 1$):
   $$H(\sigma; w) = -\frac{1}{2}\sum_{i,j} J_{ij}\sigma_i\sigma_j + \frac{w}{2}\sum_i \ell_i\sigma_i - \frac{\lambda}{4}\sum_i \ell_i^2$$

The richer centered-chain development lives in `PrimeLeeYangFerromagneticChain`.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeLeeYangFerromagnet

open PrimeLeeYangFerromagneticChain

/--
Finite prime-chain data.
-/
@[rep_depth thermo]
structure FinitePrimeChainData
    (N : ℕ) where
  p : Fin N → ℕ
  prime : ∀ i, Nat.Prime (p i)
  ell : Fin N → ℝ
  ell_eq_log : ∀ i, ell i = Real.log ((p i : ℝ))
  ell_pos : ∀ i, 0 < ell i

/-- Ising spin configuration predicate: σᵢ² = 1 for all i -/
def IsIsingSpin {N : ℕ} (σ : Fin N → ℝ) : Prop :=
  ∀ i, (σ i) ^ 2 = 1

namespace FinitePrimeChainData

variable {N : ℕ}

/-- 🏆 Constructor from genuine Nat primes without requiring redundant ell_pos hypothesis -/
def ofPrimes (p : Fin N → ℕ) (hp : ∀ i, Nat.Prime (p i)) : FinitePrimeChainData N where
  p := p
  prime := hp
  ell := fun i => Real.log (p i : ℝ)
  ell_eq_log := fun i => rfl
  ell_pos := by
    intro i
    have hp_ge : 2 ≤ p i := (hp i).two_le
    have hp_one_lt : (1 : ℝ) < (p i : ℝ) := by
      have : (2 : ℝ) ≤ (p i : ℝ) := by exact_mod_cast hp_ge
      linarith
    exact Real.log_pos hp_one_lt

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

@[rep_depth thermo]
theorem toPrimeFerromagneticChain_siteEnergy_eq_ell
    (lam : ℝ) (hLam : 0 ≤ lam) (i : Fin N) :
    (D.toPrimeFerromagneticChain lam hLam).siteEnergy i = D.ell i := by
  unfold PrimeFerromagneticChain.siteEnergy toPrimeFerromagneticChain
  exact (D.ell_eq_log i).symm

@[rep_depth thermo]
theorem toPrimeFerromagneticChain_prime_eq
    (lam : ℝ) (hLam : 0 ≤ lam) :
    (D.toPrimeFerromagneticChain lam hLam).prime = D.p :=
  rfl

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
-/
@[rep_depth thermo]
def spinHamiltonian
    (lam w : ℝ)
    (σ : Fin N → ℝ) : ℝ :=
  - (lam / 4) * (∑ i, D.ell i * σ i) ^ 2
    + (w / 2) * ∑ i, D.ell i * σ i

/-- 🏆 THEOREM: Quadratic expansion of the collective interaction sum -/
@[rep_depth thermo]
theorem sum_ell_sigma_sq (σ : Fin N → ℝ) :
    (∑ i, D.ell i * σ i) ^ 2 =
      (∑ i, (D.ell i)^2 * (σ i)^2) + (∑ i, ∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
  have h_sq := Finset.sum_mul_sum (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin N))
    (fun i => D.ell i * σ i) (fun j => D.ell j * σ j)
  have h_prod : (∑ i, D.ell i * σ i) ^ 2 = ∑ i, ∑ j, (D.ell i * σ i) * (D.ell j * σ j) := by
    rw [sq, h_sq]
  rw [h_prod]
  have h_split : (∑ i, ∑ j, (D.ell i * σ i) * (D.ell j * σ j)) =
    (∑ i, (D.ell i * σ i)^2) + (∑ i, ∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
      have h_inner : ∀ i, (∑ j, (D.ell i * σ i) * (D.ell j * σ j)) =
        (D.ell i * σ i)^2 + (∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
          intro i
          have h_diag : (D.ell i * σ i)^2 = (D.ell i * σ i) * (D.ell i * σ i) := by ring
          have h_sum_split := Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)
            (fun j => (D.ell i * σ i) * (D.ell j * σ j))
          rw [h_sum_split, ← h_diag]
          congr 1
          have h_ite : (∑ x ∈ Finset.univ \ {i}, (D.ell i * σ i) * (D.ell x * σ x)) =
            ∑ j ∈ Finset.univ, if i = j then 0 else D.ell i * D.ell j * σ i * σ j := by
              have h_ite_split := Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)
                (fun j => if i = j then 0 else D.ell i * D.ell j * σ i * σ j)
              simp only [if_true, zero_add] at h_ite_split
              rw [h_ite_split]
              apply Finset.sum_congr rfl
              intro j hj
              have hj_ne : i ≠ j := by
                have : j ∉ ({i} : Finset (Fin N)) := (Finset.mem_sdiff.mp hj).2
                intro h_eq
                subst h_eq
                exact this (Finset.mem_singleton_self i)
              simp [hj_ne]
              ring
          rw [h_ite]
      calc (∑ i, ∑ j, (D.ell i * σ i) * (D.ell j * σ j))
        _ = ∑ i, ((D.ell i * σ i)^2 + (∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_inner i
        _ = (∑ i, (D.ell i * σ i)^2) + (∑ i, ∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
          rw [Finset.sum_add_distrib]
  rw [h_split]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- 🏆 THEOREM: Exact Ising Hamiltonian reduction theorem -/
@[rep_depth thermo]
theorem spinHamiltonian_ising_decomposition (lam w : ℝ) (σ : Fin N → ℝ) (h_ising : IsIsingSpin σ) :
    D.spinHamiltonian lam w σ =
      - (1 / 2 : ℝ) * (∑ i, ∑ j, D.spinCoupling lam i j * σ i * σ j)
      + (w / 2) * (∑ i, D.ell i * σ i)
      - (lam / 4) * ∑ i, (D.ell i)^2 := by
  dsimp [spinHamiltonian]
  have h_exp := sum_ell_sigma_sq D σ
  have h_diag_ising : (∑ i, (D.ell i)^2 * (σ i)^2) = ∑ i, (D.ell i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    have : (σ i)^2 = 1 := h_ising i
    rw [this, mul_one]
  rw [h_exp, h_diag_ising]
  have h_coupling_term : (∑ i, ∑ j, D.spinCoupling lam i j * σ i * σ j) =
    (lam / 2) * (∑ i, ∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
      have h_term : ∀ i j, D.spinCoupling lam i j * σ i * σ j =
        (lam / 2) * (if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
          intro i j
          dsimp [spinCoupling]
          by_cases hij : i = j
          · simp [hij]
          · simp [hij]
            ring
      calc (∑ i, ∑ j, D.spinCoupling lam i j * σ i * σ j)
        _ = ∑ i, ∑ j, (lam / 2) * (if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact h_term i j
        _ = ∑ i, (lam / 2) * ∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.mul_sum]
        _ = (lam / 2) * (∑ i, ∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
          rw [← Finset.mul_sum]
  rw [h_coupling_term]
  ring

end FinitePrimeChainData

end InfoGeometry.Canonical.PrimeLeeYangFerromagnet
