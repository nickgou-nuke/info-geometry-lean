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

/-! An Ising configuration has squared spin equal to one at every site. -/
def IsIsingSpin {N : ℕ} (σ : Fin N → ℝ) : Prop :=
  ∀ i, σ i ^ 2 = 1

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

theorem sum_ell_sigma_sq (σ : Fin N → ℝ) :
    (∑ i, D.ell i * σ i) ^ 2 =
      (∑ i, (D.ell i)^2 * (σ i)^2) +
        (∑ i, ∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
  have h_sq := Finset.sum_mul_sum (Finset.univ : Finset (Fin N))
    (Finset.univ : Finset (Fin N)) (fun i => D.ell i * σ i)
    (fun j => D.ell j * σ j)
  have h_prod : (∑ i, D.ell i * σ i) ^ 2 =
      ∑ i, ∑ j, (D.ell i * σ i) * (D.ell j * σ j) := by
    rw [sq, h_sq]
  rw [h_prod]
  have h_split : (∑ i, ∑ j, (D.ell i * σ i) * (D.ell j * σ j)) =
      (∑ i, (D.ell i * σ i)^2) +
        (∑ i, ∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
    have h_inner : ∀ i, (∑ j, (D.ell i * σ i) * (D.ell j * σ j)) =
        (D.ell i * σ i)^2 +
          (∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
      intro i
      have h_sum_split := Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)
        (fun j => (D.ell i * σ i) * (D.ell j * σ j))
      rw [h_sum_split]
      have h_diag : (D.ell i * σ i)^2 =
          (D.ell i * σ i) * (D.ell i * σ i) := by ring
      rw [← h_diag]
      congr 1
      have h_ite : (∑ x ∈ Finset.univ \ {i},
          (D.ell i * σ i) * (D.ell x * σ x)) =
          ∑ j ∈ Finset.univ, if i = j then 0 else
            D.ell i * D.ell j * σ i * σ j := by
        have h_ite_split := Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)
          (fun j => if i = j then 0 else D.ell i * D.ell j * σ i * σ j)
        simp only [if_true, zero_add] at h_ite_split
        rw [h_ite_split]
        apply Finset.sum_congr rfl
        intro j hj
        have hj_ne : i ≠ j := by
          intro h_eq
          subst h_eq
          exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_singleton_self i)
        simp [hj_ne]
        ring
      rw [h_ite]
    calc
      (∑ i, ∑ j, (D.ell i * σ i) * (D.ell j * σ j)) =
          ∑ i, ((D.ell i * σ i)^2 +
            (∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact h_inner i
      _ = (∑ i, (D.ell i * σ i)^2) +
          (∑ i, ∑ j, if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
        rw [Finset.sum_add_distrib]
  rw [h_split]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem spinHamiltonian_ising_decomposition (lam w : ℝ) (σ : Fin N → ℝ)
    (h_ising : IsIsingSpin σ) :
    D.spinHamiltonian lam w σ =
      - (1 / 2 : ℝ) * (∑ i, ∑ j, D.spinCoupling lam i j * σ i * σ j)
        + (w / 2) * (∑ i, D.ell i * σ i)
        - (lam / 4) * ∑ i, (D.ell i)^2 := by
  dsimp [spinHamiltonian]
  have h_exp := D.sum_ell_sigma_sq σ
  have h_diag_ising : (∑ i, (D.ell i)^2 * (σ i)^2) =
      ∑ i, (D.ell i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [h_ising i, mul_one]
  rw [h_exp, h_diag_ising]
  have h_coupling_term : (∑ i, ∑ j, D.spinCoupling lam i j * σ i * σ j) =
      (lam / 2) * (∑ i, ∑ j,
        if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
    have h_term : ∀ i j, D.spinCoupling lam i j * σ i * σ j =
        (lam / 2) * (if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
      intro i j
      dsimp [spinCoupling]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
        ring
    calc
      (∑ i, ∑ j, D.spinCoupling lam i j * σ i * σ j) =
          ∑ i, ∑ j, (lam / 2) *
            (if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact h_term i j
      _ = ∑ i, (lam / 2) * ∑ j,
            if i = j then 0 else D.ell i * D.ell j * σ i * σ j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum]
      _ = (lam / 2) * (∑ i, ∑ j,
            if i = j then 0 else D.ell i * D.ell j * σ i * σ j) := by
        rw [← Finset.mul_sum]
  rw [h_coupling_term]
  ring

/-! A finite sum with one zero diagonal entry is the corresponding erased sum. -/
theorem sum_eq_sum_erase_of_eq_zero
    {α R : Type*} [AddCommMonoid R] [DecidableEq α]
    (s : Finset α) (a : α) (f : α → R) (ha : a ∈ s) :
    (∑ x ∈ s, if x = a then 0 else f x) = ∑ x ∈ s.erase a, f x := by
  have h := Finset.sum_erase_add s (fun x => if x = a then 0 else f x) ha
  have h' : (∑ x ∈ s, if x = a then 0 else f x) =
      ∑ x ∈ s.erase a, (if x = a then 0 else f x) := by
    simpa using h.symm
  rw [h']
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_erase] at hx
  simp [hx.1]

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
