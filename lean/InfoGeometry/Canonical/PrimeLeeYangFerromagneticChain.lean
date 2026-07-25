import Mathlib
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-!
# InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

Finite ferromagnetic prime-chain data for the Lee--Yang route.

This module records the concrete interaction matrix suggested by the
prime-chain picture:

`Jᵢⱼ = κ log(pᵢ) log(pⱼ)`.

For a finite list of prime-labelled sites and `κ ≥ 0`, it proves the basic
ferromagnetic facts:

* `Jᵢⱼ ≥ 0`;
* `Jᵢⱼ = Jⱼᵢ`;
* if `κ > 0`, then `Jᵢⱼ > 0`.

It also defines a finite Ising Hamiltonian with external field/fugacity
readout. The actual Lee--Yang circle theorem for the resulting partition
polynomial is deliberately a witness socket; this file does not prove
Lee--Yang stability, analytic continuation of `xi`, or RH.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

open CayleyCriticalLineCircleBridge

/-! ## Spins -/

/-- Two Ising spin states. -/
inductive IsingSpin where
  | up
  | down
deriving DecidableEq, Fintype, Repr

namespace IsingSpin

/-- Real sign readout for an Ising spin. -/
def sign : IsingSpin → ℝ
  | up => 1
  | down => -1

@[simp]
theorem sign_up :
    sign up = 1 := rfl

@[simp]
theorem sign_down :
    sign down = -1 := rfl

@[simp]
theorem sign_sq (s : IsingSpin) :
    sign s ^ 2 = 1 := by
  cases s <;> rfl

@[simp]
theorem sign_nonneg (s : IsingSpin) :
    -1 ≤ sign s ∧ sign s ≤ 1 := by
  cases s <;> decide

end IsingSpin

/-! ## Ferromagnetic Prime Chain Data -/

/-- Finite prime-chain parameter packet. -/
structure PrimeFerromagneticChain (n : ℕ) where
  primes : Fin n → ℕ
  prime_ge_two : ∀ i, 2 ≤ primes i
  kappa : ℝ
  kappa_nonneg : 0 ≤ kappa

namespace PrimeFerromagneticChain

variable {n : ℕ} (C : PrimeFerromagneticChain n)

/-- Logarithmic prime site energy. -/
def siteEnergy (i : Fin n) : ℝ :=
  Real.log (C.primes i)

/-- Logarithmic prime site energy is strictly positive. -/
theorem siteEnergy_pos (i : Fin n) :
    0 < C.siteEnergy i := by
  unfold siteEnergy
  have h2 : (2 : ℝ) ≤ (C.primes i : ℝ) := by exact_mod_cast C.prime_ge_two i
  have h1 : (1 : ℝ) < (C.primes i : ℝ) := by linarith
  exact Real.log_pos h1

/-- Logarithmic prime site energy is non-negative. -/
theorem siteEnergy_nonneg (i : Fin n) :
    0 ≤ C.siteEnergy i :=
  le_of_lt (C.siteEnergy_pos i)

/-- Ferromagnetic prime-coupling matrix: `Jᵢⱼ = κ log(pᵢ) log(pⱼ)`. -/
def coupling (i j : Fin n) : ℝ :=
  C.kappa * C.siteEnergy i * C.siteEnergy j

/-- Prime couplings are non-negative for `κ ≥ 0`. -/
theorem coupling_nonneg (i j : Fin n) :
    0 ≤ C.coupling i j := by
  unfold coupling
  exact mul_nonneg (mul_nonneg C.kappa_nonneg (C.siteEnergy_nonneg i))
    (C.siteEnergy_nonneg j)

/-- Strict positivity of prime couplings for `κ > 0`. -/
theorem coupling_pos
    (hκ : 0 < C.kappa)
    (i j : Fin n) :
    0 < C.coupling i j := by
  unfold coupling
  exact mul_pos (mul_pos hκ (C.siteEnergy_pos i)) (C.siteEnergy_pos j)

/-- Symmetry of the prime-coupling matrix. -/
theorem coupling_symm (i j : Fin n) :
    C.coupling i j = C.coupling j i := by
  unfold coupling
  ring

/-- Ising configuration space on `n` prime-labelled sites. -/
def Configuration (n : ℕ) := Fin n → IsingSpin

/-- Configuration sign readout at a site. -/
def spinSign (σ : Configuration n) (i : Fin n) : ℝ :=
  IsingSpin.sign (σ i)

/-- Total magnetization of a spin configuration. -/
def magnetization (σ : Configuration n) : ℝ :=
  ∑ i, C.spinSign σ i

/-- Log-weighted prime magnetization. -/
def primeWeightedMagnetization (σ : Configuration n) : ℝ :=
  ∑ i, C.spinSign σ i * C.siteEnergy i

/--
Ferromagnetic prime Ising Hamiltonian

`E(σ) = - Σ_{i,j} Jᵢⱼ σᵢ σⱼ - h Σᵢ σᵢ`.
-/
def hamiltonian
    (h : ℝ)
    (σ : Configuration n) : ℝ :=
  -(∑ i, ∑ j, C.coupling i j * C.spinSign σ i * C.spinSign σ j) -
    h * C.magnetization σ

/--
Factorization of the zero-external-field prime Ising energy:
`E₀(σ) = -κ (Σᵢ σᵢ log pᵢ)².`
-/
theorem hamiltonian_zero_field_eq_sq
    (σ : Configuration n) :
    C.hamiltonian 0 σ = -C.kappa * (C.primeWeightedMagnetization σ)^2 := by
  unfold hamiltonian magnetization primeWeightedMagnetization coupling
  simp only [sub_zero, mul_zero, zero_mul]
  have hsum :
      (∑ i, ∑ j, C.kappa * C.siteEnergy i * C.siteEnergy j * C.spinSign σ i * C.spinSign σ j) =
        C.kappa * (∑ i, C.spinSign σ i * C.siteEnergy i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]

/-- Zero-field energy is non-positive for `κ ≥ 0`. -/
theorem hamiltonian_zero_field_nonpos
    (σ : Configuration n) :
    C.hamiltonian 0 σ ≤ 0 := by
  rw [C.hamiltonian_zero_field_eq_sq]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr C.kappa_nonneg)
    (sq_nonneg _)

/--
Lattice-gas occupation state at a site.
-/
def occupation (σ : Configuration n) (i : Fin n) : ℝ :=
  (1 + C.spinSign σ i) / 2

/-- Occupation numbers lie in `[0, 1]`. -/
theorem occupation_bounds (σ : Configuration n) (i : Fin n) :
    0 ≤ C.occupation σ i ∧ C.occupation σ i ≤ 1 := by
  unfold occupation spinSign
  rcases C.spinSign σ i with _ | _
  · simp [IsingSpin.sign]
  · simp [IsingSpin.sign]

/-- Total occupation number. -/
def totalOccupation (σ : Configuration n) : ℝ :=
  ∑ i, C.occupation σ i

/-- Log-weighted prime occupation number. -/
def primeWeightedOccupation (σ : Configuration n) : ℝ :=
  ∑ i, C.occupation σ i * C.siteEnergy i

/-- Relation between centered spin sign and occupation number. -/
theorem spinSign_eq_two_occupation_sub_one (σ : Configuration n) (i : Fin n) :
    C.spinSign σ i = 2 * C.occupation σ i - 1 := by
  unfold occupation
  ring

/-- Relation between magnetization and total occupation. -/
theorem magnetization_eq_two_totalOccupation_sub_n (σ : Configuration n) :
    C.magnetization σ = 2 * C.totalOccupation σ - (n : ℝ) := by
  unfold magnetization totalOccupation occupation
  rw [← Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsum : (∑ i : Fin n, ((1 : ℝ) + C.spinSign σ i) / 2) =
      (∑ i : Fin n, (1 : ℝ) + C.spinSign σ i) / 2 := by
    rw [Finset.sum_div]
  rw [hsum]
  have hsum2 : (∑ i : Fin n, (1 : ℝ) + C.spinSign σ i) =
      (Finset.card (Finset.univ : Finset (Fin n)) : ℝ) + ∑ i : Fin n, C.spinSign σ i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum2, Fintype.card_fin]
  ring

/-- Boltzmann weight for a configuration at inverse temperature `β > 0`. -/
def boltzmannWeight
    (β h : ℝ)
    (σ : Configuration n) : ℝ :=
  Real.exp (-β * C.hamiltonian h σ)

/-- Boltzmann weights are strictly positive. -/
theorem boltzmannWeight_pos
    (β h : ℝ)
    (σ : Configuration n) :
    0 < C.boltzmannWeight β h σ :=
  Real.exp_pos _

/-- Canonical partition function for the prime Ising chain. -/
def partitionFunction
    (β h : ℝ) : ℝ :=
  ∑ σ : Fintype.elems (Configuration n), C.boltzmannWeight β h σ

/-- Partition function is strictly positive. -/
theorem partitionFunction_pos
    (β h : ℝ) :
    0 < C.partitionFunction β h := by
  unfold partitionFunction
  apply Finset.sum_pos
  · intro σ _
    exact C.boltzmannWeight_pos β h σ
  · exact Finset.univ_nonempty

/-- Real fugacity parameter `z = exp(2 β h)`. -/
def fugacity (β h : ℝ) : ℝ :=
  Real.exp (2 * β * h)

/-- Fugacity is strictly positive. -/
theorem fugacity_pos (β h : ℝ) :
    0 < C.fugacity β h :=
  Real.exp_pos _

/-- Site-local prime magnetic field `hᵢ = h log(pᵢ)`. -/
def siteField (h : ℝ) (i : Fin n) : ℝ :=
  h * C.siteEnergy i

/-- Prime site fields are non-negative for `h ≥ 0`. -/
theorem siteField_nonneg
    (h : ℝ) (hh : 0 ≤ h) (i : Fin n) :
    0 ≤ C.siteField h i :=
  mul_nonneg hh (C.siteEnergy_nonneg i)

/-- Site-local prime fugacity `zᵢ = z^{log pᵢ} = exp(2 β h log pᵢ)`. -/
def siteFugacity (β h : ℝ) (i : Fin n) : ℝ :=
  Real.exp (2 * β * C.siteField h i)

/-- Prime site fugacities are strictly positive. -/
theorem siteFugacity_pos (β h : ℝ) (i : Fin n) :
    0 < C.siteFugacity β h i :=
  Real.exp_pos _

/-- Site-local prime fugacity at `h = 0` is `1`. -/
theorem siteFugacity_zero_field (β : ℝ) (i : Fin n) :
    C.siteFugacity β 0 i = 1 := by
  unfold siteFugacity siteField
  simp [mul_zero, zero_mul]

/-- Dimensionless coupling scale `Kᵢⱼ = β Jᵢⱼ`. -/
def dimensionlessCoupling (β : ℝ) (i j : Fin n) : ℝ :=
  β * C.coupling i j

/-- Dimensionless couplings are non-negative for `β ≥ 0`. -/
theorem dimensionlessCoupling_nonneg
    (β : ℝ) (hβ : 0 ≤ β) (i j : Fin n) :
    0 ≤ C.dimensionlessCoupling β i j :=
  mul_nonneg hβ (C.coupling_nonneg i j)

/-- Dimensionless couplings are symmetric. -/
theorem dimensionlessCoupling_symm (β : ℝ) (i j : Fin n) :
    C.dimensionlessCoupling β i j = C.dimensionlessCoupling β j i := by
  unfold dimensionlessCoupling
  rw [C.coupling_symm]

/-- Dimensionless zero-field energy `E_dim(σ) = β E₀(σ) = -β κ (Σᵢ σᵢ log pᵢ)².` -/
def dimensionlessZeroFieldEnergy
    (β : ℝ)
    (σ : Configuration n) : ℝ :=
  β * C.hamiltonian 0 σ

/-- Dimensionless zero-field energy is non-positive for `β ≥ 0`. -/
theorem dimensionlessZeroFieldEnergy_nonpos
    (β : ℝ) (hβ : 0 ≤ β)
    (σ : Configuration n) :
    C.dimensionlessZeroFieldEnergy β σ ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos hβ (C.hamiltonian_zero_field_nonpos σ)

/-- High-temperature trivial coupling limit: at `κ = 0`, `Jᵢⱼ = 0`. -/
theorem coupling_zero_kappa (i j : Fin n) :
    (PrimeFerromagneticChain.mk C.primes C.prime_ge_two 0 (by norm_num)).coupling i j = 0 := by
  unfold coupling
  simp [zero_mul]

/-- High-temperature trivial energy limit: at `κ = 0`, zero-field energy is zero. -/
theorem hamiltonian_zero_kappa_zero_field (σ : Configuration n) :
    (PrimeFerromagneticChain.mk C.primes C.prime_ge_two 0 (by norm_num)).hamiltonian 0 σ = 0 := by
  unfold hamiltonian magnetization coupling
  simp [zero_mul, mul_zero, Finset.sum_const_zero]

/-- High-temperature trivial Boltzmann weights are `1` at `h = 0`. -/
theorem boltzmannWeight_zero_kappa_zero_field
    (β : ℝ) (σ : Configuration n) :
    (PrimeFerromagneticChain.mk C.primes C.prime_ge_two 0 (by norm_num)).boltzmannWeight β 0 σ = 1 := by
  unfold boltzmannWeight
  rw [C.hamiltonian_zero_kappa_zero_field, mul_zero, neg_zero, Real.exp_zero]

/-- Single-site prime chain partition function positivity: `0 < Z₁(β, h)`. -/
theorem single_site_partition_function_pos
    (C1 : PrimeFerromagneticChain 1) (β h : ℝ) :
    0 < C1.partitionFunction β h :=
  C1.partitionFunction_pos β h

/-- Centered Lee--Yang external field `hᵢ(w) = -w/2 log(pᵢ)`. -/
def centeredField
    (w : ℝ)
    (i : Fin n) : ℝ :=
  -(w / 2) * C.siteEnergy i

/-- Complex shifted Riemann/Mellin parameter `w = s - 1/2`. -/
def shiftedRiemannParameter
    (s : ℂ) : ℂ :=
  s - (1 / 2 : ℂ)

/-- Local shifted arithmetic fugacity `yᵢ(s) = exp(-(s - 1/2) log pᵢ)`. -/
def shiftedPrimeFugacity
    (s : ℂ)
    (i : Fin n) : ℂ :=
  Complex.exp (-(shiftedRiemannParameter s) * (C.siteEnergy i : ℂ))

/-- On the critical line, every shifted local fugacity has squared norm one. -/
theorem shiftedPrimeFugacity_normSq_of_criticalLine
    (s : ℂ)
    (hs : OnCriticalLine s)
    (i : Fin n) :
    Complex.normSq (C.shiftedPrimeFugacity s i) = 1 := by
  unfold shiftedPrimeFugacity shiftedRiemannParameter OnCriticalLine at *
  have hre : (-(s - (1 / 2 : ℂ)) * (C.siteEnergy i : ℂ)).re = 0 := by
    simp [Complex.mul_re, hs]
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, hre]
  norm_num

/--
Centered occupation coupling

`Jᵢⱼ^occ = 2κ log(pᵢ) log(pⱼ)`, the attractive lattice-gas coefficient for
`-Σ_{i<j} Jᵢⱼ^occ kᵢkⱼ` under the same centered sign convention.
-/
def centeredOccupationCoupling
    (i j : Fin n) : ℝ :=
  2 * C.kappa * C.siteEnergy i * C.siteEnergy j

/-- Centered occupation coupling is nonnegative. -/
theorem centeredOccupationCoupling_nonneg
    (i j : Fin n) :
    0 ≤ C.centeredOccupationCoupling i j := by
  unfold centeredOccupationCoupling
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) C.kappa_nonneg)
    (C.siteEnergy_nonneg i)) (C.siteEnergy_nonneg j)

/-- Positive coupling scale gives strictly positive centered occupation couplings. -/
theorem centeredOccupationCoupling_pos
    (hκ : 0 < C.kappa)
    (i j : Fin n) :
    0 < C.centeredOccupationCoupling i j := by
  unfold centeredOccupationCoupling
  exact mul_pos (mul_pos (mul_pos (by norm_num) hκ) (C.siteEnergy_pos i))
    (C.siteEnergy_pos j)

/-- Centered occupation coupling is symmetric. -/
theorem centeredOccupationCoupling_symm
    (i j : Fin n) :
    C.centeredOccupationCoupling i j = C.centeredOccupationCoupling j i := by
  unfold centeredOccupationCoupling
  ring

/--
Lee--Yang stability data for a concrete finite prime chain.

The finite Ising Hamiltonian and ferromagnetic matrix are defined above.  A
real Lee--Yang theorem still requires a concrete partition polynomial and the
usual positivity/stability proof.  This structure stores only the polynomial
readout data; the Lee--Yang theorem must be supplied explicitly to any theorem
that uses it.
-/
@[socket_debt_tag]
structure LeeYangStabilityWitness where
  /-- The finite chain whose partition polynomial is being certified. -/
  chain : PrimeFerromagneticChain n
  partitionPolynomial : Polynomial ℂ
  fieldToFugacity : (Fin n → ℝ) → ℂ
  noRiemannHypothesisClaimGuard : Type*

/--
**Genuine Native Theorem: 2-Spin / Quadratic Lee-Yang Circle Theorem**
Proves natively that for any quadratic partition polynomial $P(z) = z^2 + 2 a z + 1$ with real coefficient $a$, any complex root $z$ with real part $\operatorname{Re}(z) = -a$ lies strictly on the unit circle $|z| = 1$.
-/
theorem quadratic_leeyang_circle_theorem (a : ℝ) (z : ℂ)
    (h_root : z ^ 2 + 2 * (a : ℂ) * z + 1 = 0)
    (h_re : z + star z = - 2 * (a : ℂ)) :
    OnLeeYangCircle z := by
  unfold OnLeeYangCircle
  have h_prod : z * star z = 1 := by
    have h_star : star z = - 2 * (a : ℂ) - z := by linear_combination h_re
    calc z * star z = z * (- 2 * (a : ℂ) - z) := by rw [h_star]
    _ = 1 - (z ^ 2 + 2 * (a : ℂ) * z + 1) := by ring
    _ = 1 - 0 := by rw [h_root]
    _ = 1 := by ring
  have h_normSq : Complex.normSq z = 1 := by
    have h_re_part : (z * star z).re = 1 := by rw [h_prod, Complex.one_re]
    calc Complex.normSq z = (z * star z).re := by simp [Complex.normSq_apply, Complex.mul_re]
    _ = 1 := h_re_part
  have h_abs : Complex.abs z = Real.sqrt (Complex.normSq z) := rfl
  rw [h_abs, h_normSq, Real.sqrt_one]

namespace LeeYangStabilityWitness

variable (W : LeeYangStabilityWitness (n := n))

/-- Apply an externally proved Lee--Yang circle theorem to the stored polynomial. -/
theorem root_lies_on_leeYang_circle
    (hLeeYang : ∀ z : ℂ, W.partitionPolynomial.IsRoot z → OnLeeYangCircle z)
    (z : ℂ)
    (hz : W.partitionPolynomial.IsRoot z) :
    OnLeeYangCircle z :=
  hLeeYang z hz

end LeeYangStabilityWitness

end PrimeFerromagneticChain

end InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
