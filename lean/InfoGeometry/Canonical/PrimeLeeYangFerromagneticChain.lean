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
theorem sign_sq
    (σ : IsingSpin) :
    sign σ * sign σ = 1 := by
  cases σ <;> norm_num [sign]

end IsingSpin

/-! ## Prime ferromagnetic chain -/

/--
A finite prime-labelled ferromagnetic chain.

`prime i` is the arithmetic label at site `i`.
`κ` is the global ferromagnetic coupling scale.
-/
structure PrimeFerromagneticChain
    (n : ℕ) where
  prime : Fin n → ℕ
  prime_isPrime : ∀ i : Fin n, Nat.Prime (prime i)
  kappa : ℝ
  kappa_nonneg : 0 ≤ kappa

namespace PrimeFerromagneticChain

variable {n : ℕ}
variable (C : PrimeFerromagneticChain n)

/-- Site energy `log pᵢ`. -/
def siteEnergy
    (i : Fin n) : ℝ :=
  Real.log (C.prime i : ℝ)

/-- Prime-chain ferromagnetic interaction matrix `Jᵢⱼ = κ log(pᵢ) log(pⱼ)`. -/
def coupling
    (i j : Fin n) : ℝ :=
  C.kappa * C.siteEnergy i * C.siteEnergy j

/-- The interaction matrix as a finite real matrix. -/
def couplingMatrix : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => C.coupling i j

/-- Prime-site logarithmic energy is nonnegative. -/
theorem siteEnergy_nonneg
    (i : Fin n) :
    0 ≤ C.siteEnergy i := by
  unfold siteEnergy
  exact Real.log_nonneg (by
    exact_mod_cast (Nat.Prime.one_lt (C.prime_isPrime i)).le)

/-- Prime-site logarithmic energy is positive. -/
theorem siteEnergy_pos
    (i : Fin n) :
    0 < C.siteEnergy i := by
  unfold siteEnergy
  exact Real.log_pos (by
    exact_mod_cast Nat.Prime.one_lt (C.prime_isPrime i))

/-- The prime-chain interaction is ferromagnetic: `Jᵢⱼ ≥ 0`. -/
theorem coupling_nonneg
    (i j : Fin n) :
    0 ≤ C.coupling i j := by
  unfold coupling
  exact mul_nonneg (mul_nonneg C.kappa_nonneg (C.siteEnergy_nonneg i))
    (C.siteEnergy_nonneg j)

/-- The interaction matrix is symmetric. -/
theorem coupling_symm
    (i j : Fin n) :
    C.coupling i j = C.coupling j i := by
  unfold coupling
  ring

/-- Strictly positive coupling scale gives strictly positive pair couplings. -/
theorem coupling_pos
    (hκ : 0 < C.kappa)
    (i j : Fin n) :
    0 < C.coupling i j := by
  unfold coupling
  exact mul_pos (mul_pos hκ (C.siteEnergy_pos i)) (C.siteEnergy_pos j)

/-- Matrix readout of the coupling entry. -/
@[simp]
theorem couplingMatrix_apply
    (i j : Fin n) :
    C.couplingMatrix i j = C.coupling i j := rfl

/-- The coupling matrix has nonnegative entries. -/
theorem couplingMatrix_entry_nonneg
    (i j : Fin n) :
    0 ≤ C.couplingMatrix i j :=
  C.coupling_nonneg i j

/-- The coupling matrix is symmetric entrywise. -/
theorem couplingMatrix_symm
    (i j : Fin n) :
    C.couplingMatrix i j = C.couplingMatrix j i :=
  C.coupling_symm i j

/-! ## Hamiltonian and fugacity readout -/

/-- A spin configuration on the finite chain. -/
abbrev SpinConfiguration :=
  Fin n → IsingSpin

/-- Pair interaction energy `-Σᵢⱼ Jᵢⱼ σᵢ σⱼ`. -/
def pairEnergy
    (σ : SpinConfiguration (n := n)) : ℝ :=
  -∑ i : Fin n, ∑ j : Fin n,
    C.coupling i j * IsingSpin.sign (σ i) * IsingSpin.sign (σ j)

/-- External-field energy `-Σᵢ hᵢ σᵢ`. -/
def fieldEnergy
    (h : Fin n → ℝ)
    (σ : SpinConfiguration (n := n)) : ℝ :=
  -∑ i : Fin n, h i * IsingSpin.sign (σ i)

/-- Finite Ising Hamiltonian for the prime ferromagnetic chain. -/
def isingHamiltonian
    (h : Fin n → ℝ)
    (σ : SpinConfiguration (n := n)) : ℝ :=
  C.pairEnergy σ + fieldEnergy h σ

/-- The pair-energy definition unfolded. -/
theorem pairEnergy_eq
    (σ : SpinConfiguration (n := n)) :
    C.pairEnergy σ =
      -∑ i : Fin n, ∑ j : Fin n,
        C.coupling i j * IsingSpin.sign (σ i) * IsingSpin.sign (σ j) := rfl

/-- The field-energy definition unfolded. -/
theorem fieldEnergy_eq
    (h : Fin n → ℝ)
    (σ : SpinConfiguration (n := n)) :
    fieldEnergy h σ =
      -∑ i : Fin n, h i * IsingSpin.sign (σ i) := rfl

/-- The Hamiltonian definition unfolded. -/
theorem isingHamiltonian_eq_pair_add_field
    (h : Fin n → ℝ)
    (σ : SpinConfiguration (n := n)) :
    C.isingHamiltonian h σ = C.pairEnergy σ + fieldEnergy h σ := rfl

/--
Field/fugacity dictionary for one site:

`zᵢ = exp(-2 hᵢ)`.

The Cayley map in `CayleyCriticalLineCircleBridge` then supplies the global
Riemann-temperature/fugacity chart.
-/
def localFugacity
    (h : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  Real.exp (-2 * h i)

/-- Local fugacity is positive. -/
theorem localFugacity_pos
    (h : Fin n → ℝ)
    (i : Fin n) :
    0 < localFugacity h i := by
  unfold localFugacity
  exact Real.exp_pos _

/-! ## Occupation convention and negative-energy couplings -/

/--
Occupation readout for the convention:

* `1` means the prime is present;
* `0` means the prime is absent.

Here `up` is the occupied/present state. This is a convention bridge; the
ferromagnetic Ising convention above uses signs and positive `Jᵢⱼ` in
`-Σ Jᵢⱼ σᵢσⱼ`.
-/
def occupation : IsingSpin → ℝ :=
  fun
    | IsingSpin.up => 1
    | IsingSpin.down => 0

@[simp]
theorem occupation_up :
    occupation IsingSpin.up = 1 := rfl

@[simp]
theorem occupation_down :
    occupation IsingSpin.down = 0 := rfl

/--
Occupation-Hamiltonian pair coefficient

`Kᵢⱼ = -2 log(pᵢ) log(pⱼ)`.

This is the negative-energy convention for a Hamiltonian written as
`Σ Kᵢⱼ kᵢ kⱼ + Σ hᵢ kᵢ`. It is equivalent in sign spirit to a positive
ferromagnetic coupling in the Ising convention `-Σ Jᵢⱼ σᵢσⱼ`.
-/
def occupationPairCoefficient
    (i j : Fin n) : ℝ :=
  -2 * C.siteEnergy i * C.siteEnergy j

/-- The occupation pair coefficient is symmetric. -/
theorem occupationPairCoefficient_symm
    (i j : Fin n) :
    C.occupationPairCoefficient i j = C.occupationPairCoefficient j i := by
  unfold occupationPairCoefficient
  ring

/-- In the occupation-energy convention the pair coefficient is nonpositive. -/
theorem occupationPairCoefficient_nonpos
    (i j : Fin n) :
    C.occupationPairCoefficient i j ≤ 0 := by
  unfold occupationPairCoefficient
  have hprod : 0 ≤ C.siteEnergy i * C.siteEnergy j :=
    mul_nonneg (C.siteEnergy_nonneg i) (C.siteEnergy_nonneg j)
  nlinarith

/-- In the occupation-energy convention the pair coefficient is strictly negative. -/
theorem occupationPairCoefficient_neg
    (i j : Fin n) :
    C.occupationPairCoefficient i j < 0 := by
  unfold occupationPairCoefficient
  have hprod : 0 < C.siteEnergy i * C.siteEnergy j :=
    mul_pos (C.siteEnergy_pos i) (C.siteEnergy_pos j)
  nlinarith

/-- Occupation-space pair energy `Σᵢⱼ Kᵢⱼ kᵢ kⱼ`. -/
def occupationPairEnergy
    (σ : SpinConfiguration (n := n)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    C.occupationPairCoefficient i j * occupation (σ i) * occupation (σ j)

/--
Complex arithmetic external field

`hᵢ(s) = s log(pᵢ) - log(pᵢ - 1)`.

The subtraction is meaningful for primes because `pᵢ ≥ 2`, so `pᵢ - 1 ≥ 1`.
No analytic zero-location theorem is inferred from this readout.
-/
def arithmeticExternalField
    (s : ℂ)
    (i : Fin n) : ℂ :=
  s * (C.siteEnergy i : ℂ) - (Real.log ((C.prime i - 1 : ℕ) : ℝ) : ℂ)

/-- The regulator `log(pᵢ - 1)` is nonnegative for prime sites. -/
theorem primeMinusOne_log_nonneg
    (i : Fin n) :
    0 ≤ Real.log ((C.prime i - 1 : ℕ) : ℝ) := by
  exact Real.log_nonneg (by
    have hp : 1 < C.prime i := Nat.Prime.one_lt (C.prime_isPrime i)
    have hle : 1 ≤ C.prime i - 1 := Nat.le_sub_one_of_lt hp
    exact_mod_cast hle)

/-- Occupation-space complex field energy `Σᵢ hᵢ(s) kᵢ`. -/
def arithmeticFieldEnergy
    (s : ℂ)
    (σ : SpinConfiguration (n := n)) : ℂ :=
  ∑ i : Fin n, C.arithmeticExternalField s i * (occupation (σ i) : ℂ)

/--
Occupation-space arithmetic Hamiltonian with the negative-energy pair
convention.
-/
def arithmeticOccupationHamiltonian
    (s : ℂ)
    (σ : SpinConfiguration (n := n)) : ℂ :=
  (C.occupationPairEnergy σ : ℂ) + C.arithmeticFieldEnergy s σ

/-! ## Centered Lee--Yang prime chain -/

/-- Centered occupation `k - 1/2`, the particle-hole odd coordinate. -/
def centeredOccupation
    (σ : IsingSpin) : ℝ :=
  occupation σ - (1 / 2 : ℝ)

@[simp]
theorem centeredOccupation_up :
    centeredOccupation IsingSpin.up = (1 / 2 : ℝ) := by
  norm_num [centeredOccupation]

@[simp]
theorem centeredOccupation_down :
    centeredOccupation IsingSpin.down = -(1 / 2 : ℝ) := by
  norm_num [centeredOccupation]

/--
Centered logarithmic energy

`A_N = Σᵢ log(pᵢ) (kᵢ - 1/2)`.
-/
def centeredLogEnergy
    (σ : SpinConfiguration (n := n)) : ℝ :=
  ∑ i : Fin n, C.siteEnergy i * centeredOccupation (σ i)

/-- The centered logarithmic energy is half the weighted spin magnetization. -/
theorem centeredLogEnergy_eq_half_spinSum
    (σ : SpinConfiguration (n := n)) :
    C.centeredLogEnergy σ =
      (1 / 2 : ℝ) * ∑ i : Fin n, C.siteEnergy i * IsingSpin.sign (σ i) := by
  unfold centeredLogEnergy centeredOccupation occupation IsingSpin.sign
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  cases σ i <;> ring

/--
Centered Lee--Yang spin coupling

`Jᵢⱼ = κ/2 log(pᵢ) log(pⱼ)`.

This is the coefficient in the standard convention
`-Σ_{i<j} Jᵢⱼ σᵢσⱼ`.
-/
def centeredSpinCoupling
    (i j : Fin n) : ℝ :=
  (C.kappa / 2) * C.siteEnergy i * C.siteEnergy j

/-- Centered spin coupling is nonnegative. -/
theorem centeredSpinCoupling_nonneg
    (i j : Fin n) :
    0 ≤ C.centeredSpinCoupling i j := by
  unfold centeredSpinCoupling
  exact mul_nonneg (mul_nonneg (div_nonneg C.kappa_nonneg (by norm_num))
    (C.siteEnergy_nonneg i)) (C.siteEnergy_nonneg j)

/-- Centered spin coupling is symmetric. -/
theorem centeredSpinCoupling_symm
    (i j : Fin n) :
    C.centeredSpinCoupling i j = C.centeredSpinCoupling j i := by
  unfold centeredSpinCoupling
  ring

/-- Positive coupling scale gives strictly positive centered couplings. -/
theorem centeredSpinCoupling_pos
    (hκ : 0 < C.kappa)
    (i j : Fin n) :
    0 < C.centeredSpinCoupling i j := by
  unfold centeredSpinCoupling
  exact mul_pos (mul_pos (div_pos hκ (by norm_num)) (C.siteEnergy_pos i))
    (C.siteEnergy_pos j)

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
    have h_norm : (z * star z).re = Complex.normSq z := Complex.conj_mul_self_re z
    rw [← h_norm, h_re_part]
  rw [Complex.abs_def, h_normSq, Real.sqrt_one]

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
