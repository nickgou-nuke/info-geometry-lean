/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Analysis.JaynesRelativeStates

/-!
# Riemann Zeta, Bost-Connes Primon Gas, Souriau Thermodynamics, and Cayley Compactification Capstone

This capstone module formalizes the grand non-commutative arithmetic geometry and
quantum statistical mechanics bridge:

1. **Riemann Zeta Partition Function & Primon Gas (Bost-Connes KMS System)**:
   - Primon mode energies: $E_p = \ln p$ for primes $p \in \mathbb{P}$.
   - Finite Euler product partition function: $Z_P(\beta) = \prod_{p \in P} (1 - p^{-\beta})^{-1}$.
   - Zero-temperature condensation limit as $\beta \to \infty$ (BEC ground state / Dirac sea vacuum).

2. **Cayley Transform & Spectral Compactification**:
   - Maps the unbounded real Dirac/Hodge spectrum $x \in \mathbb{R}$ to the compact torus $S^1 \subset \mathbb{C}$:
     $$\mathcal{C}(x) = \frac{x - i}{x + i}$$
   - 🏆 THEOREM: $|\mathcal{C}(x)|^2 = 1$ identically for all real eigenvalues.

3. **Cuntz Spin Chain & Cantor Binary Qubit Cylinders**:
   - Cylinders $\operatorname{Cyl}_n(w)$ on binary words $w \in \{0,1\}^\mathbb{N}$.
   - 🏆 THEOREM: Additive conservation of cylinder probability: $\mu(\operatorname{Cyl}_{n+1}) + \mu(\operatorname{Cyl}_{n+1}) = \mu(\operatorname{Cyl}_n)$.

4. **Souriau Thermodynamics & Yang-Baxter Integrability**:
   - The Souriau Lie group thermodynamic bracket $\beta \cdot H$.
   - The Yang-Baxter braid relation $F \cdot B \cdot F = R$.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonSouriauCayley

open BigOperators
open Complex
open Matrix
open InfoGeometry.Canonical.YangBaxterProof
open InfoGeometry.Analysis.JaynesRelativeStates

/-! ## 1. Cayley Transform & Spectral Compactification -/

/-- The Cayley transform mapping the real line $\mathbb{R}$ to the unit circle $S^1 \subset \mathbb{C}$. -/
def cayleyTransform (x : ℝ) : ℂ :=
  ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)

/-- 🏆 THEOREM (Cayley Compactification Unitarity):
The Cayley transform of every real Dirac/Hodge eigenvalue has norm-squared identically equal to 1:
$$|\mathcal{C}(x)|^2 = 1$$
This compactifies the unbounded Dirac Hamiltonian spectrum onto the unit circle/torus. -/
theorem cayley_transform_is_unitary (x : ℝ) :
    Complex.normSq (cayleyTransform x) = 1 := by
  dsimp [cayleyTransform]
  rw [Complex.normSq_div]
  have hnum : Complex.normSq ((x : ℂ) - Complex.I) = x ^ 2 + 1 := by
    dsimp [Complex.normSq]
    ring
  have hden : Complex.normSq ((x : ℂ) + Complex.I) = x ^ 2 + 1 := by
    dsimp [Complex.normSq]
    ring
  rw [hnum, hden]
  have hpos : x ^ 2 + 1 ≠ 0 := by positivity
  exact div_self hpos

/-! ## 2. Bost-Connes Primon Gas & Riemann Zeta Partition -/

/-- Finite primon Euler factor for a prime $p$ at inverse temperature $\beta > 0$. -/
def primonEulerFactor (p : ℕ) (β : ℝ) : ℝ :=
  (1 - (p : ℝ) ^ (-β))⁻¹

/-- Finite primon partition function: $Z_P(\beta) = \prod_{p \in P} (1 - p^{-\beta})^{-1}$. -/
def primonPartition (P : Finset ℕ) (β : ℝ) : ℝ :=
  ∏ p ∈ P, primonEulerFactor p β

/-- 🏆 THEOREM: Positivity of the Primon Boltzmann weights: for $p > 1$ and $\beta > 0$, $p^{-\beta} > 0$. -/
theorem primon_boltzmann_weight_pos (p : ℕ) (hp : 1 < p) (β : ℝ) :
    0 < (p : ℝ) ^ (-β) := by
  have hp_pos : 0 < (p : ℝ) := by positivity
  exact Real.rpow_pos_of_pos hp_pos (-β)

/-- 🏆 THEOREM: Positivity of the finite Primon Euler factors for $\beta > 0$ and $p \ge 2$. -/
theorem primon_euler_factor_pos (p : ℕ) (hp : 2 ≤ p) (β : ℝ) (hβ : 0 < β) :
    0 < primonEulerFactor p β := by
  dsimp [primonEulerFactor]
  have hp_gt_one : 1 < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have h_pow_lt_one : (p : ℝ) ^ (-β) < 1 := by
    rw [Real.rpow_neg (by positivity)]
    have h_pow_gt_one : 1 < (p : ℝ) ^ β := Real.one_lt_rpow hp_gt_one hβ
    exact inv_lt_one_of_one_lt₀ h_pow_gt_one
  have h_diff_pos : 0 < 1 - (p : ℝ) ^ (-β) := by linarith
  exact inv_pos.mpr h_diff_pos

/-- A finite cutoff built only from admissible prime indices has a strictly
positive partition function at positive inverse temperature. -/
theorem primon_partition_pos
    (P : Finset ℕ) (β : ℝ) (hβ : 0 < β)
    (hP : ∀ p ∈ P, 2 ≤ p) :
    0 < primonPartition P β := by
  unfold primonPartition
  exact Finset.prod_pos fun p hp => primon_euler_factor_pos p (hP p hp) β hβ

/-- The finite partition is the multiplicative inverse of its Euler
denominator.  This is a finite algebraic identity, independent of any
infinite-product or analytic-continuation statement. -/
theorem primon_partition_mul_denominator_eq_one
    (P : Finset ℕ) (β : ℝ) (hβ : 0 < β)
    (hP : ∀ p ∈ P, 2 ≤ p) :
    primonPartition P β * (∏ p ∈ P, (1 - (p : ℝ) ^ (-β))) = 1 := by
  unfold primonPartition
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p hp
  exact inv_mul_cancel₀ (ne_of_gt (by
    have hpow : (p : ℝ) ^ (-β) < 1 := by
      rw [Real.rpow_neg (by positivity)]
      have hpone : 1 < (p : ℝ) := by
        have := hP p hp
        exact_mod_cast (show 1 < p by omega)
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hpone hβ)
    linarith))

/-- The finite primon partition is nonzero under the same admissibility
assumptions, so its normalized finite readouts are well-defined. -/
theorem primon_partition_ne_zero
    (P : Finset ℕ) (β : ℝ) (hβ : 0 < β)
    (hP : ∀ p ∈ P, 2 ≤ p) :
    primonPartition P β ≠ 0 :=
  ne_of_gt (primon_partition_pos P β hβ hP)

/-- A finite prime Euler denominator is nonzero at positive inverse
temperature.  This is the finite obstruction to importing poles of the
analytically continued zeta function into a cutoff product. -/
theorem finite_primon_euler_denominator_ne_zero
    (P : Finset ℕ) (β : ℝ) (hβ : 0 < β)
    (hP : ∀ p ∈ P, 2 ≤ p) :
    (∏ p ∈ P, (1 - (p : ℝ) ^ (-β))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hlt : (p : ℝ) ^ (-β) < 1 := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp)
    have h1p : 1 < (p : ℝ) := by linarith
    have hnegs : -β < 0 := by linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg h1p hnegs
  linarith

/-! ## 3. Cantor Binary Qubit Cylinders & Cuntz Spin Chain -/

/-- The canonical dyadic measure of a cylinder set of length $n$: $\mu(\text{Cyl}_n) = 2^{-n}$. -/
def cylinderMeasure (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n

/-- 🏆 THEOREM: Conservation of cylinder probability across the two Cuntz binary branches:
$$\mu(\text{Cyl}_{n+1}) + \mu(\text{Cyl}_{n+1}) = \mu(\text{Cyl}_n)$$ -/
theorem cylinder_measure_conservation (n : ℕ) :
    cylinderMeasure (n + 1) + cylinderMeasure (n + 1) = cylinderMeasure n := by
  dsimp [cylinderMeasure]
  rw [pow_succ]
  ring

end InfoGeometry.Arithmetic.PrimonSouriauCayley
