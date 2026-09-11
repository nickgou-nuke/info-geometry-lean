/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.BostConnesGeneratorsBridge

/-!
# Bost-Connes 1-Parameter Modular Automorphism Group and Range Invariance

This module formalizes the 1-parameter modular automorphism group $\sigma_t$ ($t \in \mathbb{R}$)
of the Bost-Connes C*-algebraic dynamical system $\mathcal{C}_\mathbb{Q}$, and proves the strict
invariance of the gauge range projections under the time flow:

1. **Modular Phase Flow**:
   - Central unitary character $u(t, n) = n^{it} \in \mathcal{Z}(A)$ on $\mathbb{N}^+$.
   - Unitarity: $u(t, n)^* u(t, n) = 1$ and $u(t, n) u(t, n)^* = 1$.
   - Multiplicativity: $u(t, mn) = u(t, m) u(t, n)$.
   - 1-Parameter Group Law: $u(0, n) = 1$ and $u(s+t, n) = u(s, n) u(t, n)$.

2. **Action on Generators**:
   - On semigroup isometries: $\sigma_t(\mu_n) = u(t, n) \mu_n$.
   - On phase unitaries: $\sigma_t(e(\gamma)) = e(\gamma)$ (time-invariant fixed points).

3. **Preservation of Bost-Connes Algebraic Relations**:
   - Identity isometry: $\sigma_t(\mu_1) = 1$ (`sigma_mu_one`).
   - Semigroup morphism: $\sigma_t(\mu_{mn}) = \sigma_t(\mu_m) \sigma_t(\mu_n)$ (`sigma_mu_mul`).
   - Isometric normalization: $\sigma_t(\mu_n)^* \sigma_t(\mu_n) = 1$ (`sigma_mu_isometry`).
   - Right covariance: $\sigma_t(\mu_n)^* \sigma_t(e(\gamma)) = \sigma_t(e(n \cdot \gamma)) \sigma_t(\mu_n)^*$ (`sigma_cov_right`).
   - Left covariance: $\sigma_t(e(\gamma)) \sigma_t(\mu_n) = \sigma_t(\mu_n) \sigma_t(e(n \cdot \gamma))$ (`sigma_cov_left`).
   - Coprime Hecke commutation: $\gcd(m, n) = 1 \implies \sigma_t(\mu_m)^* \sigma_t(\mu_n) = \sigma_t(\mu_n) \sigma_t(\mu_m)^*$ (`sigma_hecke_coprime`).

4. **Automorphism System & Gauge Invariance**:
   - Transformed structure: `sigma_structure (t : ℝ) : BostConnesStructure A Γ`.
   - Strict range projection invariance: $\sigma_t(P_n) = P_n$ (`sigma_P_invariance`).
     The gauge range projections $P_n = \mu_n \mu_n^*$ are exact constants of motion
     under the Hamiltonian modular time evolution.

5. **1-Parameter Dynamics & Group Laws**:
   - Initial identity: $\sigma_0(\mu_n) = \mu_n$ (`sigma_zero_mu`) and $\sigma_0(e(\gamma)) = e(\gamma)$ (`sigma_zero_e`).
   - Flow composition: $\sigma_{s+t}(\mu_n) = u(s, n) \sigma_t(\mu_n)$ (`sigma_add_mu`).
   - Time reversal / inverse: $u(-t, n) \sigma_t(\mu_n) = \mu_n$ (`sigma_inverse_mu`).

6. **Master Synthesis Theorem**:
   - Unbroken kernel certification of all 8 core dynamical pillars (`bost_connes_modular_automorphism_synthesis`).
-/

namespace InfoGeometry.Algebra.BostConnesModularAutomorphism

open InfoGeometry.Algebra.BostConnesGenerators

variable {A : Type*} [Ring A] [StarRing A]
variable {Γ : Type*} [AddCommGroup Γ]

/-- The 1-parameter central unitary phase character u(t, n) = n^(it) on ℕ+. -/
structure ModularPhaseFlow (A : Type*) [Ring A] [StarRing A] where
  u : ℝ → ℕ+ → A
  central : ∀ t n x, u t n * x = x * u t n
  unitary : ∀ t n, star (u t n) * u t n = 1
  mul : ∀ t m n, u t (m * n) = u t m * u t n
  one : ∀ t, u t 1 = 1
  time_zero : ∀ n, u 0 n = 1
  time_add : ∀ s t n, u (s + t) n = u s n * u t n

namespace ModularPhaseFlow

variable (MF : ModularPhaseFlow A) (B : BostConnesStructure A Γ)

lemma star_central (t : ℝ) (n : ℕ+) (x : A) :
    star (MF.u t n) * x = x * star (MF.u t n) := by
  have h := MF.central t n (star x)
  have h_star := congrArg star h
  simp only [star_mul, star_star] at h_star
  exact h_star.symm

lemma unitary_right (t : ℝ) (n : ℕ+) :
    MF.u t n * star (MF.u t n) = 1 := by
  rw [MF.central t n (star (MF.u t n))]
  exact MF.unitary t n

/-- Modular action on semigroup isometries: σ_t(μ_n) = u(t, n) * μ_n. -/
def sigma_mu (t : ℝ) (n : ℕ+) : A :=
  MF.u t n * B.μ n

/-- Modular action on phase unitaries: σ_t(e(γ)) = e(γ). -/
def sigma_e (_MF : ModularPhaseFlow A) (_t : ℝ) (g : Γ) : A :=
  B.e g

theorem sigma_mu_one (t : ℝ) :
    MF.sigma_mu B t 1 = 1 := by
  dsimp [sigma_mu]
  rw [MF.one t, B.μ_one, mul_one]

theorem sigma_mu_mul (t : ℝ) (m n : ℕ+) :
    MF.sigma_mu B t (m * n) = MF.sigma_mu B t m * MF.sigma_mu B t n := by
  dsimp [sigma_mu]
  rw [MF.mul t m n, B.μ_mul m n]
  calc MF.u t m * MF.u t n * (B.μ m * B.μ n)
    _ = MF.u t m * (MF.u t n * (B.μ m * B.μ n)) := by rw [mul_assoc]
    _ = MF.u t m * ((MF.u t n * B.μ m) * B.μ n) := by rw [← mul_assoc (MF.u t n)]
    _ = MF.u t m * ((B.μ m * MF.u t n) * B.μ n) := by rw [MF.central t n (B.μ m)]
    _ = MF.u t m * (B.μ m * (MF.u t n * B.μ n)) := by rw [mul_assoc (B.μ m)]
    _ = (MF.u t m * B.μ m) * (MF.u t n * B.μ n) := by rw [← mul_assoc]

theorem sigma_mu_isometry (t : ℝ) (n : ℕ+) :
    star (MF.sigma_mu B t n) * MF.sigma_mu B t n = 1 := by
  dsimp [sigma_mu]
  rw [star_mul]
  calc star (B.μ n) * star (MF.u t n) * (MF.u t n * B.μ n)
    _ = star (B.μ n) * (star (MF.u t n) * (MF.u t n * B.μ n)) := by rw [mul_assoc]
    _ = star (B.μ n) * ((star (MF.u t n) * MF.u t n) * B.μ n) := by rw [← mul_assoc (star (MF.u t n))]
    _ = star (B.μ n) * (1 * B.μ n)                            := by rw [MF.unitary t n]
    _ = star (B.μ n) * B.μ n                                  := by rw [one_mul]
    _ = 1                                                     := B.μ_isometry n

theorem sigma_cov_right (t : ℝ) (n : ℕ+) (g : Γ) :
    star (MF.sigma_mu B t n) * MF.sigma_e B t g =
      MF.sigma_e B t ((n : ℕ) • g) * star (MF.sigma_mu B t n) := by
  dsimp [sigma_mu, sigma_e]
  rw [star_mul]
  calc star (B.μ n) * star (MF.u t n) * B.e g
    _ = star (B.μ n) * (star (MF.u t n) * B.e g) := by rw [mul_assoc]
    _ = star (B.μ n) * (B.e g * star (MF.u t n)) := by rw [MF.star_central t n (B.e g)]
    _ = (star (B.μ n) * B.e g) * star (MF.u t n) := by rw [← mul_assoc]
    _ = (B.e ((n : ℕ) • g) * star (B.μ n)) * star (MF.u t n) := by rw [B.covar_right n g]
    _ = B.e ((n : ℕ) • g) * (star (B.μ n) * star (MF.u t n)) := by rw [mul_assoc]

theorem sigma_cov_left (t : ℝ) (n : ℕ+) (g : Γ) :
    MF.sigma_e B t g * MF.sigma_mu B t n =
      MF.sigma_mu B t n * MF.sigma_e B t ((n : ℕ) • g) := by
  dsimp [sigma_mu, sigma_e]
  calc B.e g * (MF.u t n * B.μ n)
    _ = (B.e g * MF.u t n) * B.μ n := by rw [← mul_assoc]
    _ = (MF.u t n * B.e g) * B.μ n := by rw [← MF.central t n (B.e g)]
    _ = MF.u t n * (B.e g * B.μ n) := by rw [mul_assoc]
    _ = MF.u t n * (B.μ n * B.e ((n : ℕ) • g)) := by rw [B.covar_left n g]
    _ = (MF.u t n * B.μ n) * B.e ((n : ℕ) • g) := by rw [← mul_assoc]

theorem sigma_hecke_coprime (t : ℝ) (m n : ℕ+) (h : Nat.Coprime m.val n.val) :
    star (MF.sigma_mu B t m) * MF.sigma_mu B t n =
      MF.sigma_mu B t n * star (MF.sigma_mu B t m) := by
  dsimp [sigma_mu]
  simp only [star_mul]
  have h_comm := B.hecke_coprime m n h
  calc star (B.μ m) * star (MF.u t m) * (MF.u t n * B.μ n)
    _ = star (B.μ m) * (star (MF.u t m) * (MF.u t n * B.μ n)) := by rw [mul_assoc]
    _ = star (B.μ m) * ((star (MF.u t m) * MF.u t n) * B.μ n) := by rw [← mul_assoc (star (MF.u t m))]
    _ = star (B.μ m) * ((MF.u t n * star (MF.u t m)) * B.μ n) := by rw [MF.star_central t m (MF.u t n)]
    _ = star (B.μ m) * (MF.u t n * (star (MF.u t m) * B.μ n)) := by simp only [mul_assoc]
    _ = star (B.μ m) * (MF.u t n * (B.μ n * star (MF.u t m))) := by rw [MF.star_central t m (B.μ n)]
    _ = (star (B.μ m) * MF.u t n) * (B.μ n * star (MF.u t m)) := by simp only [mul_assoc]
    _ = (MF.u t n * star (B.μ m)) * (B.μ n * star (MF.u t m)) := by rw [← MF.central t n (star (B.μ m))]
    _ = MF.u t n * (star (B.μ m) * B.μ n) * star (MF.u t m)   := by simp only [mul_assoc]
    _ = MF.u t n * (B.μ n * star (B.μ m)) * star (MF.u t m)   := by rw [h_comm]
    _ = (MF.u t n * B.μ n) * (star (B.μ m) * star (MF.u t m)) := by simp only [mul_assoc]

/-- The transformed Bost-Connes structure under modular time evolution σ_t. -/
def sigma_structure (t : ℝ) : BostConnesStructure A Γ where
  e := MF.sigma_e B t
  e_zero := B.e_zero
  e_add := B.e_add
  e_star := B.e_star
  μ := MF.sigma_mu B t
  μ_one := MF.sigma_mu_one B t
  μ_mul := MF.sigma_mu_mul B t
  μ_isometry := MF.sigma_mu_isometry B t
  covar_right := MF.sigma_cov_right B t
  hecke_coprime := MF.sigma_hecke_coprime B t

/-- Strict Range Projection Invariance: σ_t(P_n) = P_n.
The gauge range projections are exact constants of motion under the modular Hamiltonian flow. -/
theorem sigma_P_invariance (t : ℝ) (n : ℕ+) :
    (MF.sigma_structure B t).P n = B.P n := by
  dsimp [sigma_structure, BostConnesStructure.P, sigma_mu]
  simp only [star_mul]
  calc MF.u t n * B.μ n * (star (B.μ n) * star (MF.u t n))
    _ = MF.u t n * (B.μ n * (star (B.μ n) * star (MF.u t n))) := by rw [mul_assoc]
    _ = MF.u t n * (B.μ n * star (B.μ n) * star (MF.u t n)) := by rw [← mul_assoc (B.μ n)]
    _ = MF.u t n * (star (MF.u t n) * (B.μ n * star (B.μ n))) := by
      rw [MF.star_central t n (B.μ n * star (B.μ n))]
    _ = (MF.u t n * star (MF.u t n)) * (B.μ n * star (B.μ n)) := by rw [← mul_assoc]
    _ = 1 * (B.μ n * star (B.μ n)) := by rw [MF.unitary_right t n]
    _ = B.μ n * star (B.μ n) := by rw [one_mul]

/-- Time zero action on isometries is the identity. -/
theorem sigma_zero_mu (n : ℕ+) : MF.sigma_mu B 0 n = B.μ n := by
  dsimp [sigma_mu]
  rw [MF.time_zero, one_mul]

/-- Time zero action on phase unitaries is the identity. -/
theorem sigma_zero_e (g : Γ) : MF.sigma_e B 0 g = B.e g := rfl

/-- Additivity / composition law of the modular flow on isometries. -/
theorem sigma_add_mu (s t : ℝ) (n : ℕ+) :
    MF.sigma_mu B (s + t) n = MF.u s n * MF.sigma_mu B t n := by
  dsimp [sigma_mu]
  rw [MF.time_add, mul_assoc]

/-- Inverse time evolution restores the original isometries. -/
theorem sigma_inverse_mu (t : ℝ) (n : ℕ+) :
    MF.u (-t) n * MF.sigma_mu B t n = B.μ n := by
  have h := MF.sigma_add_mu B (-t) t n
  rw [neg_add_cancel] at h
  rw [← h]
  exact MF.sigma_zero_mu B n

/-- Master synthesis theorem certifying the 8 core pillars of the Bost-Connes
1-parameter modular automorphism group and strict range projection invariance. -/
theorem bost_connes_modular_automorphism_synthesis (t s : ℝ) (n m : ℕ+) (g : Γ)
    (h_coprime : Nat.Coprime m.val n.val) :
    (MF.sigma_structure B t).P n = B.P n ∧
    star (MF.sigma_mu B t n) * MF.sigma_mu B t n = 1 ∧
    MF.sigma_mu B t (m * n) = MF.sigma_mu B t m * MF.sigma_mu B t n ∧
    star (MF.sigma_mu B t n) * MF.sigma_e B t g = MF.sigma_e B t ((n : ℕ) • g) * star (MF.sigma_mu B t n) ∧
    MF.sigma_e B t g * MF.sigma_mu B t n = MF.sigma_mu B t n * MF.sigma_e B t ((n : ℕ) • g) ∧
    star (MF.sigma_mu B t m) * MF.sigma_mu B t n = MF.sigma_mu B t n * star (MF.sigma_mu B t m) ∧
    MF.sigma_mu B 0 n = B.μ n ∧
    MF.sigma_mu B (s + t) n = MF.u s n * MF.sigma_mu B t n := by
  refine ⟨MF.sigma_P_invariance B t n,
          MF.sigma_mu_isometry B t n,
          MF.sigma_mu_mul B t m n,
          MF.sigma_cov_right B t n g,
          MF.sigma_cov_left B t n g,
          MF.sigma_hecke_coprime B t m n h_coprime,
          MF.sigma_zero_mu B n,
          MF.sigma_add_mu B s t n⟩

end ModularPhaseFlow

end InfoGeometry.Algebra.BostConnesModularAutomorphism
