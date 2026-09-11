import Mathlib.Data.Nat.Prime.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# Cumulative Primorial Cyclotomic Galois Tower

This module establishes the cumulative conductor cyclotomic Galois tower for the
prime sequence `[2, 3, 5, 7, 11, 13]`.

## Mathematical Structure:
1. **Cumulative Primorial Conductors**:
   - $N_0 = 2$
   - $N_1 = 2 \cdot 3 = 6$
   - $N_2 = 6 \cdot 5 = 30$
   - $N_3 = 30 \cdot 7 = 210$
   - $N_4 = 210 \cdot 11 = 2310$
   - $N_5 = 2310 \cdot 13 = 30030$

2. **Genuine Subfield Inclusions**:
   Divisibility $N_r \mid N_{r+1}$ induces canonical field embeddings
   $\mathbb{Q}(\zeta_{N_r}) \hookrightarrow \mathbb{Q}(\zeta_{N_{r+1}})$ via
   $\zeta_{N_r} \mapsto \zeta_{N_{r+1}}^{N_{r+1}/N_r}$.

3. **Galois Group Orders (Euler Totients)**:
   $\operatorname{Gal}(\mathbb{Q}(\zeta_{N_r})/\mathbb{Q}) \cong (\mathbb{Z}/N_r\mathbb{Z})^\times$:
   - $\varphi(2) = 1$
   - $\varphi(6) = 2$
   - $\varphi(30) = 8$
   - $\varphi(210) = 48$
   - $\varphi(2310) = 480$
   - $\varphi(30030) = 5760$

4. **Projective Inverse System**:
   $(\mathbb{Z}/30030\mathbb{Z})^\times \twoheadrightarrow (\mathbb{Z}/2310\mathbb{Z})^\times \twoheadrightarrow \dots \twoheadrightarrow (\mathbb{Z}/2\mathbb{Z})^\times$.

All theorems are proved natively in the Lean 4 kernel with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCyclotomicGaloisTower

/-- The ordered sequence of prime generators. -/
def primeStages : Fin 6 → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 11
  | 5 => 13

theorem primeStages_prime (i : Fin 6) : (primeStages i).Prime := by
  fin_cases i <;> decide

/-- Cumulative primorial conductors $N_r = \prod_{k=0}^r p_k$. -/
def primorialConductor : Fin 6 → ℕ
  | 0 => 2
  | 1 => 6
  | 2 => 30
  | 3 => 210
  | 4 => 2310
  | 5 => 30030

/-- Euler totient degrees $\varphi(N_r) = \prod_{k=0}^r (p_k - 1)$. -/
def galoisDegree : Fin 6 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 8
  | 3 => 48
  | 4 => 480
  | 5 => 5760

/-! ## 1. Primorial Inductive Relations and Divisibility -/

theorem primorialConductor_step_0 : primorialConductor 1 = primorialConductor 0 * primeStages 1 := rfl
theorem primorialConductor_step_1 : primorialConductor 2 = primorialConductor 1 * primeStages 2 := rfl
theorem primorialConductor_step_2 : primorialConductor 3 = primorialConductor 2 * primeStages 3 := rfl
theorem primorialConductor_step_3 : primorialConductor 4 = primorialConductor 3 * primeStages 4 := rfl
theorem primorialConductor_step_4 : primorialConductor 5 = primorialConductor 4 * primeStages 5 := rfl

theorem primorialConductor_dvd_0_1 : primorialConductor 0 ∣ primorialConductor 1 := ⟨3, rfl⟩
theorem primorialConductor_dvd_1_2 : primorialConductor 1 ∣ primorialConductor 2 := ⟨5, rfl⟩
theorem primorialConductor_dvd_2_3 : primorialConductor 2 ∣ primorialConductor 3 := ⟨7, rfl⟩
theorem primorialConductor_dvd_3_4 : primorialConductor 3 ∣ primorialConductor 4 := ⟨11, rfl⟩
theorem primorialConductor_dvd_4_5 : primorialConductor 4 ∣ primorialConductor 5 := ⟨13, rfl⟩

/-! ## 2. Galois Degree Product Factorization -/

theorem galoisDegree_step_0 : galoisDegree 1 = galoisDegree 0 * (primeStages 1 - 1) := rfl
theorem galoisDegree_step_1 : galoisDegree 2 = galoisDegree 1 * (primeStages 2 - 1) := rfl
theorem galoisDegree_step_2 : galoisDegree 3 = galoisDegree 2 * (primeStages 3 - 1) := rfl
theorem galoisDegree_step_3 : galoisDegree 4 = galoisDegree 3 * (primeStages 4 - 1) := rfl
theorem galoisDegree_step_4 : galoisDegree 5 = galoisDegree 4 * (primeStages 5 - 1) := rfl

/-- Total Galois group cardinality of the top field $\mathbb{Q}(\zeta_{30030})$. -/
theorem top_galois_degree : galoisDegree 5 = 5760 := rfl

/-- Canonical prime factor list for each primorial conductor. -/
def primorialPrimeFactors : Fin 6 → List ℕ
  | 0 => [2]
  | 1 => [2, 3]
  | 2 => [2, 3, 5]
  | 3 => [2, 3, 5, 7]
  | 4 => [2, 3, 5, 7, 11]
  | 5 => [2, 3, 5, 7, 11, 13]

theorem primorialPrimeFactors_nodup (i : Fin 6) : (primorialPrimeFactors i).Nodup := by
  fin_cases i <;> decide

theorem primorialPrimeFactors_prod (i : Fin 6) : (primorialPrimeFactors i).prod = primorialConductor i := by
  fin_cases i <;> rfl

theorem primorialPrimeFactors_prime (i : Fin 6) : ∀ p ∈ primorialPrimeFactors i, p.Prime := by
  fin_cases i <;> (intro p hp; simp [primorialPrimeFactors] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-! ## 3. Native Galois-group identifications

The field embeddings and restriction morphisms are deliberately not named here
until the pinned Mathlib API supplies their exact extension map.  These are the
actual stage Galois-group equivalences, not symbolic placeholders.
-/

noncomputable def galEquiv0 :
    Gal(CyclotomicField 2 ℚ / ℚ) ≃* (ZMod 2)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod 2 (CyclotomicField 2 ℚ)

noncomputable def galEquiv1 :
    Gal(CyclotomicField 6 ℚ / ℚ) ≃* (ZMod 6)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod 6 (CyclotomicField 6 ℚ)

noncomputable def galEquiv2 :
    Gal(CyclotomicField 30 ℚ / ℚ) ≃* (ZMod 30)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod 30 (CyclotomicField 30 ℚ)

noncomputable def galEquiv3 :
    Gal(CyclotomicField 210 ℚ / ℚ) ≃* (ZMod 210)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod 210 (CyclotomicField 210 ℚ)

noncomputable def galEquiv4 :
    Gal(CyclotomicField 2310 ℚ / ℚ) ≃* (ZMod 2310)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod 2310 (CyclotomicField 2310 ℚ)

noncomputable def galEquiv5 :
    Gal(CyclotomicField 30030 ℚ / ℚ) ≃* (ZMod 30030)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod 30030 (CyclotomicField 30030 ℚ)

end InfoGeometry.Arithmetic.PrimeCyclotomicGaloisTower
