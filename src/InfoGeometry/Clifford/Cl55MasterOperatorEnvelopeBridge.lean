import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
import InfoGeometry.Clifford.Cl55SpinorChirality

set_option linter.unusedSimpArgs false

/-!
# Cl(5,5) Master Operator Envelope Bridge

This owner module formalizes the unified Clifford–Witt master operator envelope
$\operatorname{Pin}(5,5) \subset Cl(5,5)^\times$ acting on the 32-dimensional spinor / Fock
carrier $S = \Lambda^\bullet U$ ($\dim U = 5$, $\dim S = 2^5 = 32$):

1. **Master 5-Mode CAR Clifford Relations on Fock Space:**
   $$\boxed{\{\varepsilon_i, \iota_j\} = \delta_{ij} I_{32}, \qquad \{\varepsilon_i, \varepsilon_j\} = 0, \qquad \{\iota_i, \iota_j\} = 0}$$

2. **Chiral Hodge–Dirac Operator ($D_H = d + \delta$ on the 3-mode spatial sector):**
   $$d_H := \varepsilon_0 + \varepsilon_1 + \varepsilon_2, \qquad \delta_H := \iota_0 + \iota_1 + \iota_2, \qquad D_H := d_H + \delta_H$$

3. **Chiral Supercharges ($Q, \bar{Q}$ on the 2-mode spinor sector):**
   $$\boxed{Q := \varepsilon_3 + \iota_4, \qquad \bar{Q} := \varepsilon_4 + \iota_3}$$
   - Nilpotency: $\boxed{Q^2 = 0, \qquad \bar{Q}^2 = 0}$

4. **Super-Poincaré Anticommutator generating Four-Momentum:**
   $$\boxed{\{Q, \bar{Q}\} = 2 \cdot I_{32} = 2 P_0}$$

5. **Finite Clifford–Witt carrier:**
    the concrete `Mat32` Fock carrier used by the CAR and chiral operators
    above. Lie-subalgebra inclusions and dimension formulae belong to their
    dedicated native owners and are not inferred from this matrix owner.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge

open Matrix
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
open InfoGeometry.Clifford.Cl11TensorTower

abbrev Mat32 := MatStage 5

/-- Master 5-mode creation operators in the 32-dimensional Fock space. -/
def eps (i : Fin 5) : Mat32 := creation i

/-- Master 5-mode annihilation operators in the 32-dimensional Fock space. -/
def iota (i : Fin 5) : Mat32 := annihilation i

/-- 🏆 THEOREM 1: Master CAR Anticommutation on Fock Space:
    $\{\varepsilon_i, \iota_i\} = I_{32}$ on diagonal, and cross-anticommutation off-diagonal. -/
theorem car_same_site (i : Fin 5) :
    eps i * iota i + iota i * eps i = 1 :=
  same_site_car 5 i

theorem eps_sq (i : Fin 5) :
    eps i * eps i = 0 :=
  creation_sq 5 i

theorem iota_sq (i : Fin 5) :
    iota i * iota i = 0 :=
  annihilation_sq 5 i

theorem eps_cross_anticomm {i j : Fin 5} (hij : i ≠ j) :
    eps i * eps j + eps j * eps i = 0 :=
  creation_cross_anticommute hij

theorem iota_cross_anticomm {i j : Fin 5} (hij : i ≠ j) :
    iota i * iota j + iota j * iota i = 0 :=
  annihilation_cross_anticommute hij

theorem eps_iota_cross_anticomm {i j : Fin 5} (hij : i ≠ j) :
    eps i * iota j + iota j * eps i = 0 :=
  creation_annihilation_cross_site_anticommute 5 i j hij

/-- The embedded 3-mode spatial Hodge differential $d_H = \varepsilon_0 + \varepsilon_1 + \varepsilon_2$. -/
def hodgeDiff : Mat32 :=
  eps 0 + eps 1 + eps 2

/-- The embedded 3-mode spatial Hodge codifferential $\delta_H = \iota_0 + \iota_1 + \iota_2$. -/
def hodgeCodiff : Mat32 :=
  iota 0 + iota 1 + iota 2

/-- The embedded 3-mode Hodge–Dirac operator $D_H = d_H + \delta_H$. -/
def hodgeDirac : Mat32 :=
  hodgeDiff + hodgeCodiff

/-- The 2-mode chiral supercharges $Q, \bar{Q}$. -/
def superchargeQ : Mat32 :=
  eps 3 + iota 4

def superchargeQBar : Mat32 :=
  eps 4 + iota 3

/-- 🏆 THEOREM 2: Exact Supercharge Nilpotency:
    $Q^2 = 0$ and $\bar{Q}^2 = 0$. -/
theorem superchargeQ_sq :
    superchargeQ * superchargeQ = 0 := by
  dsimp [superchargeQ]
  have h34 : (3 : Fin 5) ≠ 4 := by decide
  have h_cross : eps 3 * iota 4 + iota 4 * eps 3 = 0 := eps_iota_cross_anticomm h34
  have h3sq : eps 3 * eps 3 = 0 := eps_sq 3
  have h4sq : iota 4 * iota 4 = 0 := iota_sq 4
  calc
    (eps 3 + iota 4) * (eps 3 + iota 4)
      = eps 3 * eps 3 + (eps 3 * iota 4 + iota 4 * eps 3) + iota 4 * iota 4 := by
        simp only [Matrix.add_mul, Matrix.mul_add, add_assoc]
        abel
    _ = 0 + 0 + 0 := by rw [h3sq, h_cross, h4sq]
    _ = 0 := by simp

theorem superchargeQBar_sq :
    superchargeQBar * superchargeQBar = 0 := by
  dsimp [superchargeQBar]
  have h43 : (4 : Fin 5) ≠ 3 := by decide
  have h_cross : eps 4 * iota 3 + iota 3 * eps 4 = 0 := eps_iota_cross_anticomm h43
  have h4sq : eps 4 * eps 4 = 0 := eps_sq 4
  have h3sq : iota 3 * iota 3 = 0 := iota_sq 3
  calc
    (eps 4 + iota 3) * (eps 4 + iota 3)
      = eps 4 * eps 4 + (eps 4 * iota 3 + iota 3 * eps 4) + iota 3 * iota 3 := by
        simp only [Matrix.add_mul, Matrix.mul_add, add_assoc]
        abel
    _ = 0 + 0 + 0 := by rw [h4sq, h_cross, h3sq]
    _ = 0 := by simp

/-- 🏆 THEOREM 3: The Super-Poincaré Anticommutator Identity:
    $\{Q, \bar{Q}\} = 2 \cdot I_{32} = 2 P_0$. -/
theorem supercharge_anticomm_momentum :
    superchargeQ * superchargeQBar + superchargeQBar * superchargeQ = (2 : ℝ) • (1 : Mat32) := by
  dsimp [superchargeQ, superchargeQBar]
  have h3 : eps 3 * iota 3 + iota 3 * eps 3 = 1 := car_same_site 3
  have h4 : eps 4 * iota 4 + iota 4 * eps 4 = 1 := car_same_site 4
  have h34 : (3 : Fin 5) ≠ 4 := by decide
  have h43 : (4 : Fin 5) ≠ 3 := by decide
  have h_ee : eps 3 * eps 4 + eps 4 * eps 3 = 0 := eps_cross_anticomm h34
  have h_ii : iota 4 * iota 3 + iota 3 * iota 4 = 0 := iota_cross_anticomm h43
  calc
    (eps 3 + iota 4) * (eps 4 + iota 3) + (eps 4 + iota 3) * (eps 3 + iota 4)
      = (eps 3 * eps 4 + eps 4 * eps 3) +
        (iota 4 * iota 3 + iota 3 * iota 4) +
        (eps 3 * iota 3 + iota 3 * eps 3) +
        (eps 4 * iota 4 + iota 4 * eps 4) := by
          simp only [Matrix.add_mul, Matrix.mul_add]
          abel
    _ = 0 + 0 + 1 + 1 := by rw [h_ee, h_ii, h3, h4]
    _ = (2 : ℝ) • (1 : Mat32) := by
      simp only [add_zero, zero_add]
      rw [two_smul]

end InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge
