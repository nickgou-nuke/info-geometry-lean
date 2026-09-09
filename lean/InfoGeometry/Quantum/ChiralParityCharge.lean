/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.ChiralParityCharge

open Real

noncomputable section

/-!
# Chiral Parity Charge, Ladder Operators & Equatorial Balance

This module formalizes:
1. **Chiral Ladder & Number Operators**:
   - Left-moving number operator: $N_L = a_L^\dagger a_L + f_L^\dagger f_L$
   - Right-moving number operator: $N_R = a_R^\dagger a_R + f_R^\dagger f_R$
   - Total particle number: $N_{\mathrm{tot}} = N_L + N_R$
2. **Chiral Parity / Axial Charge ($Q_5$)**:
   - $Q_5 = N_L - N_R$
3. **Parity Inversion Symmetry ($\mathcal{P}$)**:
   - Swapping sectors: $\mathcal{P}(N_L, N_R) = (N_R, N_L)$
   - Parity oddness: $Q_5(N_R, N_L) = - Q_5(N_L, N_R)$
4. **Chiral Equilibrium ($Q_5 = 0$)**:
   - Parity invariance $\implies N_L = N_R$ and $Q_5 = 0$.
5. **Critical Line Confinement ($\sigma = 1/2$)**:
   - Mapping $Q_5 = \sigma - 1/2$, the vanishing of chiral charge $Q_5 = 0$
     strictly confines the state to the critical line $\sigma = 1/2$.
-/

variable {R : Type*} [CommRing R]

/-- Left-moving chiral number operator from bosonic and fermionic modes -/
def numberL (a_L_dag a_L f_L_dag f_L : R) : R :=
  a_L_dag * a_L + f_L_dag * f_L

/-- Right-moving chiral number operator from bosonic and fermionic modes -/
def numberR (a_R_dag a_R f_R_dag f_R : R) : R :=
  a_R_dag * a_R + f_R_dag * f_R

/-- Total particle number operator -/
def totalNumber (N_L N_R : R) : R :=
  N_L + N_R

/-- Chiral parity charge (axial charge Q₅) -/
def chiralParityCharge (N_L N_R : R) : R :=
  N_L - N_R

/-- Parity reflection operator swapping left and right sectors -/
def parityReflect (p : R × R) : R × R :=
  (p.2, p.1)

/-- 🏆 THEOREM 1: Chiral Parity Charge Decomposition into Bosonic and Fermionic Sectors -/
theorem chiral_parity_charge_decomp (a_L_dag a_L f_L_dag f_L a_R_dag a_R f_R_dag f_R : R) :
    chiralParityCharge (numberL a_L_dag a_L f_L_dag f_L) (numberR a_R_dag a_R f_R_dag f_R) =
    (a_L_dag * a_L - a_R_dag * a_R) + (f_L_dag * f_L - f_R_dag * f_R) := by
  unfold chiralParityCharge numberL numberR
  ring

/-- 🏆 THEOREM 2: Parity Oddness of the Chiral Charge: Q₅(N_R, N_L) = - Q₅(N_L, N_R) -/
theorem chiral_charge_parity_odd (N_L N_R : R) :
    chiralParityCharge N_R N_L = - chiralParityCharge N_L N_R := by
  unfold chiralParityCharge
  ring

/-- 🏆 THEOREM 3: Vanishing of Chiral Charge in Parity Invariant States -/
theorem chiral_charge_eq_zero_of_equal_modes (N_L N_R : R) (h_eq : N_L = N_R) :
    chiralParityCharge N_L N_R = 0 := by
  unfold chiralParityCharge
  rw [h_eq]
  ring

/-- 🏆 THEOREM 4: Equality of Chiral Sectors from Vanishing Chiral Charge -/
theorem equal_modes_of_chiral_charge_zero (N_L N_R : R) (h_zero : chiralParityCharge N_L N_R = 0) :
    N_L = N_R := by
  unfold chiralParityCharge at h_zero
  exact sub_eq_zero.mp h_zero

/-- 🏆 THEOREM 5: Critical Line Confinement from Chiral Charge Annihilation -/
theorem critical_line_from_chiral_balance (σ : ℝ)
    (h_chiral : chiralParityCharge σ (1 / 2) = 0) :
    σ = 1 / 2 :=
  equal_modes_of_chiral_charge_zero σ (1 / 2) h_chiral

end

end InfoGeometry.Quantum.ChiralParityCharge
