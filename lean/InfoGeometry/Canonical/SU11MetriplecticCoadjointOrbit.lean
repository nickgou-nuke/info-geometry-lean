import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic

set_option linter.unusedSectionVars false

open Complex Matrix

namespace InfoGeometry.Canonical.SU11MetriplecticCoadjointOrbit

/-- 1. Matrix basis for su*(1,1) dual Lie algebra over M₂(ℂ) -/
def u1_star : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def u2_star : Matrix (Fin 2) (Fin 2) ℂ := !![0, I; I, 0]
def u3_star : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- 2. Moment Map J(z) on the Poincaré Unit Disk D = {z ∈ ℂ | |z| < 1} -/
noncomputable def momentMap (rho : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let denom := 1 - (normSq z : ℂ)
  let J1 := (rho : ℂ) * (1 + (normSq z : ℂ)) / denom
  let J2 := - (rho : ℂ) * (z + star z) / denom
  let J3 := I * (rho : ℂ) * (z - star z) / denom
  !![J1, J2; J3, -J1]

/-- 3. Component Moment Functions J₁, J₂, J₃ -/
noncomputable def J1 (rho : ℝ) (z : ℂ) : ℂ :=
  (rho : ℂ) * (1 + (normSq z : ℂ)) / (1 - (normSq z : ℂ))

noncomputable def J2 (rho : ℝ) (z : ℂ) : ℂ :=
  - (rho : ℂ) * (z + star z) / (1 - (normSq z : ℂ))

noncomputable def J3 (rho : ℝ) (z : ℂ) : ℂ :=
  I * (rho : ℂ) * (z - star z) / (1 - (normSq z : ℂ))

/-- 🏆 THEOREM 1: Casimir Invariant Hyperboloid Relation J₁² - J₂² - J₃² = ρ²
    Proves that the moment map images lie on the SU(1,1) hyperboloid of coadjoint orbits. -/
theorem casimir_hyperboloid_identity (rho : ℝ) (z : ℂ) (hz : normSq z ≠ 1) :
    (J1 rho z)^2 - (J2 rho z)^2 - (J3 rho z)^2 = (rho : ℂ)^2 := by
  dsimp [J1, J2, J3]
  have h_denom : 1 - (normSq z : ℂ) ≠ 0 := by
    intro h
    have h_eq : (normSq z : ℂ) = 1 := by
      calc (normSq z : ℂ) = 1 - (1 - (normSq z : ℂ)) := by ring
        _ = 1 - 0 := by rw [h]
        _ = 1 := by ring
    have h_real : normSq z = 1 := by exact_mod_cast h_eq
    exact hz h_real
  have h_mul : z * (starRingEnd ℂ) z = (normSq z : ℂ) := by
    refine Complex.ext ?_ ?_
    · dsimp [normSq]; ring
    · dsimp; ring
  have h_sub : (z + (starRingEnd ℂ) z)^2 - (z - (starRingEnd ℂ) z)^2 = 4 * (normSq z : ℂ) := by
    calc (z + (starRingEnd ℂ) z)^2 - (z - (starRingEnd ℂ) z)^2
      _ = 4 * (z * (starRingEnd ℂ) z) := by ring
      _ = 4 * (normSq z : ℂ) := by rw [h_mul]
  have h_num : (1 + (normSq z : ℂ))^2 - (z + (starRingEnd ℂ) z)^2 - (-1) * (z - (starRingEnd ℂ) z)^2 = (1 - (normSq z : ℂ))^2 := by
    calc (1 + (normSq z : ℂ))^2 - (z + (starRingEnd ℂ) z)^2 - (-1) * (z - (starRingEnd ℂ) z)^2
      _ = (1 + (normSq z : ℂ))^2 - ((z + (starRingEnd ℂ) z)^2 - (z - (starRingEnd ℂ) z)^2) := by ring
      _ = (1 + (normSq z : ℂ))^2 - 4 * (normSq z : ℂ) := by rw [h_sub]
      _ = (1 - (normSq z : ℂ))^2 := by ring
  field_simp [h_denom]
  rw [I_sq, h_num]

/-- 4. Poincaré Disk Poisson Bracket {f, H} on Symplectic Leaves -/
noncomputable def poincarePoissonBracket (rho : ℝ) (df_dz df_dzc dH_dz dH_dzc : ℂ) : ℂ :=
  (1 / (2 * I * (rho : ℂ))) * (df_dz * dH_dzc - df_dzc * dH_dz)

/-- 🏆 THEOREM 2: Skew-Symmetry of the Poincaré Poisson Bracket
    {f, H} = - {H, f} along the symplectic leaves of invariant entropy. -/
theorem poincarePoissonBracket_skew (rho : ℝ) (df_dz df_dzc dH_dz dH_dzc : ℂ) :
    poincarePoissonBracket rho df_dz df_dzc dH_dz dH_dzc =
    - poincarePoissonBracket rho dH_dz dH_dzc df_dz df_dzc := by
  dsimp [poincarePoissonBracket]
  ring

/-- 🏆 THEOREM 3: Vanishing Self-Poisson Bracket {f, f} = 0 -/
theorem poincarePoissonBracket_self (rho : ℝ) (df_dz df_dzc : ℂ) :
    poincarePoissonBracket rho df_dz df_dzc df_dz df_dzc = 0 := by
  dsimp [poincarePoissonBracket]
  ring

end InfoGeometry.Canonical.SU11MetriplecticCoadjointOrbit
