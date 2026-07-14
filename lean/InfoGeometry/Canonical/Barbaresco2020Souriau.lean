import Mathlib
import InfoGeometry.Canonical.SouriauCasimirInvariant
import InfoGeometry.Canonical.SouriauFenchelOnsagerBridge

/-!
# Barbaresco 2020: finite Souriau representation spine

Source digest:

Frederic Barbaresco, "Lie Group Statistics and Lie Group Machine Learning
Based on Souriau Lie Groups Thermodynamics & Koszul-Souriau-Fisher Metric",
Entropy 22(6), 642, 2020.

The paper's formalizable finite algebraic core is:

* the `SU(1,1)` / `SL(2,R)` null-cohomology example, represented here by
  the real `sl2` matrices and the equivalent `so(2,1)` Lorentz algebra;
* the Poincare-disk moment map landing on the two-sheeted hyperboloid;
* the `SE(2)` non-null-cohomology example, represented by strict homogeneous
  `3 x 3` matrices and its Lie algebra brackets; and
* Souriau's affine coadjoint action law, delegated to the repository owner
  `SouriauCasimirInvariant`.

This file intentionally does not formalize the analytic orbit method,
Laplace-transform convergence, or smooth Gibbs-density theory.  The external
SymPy/Sage/GAP/Clifford certificates in `tools/` check the same finite matrix
spine; Lean owns only the kernel-checked algebra below.
-/

noncomputable section

set_option linter.unnecessarySeqFocus false

namespace Barbaresco2020Souriau

open InfoGeometry.Canonical.SouriauCasimirInvariant
open InfoGeometry.Canonical.SouriauFenchelOnsagerBridge

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) ℝ

def comm2 (A B : Mat2) : Mat2 :=
  A * B - B * A

def comm3 (A B : Mat3) : Mat3 :=
  A * B - B * A

/-! ## `sl2` / `su(1,1)` finite matrix algebra -/

def sl2H : Mat2 := !![(1 : ℝ), 0; 0, -1]
def sl2E : Mat2 := !![(0 : ℝ), 1; 0, 0]
def sl2F : Mat2 := !![(0 : ℝ), 0; 1, 0]

theorem sl2_H_E :
    comm2 sl2H sl2E = (2 : ℝ) • sl2E := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm2, sl2H, sl2E] <;> norm_num

theorem sl2_H_F :
    comm2 sl2H sl2F = (-2 : ℝ) • sl2F := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm2, sl2H, sl2F] <;> norm_num

theorem sl2_E_F :
    comm2 sl2E sl2F = sl2H := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm2, sl2E, sl2F, sl2H]

/-! ## `so(2,1)` coadjoint/Lorentz representation -/

def eta21 : Mat3 :=
  !![(1 : ℝ), 0, 0;
     0, -1, 0;
     0, 0, -1]

def so21J : Mat3 :=
  !![(0 : ℝ), 0, 0;
     0, 0, -1;
     0, 1, 0]

def so21Kx : Mat3 :=
  !![(0 : ℝ), 1, 0;
     1, 0, 0;
     0, 0, 0]

def so21Ky : Mat3 :=
  !![(0 : ℝ), 0, 1;
     0, 0, 0;
     1, 0, 0]

theorem so21J_lorentz_infinitesimal :
    so21J.transpose * eta21 + eta21 * so21J = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [so21J, eta21, Matrix.mul_apply, Fin.sum_univ_three]

theorem so21Kx_lorentz_infinitesimal :
    so21Kx.transpose * eta21 + eta21 * so21Kx = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [so21Kx, eta21, Matrix.mul_apply, Fin.sum_univ_three]

theorem so21Ky_lorentz_infinitesimal :
    so21Ky.transpose * eta21 + eta21 * so21Ky = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [so21Ky, eta21, Matrix.mul_apply, Fin.sum_univ_three]

theorem so21_J_Kx :
    comm3 so21J so21Kx = so21Ky := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm3, so21J, so21Kx, so21Ky]

theorem so21_J_Ky :
    comm3 so21J so21Ky = -so21Kx := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm3, so21J, so21Ky, so21Kx]

theorem so21_Kx_Ky :
    comm3 so21Kx so21Ky = -so21J := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm3, so21Kx, so21Ky, so21J]

/--
Polynomially cleared Poincare-disk moment-map identity.

With `r2 = u^2 + v^2`, the numerator of

`J0 = rho (1+r2)/(1-r2), J1 = 2 rho u/(1-r2), J2 = 2 rho v/(1-r2)`

satisfies the `SO(2,1)` hyperboloid equation after clearing denominators.
-/
theorem su11_disk_moment_map_hyperboloid_cleared
    (rho u v : ℝ) :
    (rho * (1 + (u * u + v * v))) ^ 2
      - (2 * rho * u) ^ 2
      - (2 * rho * v) ^ 2
      =
    rho ^ 2 * (1 - (u * u + v * v)) ^ 2 := by
  ring

/-! ## `SE(2)` strict homogeneous matrix representation -/

def se2GroupMatrix (c s tx ty : ℝ) : Mat3 :=
  !![c, -s, tx;
     s, c, ty;
     0, 0, 1]

theorem se2GroupMatrix_mul
    (c₁ s₁ tx₁ ty₁ c₂ s₂ tx₂ ty₂ : ℝ) :
    se2GroupMatrix c₁ s₁ tx₁ ty₁ * se2GroupMatrix c₂ s₂ tx₂ ty₂ =
      se2GroupMatrix
        (c₁ * c₂ - s₁ * s₂)
        (s₁ * c₂ + c₁ * s₂)
        (c₁ * tx₂ - s₁ * ty₂ + tx₁)
        (s₁ * tx₂ + c₁ * ty₂ + ty₁) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [se2GroupMatrix] <;> ring

def se2LieMatrix (omega vx vy : ℝ) : Mat3 :=
  !![0, -omega, vx;
     omega, 0, vy;
     0, 0, 0]

def se2J : Mat3 := se2LieMatrix 1 0 0
def se2P1 : Mat3 := se2LieMatrix 0 1 0
def se2P2 : Mat3 := se2LieMatrix 0 0 1

theorem se2_J_P1 :
    comm3 se2J se2P1 = se2P2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm3, se2J, se2P1, se2P2, se2LieMatrix]

theorem se2_J_P2 :
    comm3 se2J se2P2 = -se2P1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm3, se2J, se2P2, se2P1, se2LieMatrix]

theorem se2_P1_P2 :
    comm3 se2P1 se2P2 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [comm3, se2P1, se2P2, se2LieMatrix]

/-- The `SE(2)` coadjoint momentum norm is invariant under the rotation block. -/
theorem se2_momentum_norm_rotation_invariant
    (c s mx my : ℝ)
    (hrot : c ^ 2 + s ^ 2 = 1) :
    (c * mx - s * my) ^ 2 + (s * mx + c * my) ^ 2 =
      mx ^ 2 + my ^ 2 := by
  nlinarith [sq_nonneg (s * mx - c * my), hrot]

/-! ## Souriau affine coadjoint action owner readback -/

def IsCasimirInvariant
    {G Q : Type*} [Group G]
    (act : G → Q → Q) (S : Q → ℝ) : Prop :=
  ∀ g Q, S (act g Q) = S Q

theorem souriau_affineCoAd_is_action
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_mul :
      ∀ g h : G,
        coAd (g * h) = (coAd g).comp (coAd h))
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g h : G) (Q : LieDual) :
    affineCoAd coAd theta (g * h) Q =
      affineCoAd coAd theta g (affineCoAd coAd theta h Q) :=
  affineCoAd_mul coAd theta hcoAd_mul htheta_mul g h Q

theorem entropy_is_casimir_under_affine_coadjoint_action
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (entropy : LieDual → ℝ)
    (hentropy :
      ∀ g Q, entropy (affineCoAd coAd theta g Q) = entropy Q) :
    IsCasimirInvariant (affineCoAd coAd theta) entropy :=
  hentropy

end Barbaresco2020Souriau
