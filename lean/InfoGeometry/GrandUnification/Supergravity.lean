/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.FiniteInductiveSUSY
import InfoGeometry.Algebra.FiniteSUSYBlocks
import InfoGeometry.Algebra.CuntzSupergradedSUSY
import InfoGeometry.Topology.KANWallpaperIsomorphism
import InfoGeometry.Topology.KANWallpaperSuperchargeReadout
import InfoGeometry.Quantum.PoincareSupercharge

/-!
# Crystallographic Supergravity & N=1 / N=2 Supersymmetry Closure

Unifies the crystallographic glide-reflection to supersymmetry algebraic closure
(`G^2 = T_x => {Q, Q} = 2 P` and `[Q, P] = 0`) across:

1. Arbitrary associative rings via `CrystallographicSUSYDatum` and ring-homomorphism transport;
2. The concrete `3 × 3` projective `pg` wallpaper realization (`KANWallpaper.G`, `KANWallpaper.T_x`,
   nilpotent horizon `n = T_x - 1`, and non-commuting vertical translation `T_y`);
3. Finite partner-block SUSY closures (`FiniteSUSY.FiniteSUSYSystem` with `Q = A + A†`);
4. An explicit non-commutative `4 × 4` complex `N = 2` Clifford-SUSY algebra (`{Qᵢ, Qⱼ} = 2 δᵢⱼ P₄`,
   `Q₁ * Q₂ ≠ Q₂ * Q₁`, and nilpotent chiral combinations `Q₊² = Q₋² = 0`, `{Q₊, Q₋} = P₄`);
5. Compatibility with the Cuntz quotient supercharge (`SupergradedSUSY`) and Pauli rest-frame
   super-Poincaré anticommutator (`PoincareSupercharge`).
-/

noncomputable section

namespace InfoGeometry.GrandUnification.Supergravity

open Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Algebra.FiniteInductiveSUSY
open InfoGeometry.Algebra.FiniteSUSY
open InfoGeometry.Topology.KANWallpaperSuperchargeReadout
open InfoGeometry.Canonical.PauliHestenesSpinMomentum

/-! ## 1. Universal Associative Crystallographic SUSY Closure -/

/-- A crystallographic SUSY datum in an arbitrary associative ring `B`:
    an odd generator `Q` whose square equals an even momentum generator `P`. -/
structure CrystallographicSUSYDatum (B : Type*) [Ring B] where
  Q : B
  P : B
  sq_eq : Q * Q = P

/-- Constructive `Inhabited` instance for any ring `B` (zero supercharge/momentum). -/
instance instInhabitedCrystallographicSUSYDatum (B : Type*) [Ring B] :
    Inhabited (CrystallographicSUSYDatum B) :=
  ⟨⟨0, 0, mul_zero 0⟩⟩

namespace CrystallographicSUSYDatum

variable {B : Type*} [Ring B] (S : CrystallographicSUSYDatum B)

/-- Universal `N = 1` SUSY closure `{Q, Q} = 2 • P` (additive `ℕ`-smul). -/
theorem anticomm_eq_two_nsmul :
    anticomm S.Q S.Q = (2 : ℕ) • S.P := by
  rw [anticomm, S.sq_eq, two_nsmul]

/-- Scalar `ℝ`-module form `{Q, Q} = (2 : ℝ) • P`. -/
theorem anticomm_eq_two_smul [Module ℝ B] :
    anticomm S.Q S.Q = (2 : ℝ) • S.P := by
  rw [anticomm, S.sq_eq, two_smul]

/-- Complex `ℂ`-module form `{Q, Q} = (2 : ℂ) • P`. -/
theorem anticomm_eq_two_smul_complex [Module ℂ B] :
    anticomm S.Q S.Q = (2 : ℂ) • S.P := by
  rw [anticomm, S.sq_eq, two_smul]

/-- The supercharge commutes with its generated momentum: `Q * P = P * Q`. -/
theorem comm_Q_P : S.Q * S.P = S.P * S.Q := by
  calc
    S.Q * S.P = S.Q * (S.Q * S.Q) := by rw [S.sq_eq]
    _ = (S.Q * S.Q) * S.Q := (mul_assoc S.Q S.Q S.Q).symm
    _ = S.P * S.Q := by rw [S.sq_eq]

/-- Vanishing commutator `[Q, P] = 0`. -/
theorem comm_Q_P_eq_zero : S.Q * S.P - S.P * S.Q = 0 := by
  rw [S.comm_Q_P, sub_self]

/-- Ring-homomorphism transport of a `CrystallographicSUSYDatum`. -/
def map {C : Type*} [Ring C] (φ : B →+* C) (S : CrystallographicSUSYDatum B) :
    CrystallographicSUSYDatum C where
  Q := φ S.Q
  P := φ S.P
  sq_eq := by rw [← map_mul, S.sq_eq]

/-- Ring homomorphisms preserve the SUSY anticommutator closure `{φ Q, φ Q} = 2 • φ P`. -/
theorem map_anticomm_eq_two_nsmul {C : Type*} [Ring C] (φ : B →+* C) :
    anticomm (S.map φ).Q (S.map φ).Q = (2 : ℕ) • (S.map φ).P := by
  calc
    anticomm (S.map φ).Q (S.map φ).Q = φ (anticomm S.Q S.Q) :=
      (InfoGeometry.Algebra.FiniteInductiveSUSY.map_anticomm φ S.Q S.Q).symm
    _ = φ ((2 : ℕ) • S.P) := by rw [S.anticomm_eq_two_nsmul]
    _ = (2 : ℕ) • (S.map φ).P := map_nsmul φ 2 S.P

end CrystallographicSUSYDatum

/-! ## 2. Concrete KAN Wallpaper Supergravity Model (`Matrix (Fin 3) (Fin 3) ℝ`) -/

/-- Constructive inhabitant of `CrystallographicSUSYDatum KANWallpaper.ProjMatrix`
    realizing the `pg` wallpaper glide `G` and translation `T_x`. -/
def wallpaperSUSYModel :
    CrystallographicSUSYDatum InfoGeometry.Topology.KANWallpaper.ProjMatrix where
  Q := InfoGeometry.Topology.KANWallpaper.G
  P := InfoGeometry.Topology.KANWallpaper.T_x
  sq_eq := InfoGeometry.Topology.KANWallpaper.glide_squared_is_translation

/-- The glide supercharge generates twice the translation momentum (`2 • P`). -/
theorem wallpaper_generates_SUSY_nsmul :
    anticomm wallpaperSUSYModel.Q wallpaperSUSYModel.Q =
      (2 : ℕ) • wallpaperSUSYModel.P :=
  glide_self_anticomm_eq_two_nsmul_translation

/-- Real-scalar form `{Q, Q} = (2 : ℝ) • P` in the concrete `3 × 3` projective model. -/
theorem wallpaper_generates_SUSY :
    wallpaperSUSYModel.Q * wallpaperSUSYModel.Q + wallpaperSUSYModel.Q * wallpaperSUSYModel.Q =
      (2 : ℝ) • wallpaperSUSYModel.P :=
  wallpaperSUSYModel.anticomm_eq_two_smul

/-- Supercharge–momentum commutation `[Q, P] = 0` in the wallpaper model. -/
theorem wallpaper_Q_comm_P :
    wallpaperSUSYModel.Q * wallpaperSUSYModel.P =
      wallpaperSUSYModel.P * wallpaperSUSYModel.Q :=
  wallpaperSUSYModel.comm_Q_P

/-- Compatibility with `SupergradedSUSY.superAnticommutator`. -/
theorem wallpaper_matches_supergradedSUSY :
    InfoGeometry.Algebra.SupergradedSUSY.superAnticommutator
        InfoGeometry.Algebra.SupergradedSUSY.Q
        InfoGeometry.Algebra.SupergradedSUSY.Q =
      (2 : ℝ) • InfoGeometry.Algebra.SupergradedSUSY.P_x :=
  InfoGeometry.Algebra.SupergradedSUSY.susy_anticommutator_generates_two_smul_momentum

/-- Horizon decomposition `Q^2 = 1 + n` with nilpotent `n = T_x - 1` (`n^2 = 0`). -/
theorem wallpaper_horizon_decomposition :
    wallpaperSUSYModel.Q * wallpaperSUSYModel.Q =
        1 + InfoGeometry.Topology.KANWallpaper.n ∧
      InfoGeometry.Topology.KANWallpaper.n * InfoGeometry.Topology.KANWallpaper.n = 0 ∧
      wallpaperSUSYModel.Q * InfoGeometry.Topology.KANWallpaper.n =
        InfoGeometry.Topology.KANWallpaper.n * wallpaperSUSYModel.Q := by
  refine ⟨?_, InfoGeometry.Topology.KANWallpaper.translation_is_nilpotent_horizon, ?_⟩
  · change InfoGeometry.Topology.KANWallpaper.G * InfoGeometry.Topology.KANWallpaper.G =
      1 + (InfoGeometry.Topology.KANWallpaper.T_x - 1)
    rw [InfoGeometry.Topology.KANWallpaper.glide_squared_is_translation]
    abel
  · change InfoGeometry.Topology.KANWallpaper.G *
        (InfoGeometry.Topology.KANWallpaper.T_x - 1) =
      (InfoGeometry.Topology.KANWallpaper.T_x - 1) * InfoGeometry.Topology.KANWallpaper.G
    have hQP : InfoGeometry.Topology.KANWallpaper.G * InfoGeometry.Topology.KANWallpaper.T_x =
        InfoGeometry.Topology.KANWallpaper.T_x * InfoGeometry.Topology.KANWallpaper.G :=
      wallpaper_Q_comm_P
    rw [mul_sub, sub_mul, mul_one, one_mul, hQP]

/-- Unit vertical translation `T_y : y ↦ y + 1` in `ProjMatrix`. -/
def T_y : InfoGeometry.Topology.KANWallpaper.ProjMatrix :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

/-- Inverse vertical translation `T_y⁻¹ : y ↦ y - 1`. -/
def T_y_inv : InfoGeometry.Topology.KANWallpaper.ProjMatrix :=
  !![1, 0, 0;
     0, 1, -1;
     0, 0, 1]

/-- Glide reflection reverses vertical translation: `G * T_y = T_y⁻¹ * G`. -/
theorem wallpaper_glide_conjugates_Ty :
    InfoGeometry.Topology.KANWallpaper.G * T_y =
      T_y_inv * InfoGeometry.Topology.KANWallpaper.G := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Topology.KANWallpaper.G, T_y, T_y_inv,
      Matrix.mul_apply, Fin.sum_univ_three]

/-- Local `Matrix (Fin 3) (Fin 3) ℝ`-typed alias of `KANWallpaper.G` for witness matching. -/
def G3 : Matrix (Fin 3) (Fin 3) ℝ := InfoGeometry.Topology.KANWallpaper.G

/-- Local `Matrix (Fin 3) (Fin 3) ℝ`-typed alias of `T_y` for witness matching. -/
def T_y3 : Matrix (Fin 3) (Fin 3) ℝ := T_y

/-- Mandatory T16 non-commutativity witness for `Matrix (Fin 3) (Fin 3) ℝ`:
    glide reflection `G` and vertical translation `T_y` do not commute. -/
theorem wallpaper_G_Ty_noncomm : G3 * T_y3 ≠ T_y3 * G3 := by
  intro h
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) h
  simp [G3, T_y3, InfoGeometry.Topology.KANWallpaper.G, T_y,
    Matrix.mul_apply, Fin.sum_univ_three] at h12
  norm_num at h12

/-! ## 3. Finite Partner-Block SUSY Closure (`FiniteSUSYSystem`) -/

/-- Any nilpotent finite SUSY block system (`A² = 0`, `A†² = 0`) induces a
    `CrystallographicSUSYDatum (MatC k)` with `Q = A + A†` and `P = H₊ + H₋`. -/
def finiteSUSYToDatum {k : ℕ} (sys : FiniteSUSYSystem k)
    (hA : sys.A * sys.A = 0) (hAdag : sys.A_dag * sys.A_dag = 0) :
    CrystallographicSUSYDatum (MatC k) where
  Q := sys.A + sys.A_dag
  P := sys.H_plus + sys.H_minus
  sq_eq := nilpotent_dirac_square_eq_closure sys.A sys.A_dag sys.H_plus sys.H_minus
    hA hAdag sys.odd_anticommutator_is_even_sum

/-- Partner-block supercharge closure `{Q, Q} = (2 : ℂ) • (H₊ + H₋)` and `[Q, H₊ + H₋] = 0`. -/
theorem finiteSUSY_closure_and_comm {k : ℕ} (sys : FiniteSUSYSystem k)
    (hA : sys.A * sys.A = 0) (hAdag : sys.A_dag * sys.A_dag = 0) :
    anticomm (sys.A + sys.A_dag) (sys.A + sys.A_dag) =
        (2 : ℂ) • (sys.H_plus + sys.H_minus) ∧
      (sys.A + sys.A_dag) * (sys.H_plus + sys.H_minus) =
        (sys.H_plus + sys.H_minus) * (sys.A + sys.A_dag) :=
  ⟨(finiteSUSYToDatum sys hA hAdag).anticomm_eq_two_smul_complex,
   (finiteSUSYToDatum sys hA hAdag).comm_Q_P⟩

/-- Concrete `2 × 2` spin-half realization `Q₂ = J₋ + J₊` with `Q₂² = 1` and `{Q₂, Q₂} = 2 • 1`. -/
def spinHalfSUSYDatum : CrystallographicSUSYDatum (MatC 2) :=
  finiteSUSYToDatum canonicalFiniteSUSYSystem
    canonical_supercharge_square_zero canonical_adjoint_supercharge_square_zero

theorem spinHalfSUSY_P_eq_one : spinHalfSUSYDatum.P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfSUSYDatum, finiteSUSYToDatum, canonicalFiniteSUSYSystem,
      FiniteSUSYSystem.H_plus, FiniteSUSYSystem.H_minus, superchargeA, superchargeAdag,
      J_minus, J_plus]

/-! ## 4. Explicit `N = 2` Clifford-SUSY Algebra on `Matrix (Fin 4) (Fin 4) ℂ` -/

/-- First `N = 2` supercharge `Q₁ = σₓ ⊗ I₂` on `Matrix (Fin 4) (Fin 4) ℂ`. -/
def Q1_N2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Second `N = 2` supercharge `Q₂ = σ_y ⊗ σ_z` on `Matrix (Fin 4) (Fin 4) ℂ`. -/
def Q2_N2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, -Complex.I, 0;
     0, 0, 0, Complex.I;
     Complex.I, 0, 0, 0;
     0, -Complex.I, 0, 0]

/-- Central momentum operator `P₄ = I₄` for the `N = 2` superalgebra. -/
def P4_N2 : Matrix (Fin 4) (Fin 4) ℂ := 1

theorem Q1_N2_sq : Q1_N2 * Q1_N2 = P4_N2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q1_N2, P4_N2, Matrix.mul_apply, Fin.sum_univ_four]

theorem Q2_N2_sq : Q2_N2 * Q2_N2 = P4_N2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q2_N2, P4_N2, Matrix.mul_apply, Fin.sum_univ_four]

/-- Both `Q₁` and `Q₂` form `CrystallographicSUSYDatum` instances over `Matrix (Fin 4) (Fin 4) ℂ`. -/
def n2SUSYDatum1 : CrystallographicSUSYDatum (Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨Q1_N2, P4_N2, Q1_N2_sq⟩

def n2SUSYDatum2 : CrystallographicSUSYDatum (Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨Q2_N2, P4_N2, Q2_N2_sq⟩

/-- Diagonal `N = 2` SUSY anticommutators: `{Q₁, Q₁} = 2 • P₄` and `{Q₂, Q₂} = 2 • P₄`. -/
theorem n2_diag_anticomm :
    anticomm Q1_N2 Q1_N2 = (2 : ℂ) • P4_N2 ∧
      anticomm Q2_N2 Q2_N2 = (2 : ℂ) • P4_N2 :=
  ⟨n2SUSYDatum1.anticomm_eq_two_smul_complex, n2SUSYDatum2.anticomm_eq_two_smul_complex⟩

/-- Off-diagonal `N = 2` SUSY anticommutator vanishes: `{Q₁, Q₂} = 0`. -/
theorem n2_offdiag_anticomm : anticomm Q1_N2 Q2_N2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [anticomm, Q1_N2, Q2_N2]

/-- Mandatory T16 non-commutativity witness for `Matrix (Fin 4) (Fin 4) ℂ`:
    `Q₁ * Q₂ ≠ Q₂ * Q₁` (`(Q₁ * Q₂) 0 0 = i ≠ -i = (Q₂ * Q₁) 0 0`). -/
theorem n2_Q1_Q2_noncomm : Q1_N2 * Q2_N2 ≠ Q2_N2 * Q1_N2 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  simp [Q1_N2, Q2_N2, Matrix.mul_apply, Fin.sum_univ_four] at h00
  have hI : (2 : ℂ) * Complex.I = 0 := by linear_combination h00
  have hne : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact hne hI

/-- Chiral nilpotent supercharge `Q₊ = (1/2) (Q₁ + i Q₂)`. -/
def Qplus_N2 : Matrix (Fin 4) (Fin 4) ℂ :=
  ((1 / 2 : ℂ)) • (Q1_N2 + Complex.I • Q2_N2)

/-- Conjugate chiral nilpotent supercharge `Q₋ = (1/2) (Q₁ - i Q₂)`. -/
def Qminus_N2 : Matrix (Fin 4) (Fin 4) ℂ :=
  ((1 / 2 : ℂ)) • (Q1_N2 - Complex.I • Q2_N2)

theorem Qplus_N2_sq : Qplus_N2 * Qplus_N2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qplus_N2, Q1_N2, Q2_N2, Matrix.mul_apply, Fin.sum_univ_four]

theorem Qminus_N2_sq : Qminus_N2 * Qminus_N2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qminus_N2, Q1_N2, Q2_N2, Matrix.mul_apply, Fin.sum_univ_four]

/-- Chiral `N = 2` closure: `{Q₊, Q₋} = P₄` and `(Q₊ + Q₋)² = P₄`. -/
theorem n2_chiral_closure :
    anticomm Qplus_N2 Qminus_N2 = P4_N2 ∧
      (Qplus_N2 + Qminus_N2) * (Qplus_N2 + Qminus_N2) = P4_N2 := by
  have hanti : anticomm Qplus_N2 Qminus_N2 = P4_N2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [anticomm, Qplus_N2, Qminus_N2, Q1_N2, Q2_N2, P4_N2] <;>
      ring_nf
  refine ⟨hanti, ?_⟩
  simpa [zero_add] using nilpotent_dirac_square_eq_closure Qplus_N2 Qminus_N2 P4_N2 0
    Qplus_N2_sq Qminus_N2_sq (by simpa using hanti)

/-! ## 5. Compatibility with Rest-Frame Super-Poincaré (`PoincareSupercharge`) -/

/-- At rest frame `P_rest = (1, 0, 0, 0)`, the Pauli super-Poincaré anticommutator matrix
    matches `spinHalfSUSYDatum`'s `{Q₂, Q₂} = 2 • 1` with Minkowski Casimir determinant `4`. -/
theorem rest_frame_superPoincare_matches_spinHalf :
    let P_rest : PauliParavector := ⟨1, 0, 0, 0⟩
    P_rest.superPoincareAnticommutatorMatrix =
        anticomm spinHalfSUSYDatum.Q spinHalfSUSYDatum.Q ∧
      Matrix.det P_rest.superPoincareAnticommutatorMatrix = 4 := by
  refine ⟨?_, ?_⟩
  · rw [spinHalfSUSYDatum.anticomm_eq_two_smul_complex, spinHalfSUSY_P_eq_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PauliParavector.superPoincareAnticommutatorMatrix, PauliParavector.pauliMatrix]
  · rw [InfoGeometry.Quantum.PoincareSupercharge.pauli_supercharge_anticommutator_det_eq_four_casimir]
    simp [PauliParavector.minkowskiNormSq]

end InfoGeometry.GrandUnification.Supergravity

end noncomputable section
