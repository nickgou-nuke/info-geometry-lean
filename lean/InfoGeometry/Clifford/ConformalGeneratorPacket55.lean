import InfoGeometry.Clifford.ConformalLieAlgebra55Dilation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.ConformalReflection55
import InfoGeometry.Clifford.ModularCftBridge
import InfoGeometry.Clifford.DiscreteMoebiusGroup
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

noncomputable section

/-!
# ConformalGeneratorPacket55

This file freezes a small source-faithful conformal generator packet matching the
explicit `2 × 2`/`sl₂` witness used on the SymPy side.

Infinitesimal packet:
- `P = u5` (translation)
- `D = D5` (dilation)
- `K = v5` (special conformal)

Projective packet:
- `T = modularT` (upper-triangular translation generator)
- `S = modularS` (projective inversion generator)

The file does not claim a full global conformal closure for all Clifford
components.  It only packages the exact existing owner-side theorems for this
single null-pair lane and its projective readout.

Ambient symmetry naming for this packet:
- `Cl(5,5)` is the carrier.
- `O(5,5)` is the ambient split-orthogonal symmetry group.
- `Pin(5,5)` is the honest Clifford double cover including reflections.
- `Spin(5,5)` is the even orientation-preserving subgroup.

This file packages only the infinitesimal `P/D/K` readout and the explicit
projective `T/S` chart action already proved in the owner lanes.
-/

namespace InfoGeometry.Clifford.ConformalGeneratorPacket55

open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Clifford.ConformalLieAlgebra55Dilation
open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Clifford.ConformalReflection55
open InfoGeometry.Clifford.ModularCftBridge
open InfoGeometry.Clifford.DiscreteMoebiusGroup
open InfoGeometry.Clifford.MonodromyFlowAdapter

/-- Translation generator in the SymPy/`sl₂` packet. -/
abbrev P := u5

/-- Dilation generator in the SymPy/`sl₂` packet. -/
abbrev D := D5

/-- Special conformal generator in the SymPy/`sl₂` packet. -/
abbrev K := v5

@[simp] theorem P_sq : P * P = 0 :=
  ConformalLieAlgebra55Dilation.u5_sq

@[simp] theorem K_sq : K * K = 0 :=
  ConformalLieAlgebra55Dilation.v5_sq

@[simp] theorem P_K_add_K_P : P * K + K * P = 1 :=
  ConformalLieAlgebra55Dilation.u5_v5_add_v5_u5

/-- In the null-pair packet, dilation acts on translation with weight `+1`. -/
theorem adD_P : D * P - P * D = P :=
  ConformalLieAlgebra55Dilation.adD5_u5

/-- In the null-pair packet, dilation acts on special conformal with weight `-1`. -/
theorem adD_K : D * K - K * D = -K :=
  ConformalLieAlgebra55Dilation.adD5_v5

/-- The null-pair `P/K` commutator closes to `2D`. -/
theorem P_K_commutator :
    P * K - K * P = (2 : ℝ) • D := by
  calc
    P * K - K * P = u5 * v5 - v5 * u5 := by rfl
    _ = (2 : ℝ) • ((1 / 2 : ℝ) • (u5 * v5 - v5 * u5)) := by
      rw [smul_smul]
      norm_num
    _ = (2 : ℝ) • D := by rfl

/-! ## Ambient null-pair / inversion packet -/

/-- Generic ambient null-pair translation witness. -/
abbrev U (p : ConformalNullPair) := p.u

/-- Generic ambient null-pair special-conformal witness. -/
abbrev V (p : ConformalNullPair) := p.v

/-- Generic ambient inversion/reflection witness. -/
abbrev Jgen (p : ConformalNullPair) := J p

@[simp] theorem U_sq (p : ConformalNullPair) : U p * U p = 0 := by
  rw [← sq]
  simpa [U] using p.u_square

@[simp] theorem V_sq (p : ConformalNullPair) : V p * V p = 0 := by
  rw [← sq]
  simpa [V] using p.v_square

@[simp] theorem U_V_add_V_U (p : ConformalNullPair) : U p * V p + V p * U p = 1 := by
  simpa [U, V] using p.anticomm

@[simp] theorem Jgen_sq (p : ConformalNullPair) : Jgen p ^ 2 = -1 :=
  ConformalReflection55.J_sq p

theorem Jgen_swaps_U_to_V (p : ConformalNullPair) :
    Jgen p * U p * Jgen p = V p := by
  simpa [Jgen, U, V] using ConformalReflection55.J_swap_origin p

theorem Jgen_swaps_V_to_U (p : ConformalNullPair) :
    Jgen p * V p * Jgen p = U p := by
  simpa [Jgen, U, V] using ConformalReflection55.J_swap_infinity p

theorem Jgen_mul_neg_Jgen (p : ConformalNullPair) :
    Jgen p * (-Jgen p) = 1 := by
  simpa [Jgen] using ConformalReflection55.J_mul_neg_J p

theorem neg_Jgen_mul_Jgen (p : ConformalNullPair) :
    (-Jgen p) * Jgen p = 1 := by
  simpa [Jgen] using ConformalReflection55.neg_J_mul_J p

/-- Projective translation generator in the affine chart. -/
abbrev T : Matrix (Fin 2) (Fin 2) ℂ := modularT

/-- Projective inversion generator. -/
abbrev S : Matrix (Fin 2) (Fin 2) ℂ := modularS

/-- Chosen explicit inverse of `S`. -/
abbrev SInv : Matrix (Fin 2) (Fin 2) ℂ := modularSInverse

/-- Explicit `2 × 2` dilation generator in the projective `sl₂` packet. -/
def Dproj : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 2, 0; 0, -1 / 2]

/-- The modular inversion matrix is an involution up to sign. -/
theorem S_sq_neg_I : S * S = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [S, modularS]

/-- Inversion flips the sign of the projective dilation generator. -/
theorem S_conjugates_Dproj_neg :
    S * Dproj * SInv = -Dproj := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [S, SInv, Dproj, modularS, modularSInverse]

/-- The dilation sign flip exponentiates to the rapidity inversion law. -/
theorem S_conjugates_exp_dilation_neg (lam : ℂ) :
    S * NormedSpace.exp (lam • Dproj) * SInv =
      NormedSpace.exp (-lam • Dproj) := by
  have hconj :
      (S : Matrix (Fin 2) (Fin 2) ℂ) * (lam • Dproj) * SInv = - (lam • Dproj) := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [S, SInv, Dproj, modularS, modularSInverse]
  have hExp :=
    Matrix.exp_units_conj'
      (U := (⟨SInv, S, modularS_inverse_mul, modularS_mul_inverse⟩ :
        (Matrix (Fin 2) (Fin 2) ℂ)ˣ))
      (A := lam • Dproj)
  calc
    S * NormedSpace.exp (lam • Dproj) * SInv
        = NormedSpace.exp (S * (lam • Dproj) * SInv) := by
            symm
            simpa using hExp
    _ = NormedSpace.exp (-(lam • Dproj)) := by rw [hconj]
    _ = NormedSpace.exp (-lam • Dproj) := by simp [smul_neg]

/-- The affine chart action of the projective translation generator. -/
theorem T_action (z : ℂ) :
    moebiusAction T z = z + 1 :=
  moebius_T_action z

/-- Powers of `T` act by additive translations on the affine chart. -/
theorem T_pow_action (m : ℕ) (z : ℂ) :
    moebiusAction (T ^ m) z = z + (m : ℂ) := by
  simpa [T] using moebius_T_pow_action m z

/-- The projective inversion generator acts by `z ↦ -1 / z`. -/
theorem S_action (z : ℂ) :
    moebiusAction S z = -1 / z :=
  moebius_S_action z

/-- The parabolic translation flow is exactly the upper-triangular shear packet. -/
theorem affine_flow_eq_upper_shear (t : ℂ) :
    lcftParabolicFlowStep t = !![1, t; 0, 1] :=
  lcftParabolicFlowStep_eq t

/-- Conjugation by `S` sends the upper shear to the lower shear sector. -/
theorem S_conjugates_upper_shear_to_lower (t : ℂ) :
    S * lcftParabolicFlowStep t * SInv = !![1, 0; -t, 1] :=
  parabolicFlow_S_conjugation t

/-- The same lower-shear readback for the discrete modular translation subgroup. -/
theorem S_conjugates_T_pow_to_lower_shear (m : ℕ) :
    S * T ^ m * SInv = !![1, 0; -(m : ℂ), 1] := by
  simpa [S, T, SInv] using modularT_pow_S_conjugation m

end InfoGeometry.Clifford.ConformalGeneratorPacket55
