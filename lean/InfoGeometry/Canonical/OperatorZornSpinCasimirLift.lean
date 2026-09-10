import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.FourVectorPauliCasimirBridge
import InfoGeometry.Physics.OperatorZornMatrixAlgebra
import InfoGeometry.Quantum.PauliSoldering
import InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge

/-!
# InfoGeometry.Canonical.OperatorZornSpinCasimirLift

Finite spin-1/2 projection and quadratic-Casimir data transported to the
repository's associative chiral `OperatorZornMatrix` carrier.

The repository already owns:

* Pauli matrices and their multiplication table;
* nilpotent circular raising/lowering matrices `sigmaPlus`, `sigmaMinus`;
* complementary circular projectors and the helicity involution;
* the associative `OperatorZornMatrix ≃+* Matrix (Fin 2) (Fin 2) A` carrier.

This file adds the missing compatibility layer.  It proves the genuine
spin-half quadratic Casimir

`S₁² + S₂² + S₃² = 3/4 I`,

identifies the circular projectors as the `±1/2` spin projections, and
transports the projectors, helicity, ladder operators, and Casimir to the
operator-Zorn/chiral coordinates.  No new spin representation or Casimir
notion is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorZornSpinCasimirLift

open Matrix
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge
open InfoGeometry.Physics
open InfoGeometry.Physics.OperatorZornMatrix

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev OperatorZornC := OperatorZornMatrix ℂ

/-! ## Spin-half Pauli generators and Casimir -/

/-- `S₁ = σ₁/2`. -/
def spinX : Mat2C := (2 : ℂ)⁻¹ • σ1

/-- `S₂ = σ₂/2`. -/
def spinY : Mat2C := (2 : ℂ)⁻¹ • σ2

/-- `S₃ = σ₃/2`. -/
def spinZ : Mat2C := (2 : ℂ)⁻¹ • σ3

@[simp] theorem spinX_sq :
    spinX * spinX = (4 : ℂ)⁻¹ • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinX, σ1, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] theorem spinY_sq :
    spinY * spinY = (4 : ℂ)⁻¹ • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinY, σ2, Matrix.mul_apply, Fin.sum_univ_two, pow_two] <;>
      ring_nf <;> simp [Complex.I_sq] <;> norm_num

@[simp] theorem spinZ_sq :
    spinZ * spinZ = (4 : ℂ)⁻¹ • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinZ, σ3, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Quadratic spin Casimir in the fundamental Pauli representation. -/
def spinHalfCasimir : Mat2C :=
  spinX * spinX + spinY * spinY + spinZ * spinZ

/-- The exact spin-half value `s(s+1)=3/4`. -/
theorem spinHalfCasimir_eq_three_quarters :
    spinHalfCasimir = (3 / 4 : ℂ) • (1 : Mat2C) := by
  rw [spinHalfCasimir, spinX_sq, spinY_sq, spinZ_sq]
  module

/-! ## Circular basis and spin projections -/

/-- Circular helicity is exactly the third Pauli matrix. -/
theorem circularHelicity_eq_sigma3 :
    circularHelicity = σ3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularHelicity, circularPlus, circularMinus,
      InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularPlusProjector,
      InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularMinusProjector,
      InfoGeometry.Optics.FiniteJonesModel.sProjector,
      InfoGeometry.Optics.FiniteJonesModel.pProjector,
      InfoGeometry.Optics.FiniteJonesModel.diagJones,
      σ3]

/-- Hence `S₃` is one half of the circular helicity involution. -/
theorem spinZ_eq_half_helicity :
    spinZ = (2 : ℂ)⁻¹ • circularHelicity := by
  rw [circularHelicity_eq_sigma3]
  rfl

/-- Positive circular projector is the `+1` eigenspace projector of helicity. -/
theorem helicity_mul_circularPlus :
    circularHelicity * circularPlus = circularPlus := by
  unfold circularHelicity
  rw [sub_mul,
    InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularPlusProjector_idem,
    InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularProjectors_orthogonal_right]
  simp

/-- Negative circular projector is the `-1` eigenspace projector of helicity. -/
theorem helicity_mul_circularMinus :
    circularHelicity * circularMinus = -circularMinus := by
  unfold circularHelicity
  rw [sub_mul,
    InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularProjectors_orthogonal_left,
    InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularMinusProjector_idem]
  simp

/-- The two circular sectors therefore carry spin projections `+1/2` and
`-1/2`. -/
theorem spinZ_projection_packet :
    spinZ * circularPlus = (2 : ℂ)⁻¹ • circularPlus ∧
      spinZ * circularMinus = -(2 : ℂ)⁻¹ • circularMinus := by
  constructor
  · rw [spinZ_eq_half_helicity]
    calc
      ((2 : ℂ)⁻¹ • circularHelicity) * circularPlus =
          (2 : ℂ)⁻¹ • (circularHelicity * circularPlus) := by
            rw [smul_mul_assoc]
      _ = (2 : ℂ)⁻¹ • circularPlus := by rw [helicity_mul_circularPlus]
  · rw [spinZ_eq_half_helicity]
    calc
      ((2 : ℂ)⁻¹ • circularHelicity) * circularMinus =
          (2 : ℂ)⁻¹ • (circularHelicity * circularMinus) := by
            rw [smul_mul_assoc]
      _ = (2 : ℂ)⁻¹ • (-circularMinus) := by rw [helicity_mul_circularMinus]
      _ = -(2 : ℂ)⁻¹ • circularMinus := by module

/-- The circular nilpotents are the spin raising/lowering operators. -/
def spinRaise : Mat2C := sigmaPlus

def spinLower : Mat2C := sigmaMinus

/-- Standard `su(2)` ladder commutator `[S₊,S₋]=2S₃`. -/
theorem spinRaise_spinLower_commutator :
    spinRaise * spinLower - spinLower * spinRaise = 2 • spinZ := by
  rw [spinRaise, spinLower]
  rw [sigmaPlus_mul_sigmaMinus, sigmaMinus_mul_sigmaPlus]
  change circularHelicity = 2 • spinZ
  rw [circularHelicity_eq_sigma3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinZ, σ3]

/-- Symmetrized ladder product is the identity, equivalently the two circular
spin projections resolve the complete two-state carrier. -/
theorem spinRaise_spinLower_anticommutator :
    spinRaise * spinLower + spinLower * spinRaise = 1 := by
  exact sigmaPlus_oddOdd_eq_identity

/-! ## Associative transport to the operator-Zorn carrier -/

def zornLift (A : Mat2C) : OperatorZornC := ofMatrix A

@[simp] theorem toMatrix_zornLift (A : Mat2C) :
    toMatrix (zornLift A) = A := by
  simp [zornLift]

theorem zornLift_mul (A B : Mat2C) :
    zornLift (A * B) = zornLift A * zornLift B := by
  apply (equivMatrix (A := ℂ)).injective
  simp [zornLift]

theorem zornLift_casimir :
    zornLift spinHalfCasimir =
      ofMatrix ((3 / 4 : ℂ) • (1 : Mat2C)) := by
  apply (equivMatrix (A := ℂ)).injective
  simp [zornLift, equivMatrix, ofMatrix, toMatrix,
    spinHalfCasimir_eq_three_quarters]

theorem zornLift_ladder_anticommutator :
    zornLift spinRaise * zornLift spinLower +
        zornLift spinLower * zornLift spinRaise = 1 := by
  apply (equivMatrix (A := ℂ)).injective
  simp [zornLift, spinRaise_spinLower_anticommutator]

end InfoGeometry.Canonical.OperatorZornSpinCasimirLift
