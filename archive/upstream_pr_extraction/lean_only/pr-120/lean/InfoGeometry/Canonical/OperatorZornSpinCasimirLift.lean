import Mathlib.Tactic
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

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ
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
    simp [spinX, σ1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem spinY_sq :
    spinY * spinY = (4 : ℂ)⁻¹ • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinY, σ2, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

@[simp] theorem spinZ_sq :
    spinZ * spinZ = (4 : ℂ)⁻¹ • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinZ, σ3, Matrix.mul_apply, Fin.sum_univ_two]

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
      InfoGeometry.Optics.JonesPoincareSphere.FiniteJonesModel.sProjector,
      InfoGeometry.Optics.JonesPoincareSphere.FiniteJonesModel.pProjector,
      InfoGeometry.Optics.JonesPoincareSphere.FiniteJonesModel.diagJones,
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
  rw [← circularHelicity_eq_commutator, circularHelicity_eq_sigma3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinZ, σ3]

/-- Symmetrized ladder product is the identity, equivalently the two circular
spin projections resolve the complete two-state carrier. -/
theorem spinRaise_spinLower_anticommutator :
    spinRaise * spinLower + spinLower * spinRaise = 1 := by
  exact sigmaPlus_oddOdd_eq_identity

/-! ## Transport to associative operator-Zorn coordinates -/

/-- Matrix-to-operator-Zorn lift through the repository's existing ring
isomorphism. -/
def zornLift (A : Mat2C) : OperatorZornC :=
  ofMatrix A

@[simp] theorem toMatrix_zornLift (A : Mat2C) :
    toMatrix (zornLift A) = A := by
  simp [zornLift]

/-- The lift respects multiplication exactly. -/
theorem zornLift_mul (A B : Mat2C) :
    zornLift (A * B) = zornLift A * zornLift B := by
  apply (equivMatrix (A := ℂ)).injective
  simp [zornLift]

/-- Positive and negative spin projectors in operator-Zorn coordinates. -/
def zornSpinPlusProjector : OperatorZornC := zornLift circularPlus

def zornSpinMinusProjector : OperatorZornC := zornLift circularMinus

/-- Helicity grading in operator-Zorn coordinates. -/
def zornHelicity : OperatorZornC := zornLift circularHelicity

/-- Circular spin raising and lowering rails in operator-Zorn coordinates. -/
def zornSpinRaise : OperatorZornC := zornLift spinRaise

def zornSpinLower : OperatorZornC := zornLift spinLower

/-- Spin-half quadratic Casimir in operator-Zorn coordinates. -/
def zornSpinHalfCasimir : OperatorZornC := zornLift spinHalfCasimir

/-- The positive spin projector is purely the upper diagonal chiral sector. -/
theorem zornSpinPlusProjector_coordinates :
    zornSpinPlusProjector =
      ({ n_plus_op := 1, n_minus_op := 0,
         sigma_plus_op := 0, sigma_minus_op := 0 } : OperatorZornC) := by
  apply (equivMatrix (A := ℂ)).injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zornSpinPlusProjector, zornLift, circularPlus,
      InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularPlusProjector,
      InfoGeometry.Optics.JonesPoincareSphere.FiniteJonesModel.sProjector,
      InfoGeometry.Optics.JonesPoincareSphere.FiniteJonesModel.diagJones,
      toMatrix]

/-- The negative spin projector is purely the lower diagonal chiral sector. -/
theorem zornSpinMinusProjector_coordinates :
    zornSpinMinusProjector =
      ({ n_plus_op := 0, n_minus_op := 1,
         sigma_plus_op := 0, sigma_minus_op := 0 } : OperatorZornC) := by
  apply (equivMatrix (A := ℂ)).injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zornSpinMinusProjector, zornLift, circularMinus,
      InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularMinusProjector,
      InfoGeometry.Optics.JonesPoincareSphere.FiniteJonesModel.pProjector,
      InfoGeometry.Optics.JonesPoincareSphere.FiniteJonesModel.diagJones,
      toMatrix]

/-- Helicity is the diagonal chiral grading `diag(1,-1)`. -/
theorem zornHelicity_coordinates :
    zornHelicity =
      ({ n_plus_op := 1, n_minus_op := -1,
         sigma_plus_op := 0, sigma_minus_op := 0 } : OperatorZornC) := by
  apply (equivMatrix (A := ℂ)).injective
  rw [toMatrix_zornLift]
  rw [circularHelicity_eq_sigma3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ3, toMatrix]

/-- Raising is the upper-right odd/chiral rail. -/
theorem zornSpinRaise_coordinates :
    zornSpinRaise =
      ({ n_plus_op := 0, n_minus_op := 0,
         sigma_plus_op := 1, sigma_minus_op := 0 } : OperatorZornC) := by
  apply (equivMatrix (A := ℂ)).injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zornSpinRaise, zornLift, spinRaise, sigmaPlus,
      InfoGeometry.Optics.ChiralLorentzOperatorLift.create, toMatrix]

/-- Lowering is the lower-left odd/chiral rail. -/
theorem zornSpinLower_coordinates :
    zornSpinLower =
      ({ n_plus_op := 0, n_minus_op := 0,
         sigma_plus_op := 0, sigma_minus_op := 1 } : OperatorZornC) := by
  apply (equivMatrix (A := ℂ)).injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zornSpinLower, zornLift, spinLower, sigmaMinus,
      InfoGeometry.Optics.ChiralLorentzOperatorLift.annihilate, toMatrix]

/-- The spin-half Casimir remains central and diagonal after the operator-Zorn
lift. -/
theorem zornSpinHalfCasimir_coordinates :
    zornSpinHalfCasimir =
      ({ n_plus_op := (3 / 4 : ℂ), n_minus_op := (3 / 4 : ℂ),
         sigma_plus_op := 0, sigma_minus_op := 0 } : OperatorZornC) := by
  apply (equivMatrix (A := ℂ)).injective
  rw [toMatrix_zornLift, spinHalfCasimir_eq_three_quarters]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [toMatrix]

/-- The operator-Zorn helicity still squares to the identity. -/
theorem zornHelicity_sq :
    zornHelicity * zornHelicity = 1 := by
  apply (equivMatrix (A := ℂ)).injective
  simp [zornHelicity, zornLift, circularHelicity_sq]

/-- The two lifted spin projections remain complementary idempotents. -/
theorem zornSpinProjector_packet :
    zornSpinPlusProjector * zornSpinPlusProjector = zornSpinPlusProjector ∧
      zornSpinMinusProjector * zornSpinMinusProjector = zornSpinMinusProjector ∧
      zornSpinPlusProjector * zornSpinMinusProjector = 0 ∧
      zornSpinPlusProjector + zornSpinMinusProjector = 1 := by
  constructor
  · apply (equivMatrix (A := ℂ)).injective
    simp [zornSpinPlusProjector, zornLift,
      InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularPlusProjector_idem]
  constructor
  · apply (equivMatrix (A := ℂ)).injective
    simp [zornSpinMinusProjector, zornLift,
      InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularMinusProjector_idem]
  constructor
  · apply (equivMatrix (A := ℂ)).injective
    simp [zornSpinPlusProjector, zornSpinMinusProjector, zornLift,
      InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularProjectors_orthogonal_left]
  · apply (equivMatrix (A := ℂ)).injective
    simp [zornSpinPlusProjector, zornSpinMinusProjector, zornLift,
      InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularProjectors_sum_one]

/-- Capstone: the lifted chiral spin data simultaneously expose the two spin
projections, the odd ladder rails, the helicity involution, and the central
spin-half Casimir. -/
theorem operatorZorn_spin_half_packet :
    zornHelicity * zornHelicity = 1 ∧
      zornSpinPlusProjector * zornSpinPlusProjector = zornSpinPlusProjector ∧
      zornSpinMinusProjector * zornSpinMinusProjector = zornSpinMinusProjector ∧
      zornSpinPlusProjector * zornSpinMinusProjector = 0 ∧
      toMatrix zornSpinHalfCasimir = (3 / 4 : ℂ) • (1 : Mat2C) := by
  refine ⟨zornHelicity_sq, ?_⟩
  rcases zornSpinProjector_packet with ⟨hp, hm, hpm, _⟩
  refine ⟨hp, hm, hpm, ?_⟩
  simp [zornSpinHalfCasimir, spinHalfCasimir_eq_three_quarters]

end InfoGeometry.Canonical.OperatorZornSpinCasimirLift
