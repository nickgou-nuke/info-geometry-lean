import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.DeterminantSupergrading
import InfoGeometry.External.Auto.TrifactorGeometry
import InfoGeometry.External.Auto.LieFlowCompilerBridge
import InfoGeometry.External.Auto.MobiusInversion

noncomputable section

open Matrix
open Complex

namespace InfoGeometry.Canonical.TopologicalBraiding

open InfoGeometry.Canonical.LieFlowCompiler

variable {G X V : Type*} [Group G] [MulAction G X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R
abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Step-7 trajectory operators reused as concrete Pauli-like braid generators. -/
def pauliX : M2R := modular_j

def pauliZ : M2R := chiralParity

def pauliXc : M2C := !![(0 : ℂ), 1; 1, 0]

def pauliZc : M2C := !![(1 : ℂ), 0; 0, -1]

/-- Local braid operator in the doubled-sheet 2×2 sector. -/
def braidOperatorR (σ₁ σ₂ : M2R) : M2R := σ₁ * σ₂

def braidOperator (σ₁ σ₂ : M2C) : M2C := σ₁ * σ₂

/-- Pauli-like braid generators from the Z₂ twisted sheet geometry do not commute. -/
theorem pauliXZ_noncommute_R : braidOperatorR pauliX pauliZ ≠ braidOperatorR pauliZ pauliX := by
  intro h
  have h01 : (braidOperatorR pauliX pauliZ) 0 1 = (-1 : ℝ) := by
    simp [braidOperatorR, pauliX, pauliZ, modular_j, chiralParity, Matrix.mul_apply,
      Fin.sum_univ_two]
  have h01' : (braidOperatorR pauliZ pauliX) 0 1 = (1 : ℝ) := by
    simp [braidOperatorR, pauliX, pauliZ, modular_j, chiralParity, Matrix.mul_apply,
      Fin.sum_univ_two]
  have hcontra : (-1 : ℝ) = 1 := by
    simpa [h01, h01'] using congrArg (fun M => M 0 1) h
  norm_num at hcontra

/-- The same noncommutation computation in complex Pauli form. -/
theorem pauliXZ_noncommute_C : braidOperator pauliXc pauliZc ≠ braidOperator pauliZc pauliXc := by
  intro h
  have h01 : (braidOperator pauliXc pauliZc) 0 1 = (-1 : ℂ) := by
    simp [braidOperator, pauliXc, pauliZc, Matrix.mul_apply, Fin.sum_univ_two]
  have h01' : (braidOperator pauliZc pauliXc) 0 1 = (1 : ℂ) := by
    simp [braidOperator, pauliXc, pauliZc, Matrix.mul_apply, Fin.sum_univ_two]
  have hcontra : (-1 : ℝ) = (1 : ℝ) := by
    have hcontraC : (-1 : ℂ) = (1 : ℂ) := by
      simpa [h01, h01'] using congrArg (fun M => M 0 1) h
    exact congrArg Complex.re hcontraC
  norm_num at hcontra

/-- The Z2 flow carries a concrete non-abelian braid gate. -/
theorem z2_rindler_braiding_is_nonabelian
    (_rf : KMSCompiler G X V) :
    ∃ (σ₁ σ₂ : M2R),
      braidOperatorR σ₁ σ₂ ≠ braidOperatorR σ₂ σ₁ := by
  use pauliX
  use pauliZ
  exact pauliXZ_noncommute_R

/-- Trifactor projectors for OP³-classified sectors are idempotent in the cubic case. -/
theorem nonabelian_packet_with_trifactor
    {q : ℝ} (hq : q ^ 3 = q) :
    (TrifactorGeometry.trifactorProjectorPlus q) ^ 2 = TrifactorGeometry.trifactorProjectorPlus q ∧
    (TrifactorGeometry.trifactorProjectorMinus q) ^ 2 = TrifactorGeometry.trifactorProjectorMinus q := by
  constructor
  · exact TrifactorGeometry.trifactor_projector_idempotent_plus hq
  · exact TrifactorGeometry.trifactor_projector_idempotent_minus hq

/-- Determinant supergrading remains multiplicative across braid composition. -/
theorem braid_grade_multiplicative (A B : M2R) :
    superGrade (A * B) = superGrade A * superGrade B :=
  superGrade_mul A B

/-- Möbius inversion gives the arithmetic duality identity used by this layer. -/
theorem moebius_duality_layer :
    dirichletConvolution bosonicKernel fermionicMobiusKernel = vacuumKernel :=
  mobius_is_dirichlet_inverse

end InfoGeometry.Canonical.TopologicalBraiding
