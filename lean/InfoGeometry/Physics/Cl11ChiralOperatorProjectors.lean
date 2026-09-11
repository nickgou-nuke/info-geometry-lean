import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import InfoGeometry.Physics.Cl11ChiralCARBridge

noncomputable section

namespace InfoGeometry.Physics.Cl11ChiralCARBridge

open InfoGeometry.Physics.ChiralCausalCone

/-!
  The native associative operator calculus for the circular chiral basis.
  The split-octonion/Zorn constructions are downstream readouts of these
  operators, not their foundational carrier.
-/

def chiralGamma : M2C := σ3c

def chiralProjectorPlus : M2C := σPlus * σMinus

def chiralProjectorMinus : M2C := σMinus * σPlus

def chiralOperatorExp (eta : ℝ) : M2C :=
  NormedSpace.exp ((eta : ℂ) • chiralGamma)

@[simp] theorem chiralProjectorPlus_sq :
    chiralProjectorPlus * chiralProjectorPlus = chiralProjectorPlus := by
  exact PPlus_idempotent

@[simp] theorem chiralProjectorMinus_sq :
    chiralProjectorMinus * chiralProjectorMinus = chiralProjectorMinus := by
  exact PMinus_idempotent

@[simp] theorem chiralProjectorPlus_mul_minus :
    chiralProjectorPlus * chiralProjectorMinus = 0 := by
  exact PPlus_PMinus_orthogonal

@[simp] theorem chiralProjectorMinus_mul_plus :
    chiralProjectorMinus * chiralProjectorPlus = 0 := by
  exact PMinus_PPlus_orthogonal

theorem chiralProjectorPlus_add_minus :
    chiralProjectorPlus + chiralProjectorMinus = (1 : M2C) := by
  exact PPlus_add_PMinus

theorem chiralProjectorPlus_sub_minus :
    chiralProjectorPlus - chiralProjectorMinus = chiralGamma := by
  exact PPlus_sub_PMinus

@[simp] theorem chiralGamma_sq :
    chiralGamma * chiralGamma = (1 : M2C) := by
  exact σ3c_sq

theorem chiralGamma_mul_plus :
    chiralGamma * chiralProjectorPlus = chiralProjectorPlus := by
  rw [chiralProjectorPlus, chiralGamma]
  rw [← Matrix.mul_assoc, σ3c_mul_σPlus]

theorem chiralGamma_mul_minus :
    chiralGamma * chiralProjectorMinus = -chiralProjectorMinus := by
  rw [chiralProjectorMinus, chiralGamma]
  rw [← Matrix.mul_assoc, σ3c_mul_σMinus]
  simp

theorem chiralOperatorExp_projector_decomposition (eta : ℝ) :
    chiralOperatorExp eta =
      (Real.exp eta : ℂ) • chiralProjectorPlus +
        (Real.exp (-eta) : ℂ) • chiralProjectorMinus := by
  unfold chiralOperatorExp chiralGamma chiralProjectorPlus
    chiralProjectorMinus
  rw [show ((eta : ℂ) • σ3c) =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then (eta : ℂ) else (-eta : ℂ)) by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [σ3c, Matrix.diagonal, Matrix.smul_apply]]
  rw [Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σPlus, σMinus, Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

end InfoGeometry.Physics.Cl11ChiralCARBridge
