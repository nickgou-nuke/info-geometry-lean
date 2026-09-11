import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.AZTenFoldCompleteClassification

open InfoGeometry.Quantum.AZTenFoldCompleteClassification

namespace InfoGeometry.Quantum.BRSTNambuGorkovNilpotentBridge

/-!
A BRST charge is exactly a square-zero linear endomorphism.  The subtype is
the native proof-carrying carrier; `charge` and `nilpotent` below preserve the
old projection API.
-/
def BRSTOperator (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  {charge : V →ₗ[ℝ] V // charge.comp charge = 0}

namespace BRSTOperator

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev charge (Q : BRSTOperator V) : V →ₗ[ℝ] V :=
  Q.1

theorem nilpotent (Q : BRSTOperator V) : Q.charge.comp Q.charge = 0 :=
  Q.2

def mk (charge : V →ₗ[ℝ] V) (nilpotent : charge.comp charge = 0) :
    BRSTOperator V :=
  ⟨charge, nilpotent⟩

end BRSTOperator

/-- Theorem: For any BRST operator Q, Q(Q(v)) = 0 -/
theorem brst_charge_sq_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : BRSTOperator V) (v : V) :
    Q.charge (Q.charge v) = 0 := by
  have h := LinearMap.congr_fun Q.nilpotent v
  exact h

/-- 2D Nambu-Gor'kov Matrix Space -/
abbrev NambuSpace : Type := InfoGeometry.Algebra.FiniteSpin.Vec2R

/-- The 2D Boundary Majorana BRST Charge Operator -/
def boundaryBRSTCharge : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.mulVecLin boundaryNilpotentMajorana

/-- Theorem: The Boundary Majorana BRST charge is strictly Nilpotent (Q_BRST² = 0) -/
theorem boundary_brst_nilpotent :
    boundaryBRSTCharge.comp boundaryBRSTCharge = 0 := by
  dsimp [boundaryBRSTCharge]
  rw [← Matrix.mulVecLin_mul, boundary_majorana_nilpotent, Matrix.mulVecLin_zero]

/-- The Boundary Majorana BRST Instance -/
def boundaryBRSTOperator : BRSTOperator NambuSpace :=
  BRSTOperator.mk boundaryBRSTCharge boundary_brst_nilpotent

/-- Theorem: Image of BRST charge is contained in the Kernel (im Q ⊆ ker Q) -/
theorem brst_im_subset_ker {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : BRSTOperator V) (v : V) :
    Q.charge (Q.charge v) = 0 :=
  brst_charge_sq_zero Q v

theorem brst_nambu_gorkov_bridge_exists :
    boundaryBRSTCharge.comp boundaryBRSTCharge = 0 ∧
      boundaryNilpotentMajorana * boundaryNilpotentMajorana = 0 := by
  exact ⟨boundary_brst_nilpotent, boundary_majorana_nilpotent⟩

end InfoGeometry.Quantum.BRSTNambuGorkovNilpotentBridge
