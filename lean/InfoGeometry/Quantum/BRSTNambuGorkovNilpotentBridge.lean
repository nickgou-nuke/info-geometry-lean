import Mathlib
import InfoGeometry.Quantum.MajoranaPfaffianNaturalClosure

open InfoGeometry.MajoranaPfaffianNaturalClosure

namespace InfoGeometry.Quantum.BRSTNambuGorkovNilpotentBridge

/-- A square-zero linear charge on a real vector space. -/
structure BRSTOperator (V : Type*) [AddCommGroup V] [Module ℝ V] where
  charge : V →ₗ[ℝ] V
  nilpotent : charge.comp charge = 0

namespace BRSTOperator

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A square-zero charge sends every vector to a cycle. -/
theorem charge_sq_zero
    (Q : BRSTOperator V) (v : V) :
    Q.charge (Q.charge v) = 0 := by
  exact LinearMap.congr_fun Q.nilpotent v

/-- The charge regarded as a linear map from states into cycles. -/
def chargeToCycles (Q : BRSTOperator V) :
    V →ₗ[ℝ] LinearMap.ker Q.charge where
  toFun v := ⟨Q.charge v, Q.charge_sq_zero v⟩
  map_add' x y := by ext; exact Q.charge.map_add x y
  map_smul' c x := by ext; exact Q.charge.map_smul c x

/-- Boundaries are the image of the charge inside the cycle subspace. -/
def boundaries (Q : BRSTOperator V) :
    Submodule ℝ (LinearMap.ker Q.charge) :=
  LinearMap.range Q.chargeToCycles

/-- BRST cohomology is cycles modulo boundaries. -/
abbrev Cohomology (Q : BRSTOperator V) :=
  Submodule.Quotient Q.boundaries

end BRSTOperator

/-- The two-component real carrier for the concrete CAR charge. -/
abbrev NambuSpace : Type := Fin 2 → ℝ

/-- The linear charge induced by the nilpotent CAR annihilation matrix. -/
def boundaryBRSTCharge : NambuSpace →ₗ[ℝ] NambuSpace :=
  Matrix.mulVecLin annihilationR

/-- The concrete CAR charge squares to zero. -/
theorem boundary_brst_nilpotent :
    boundaryBRSTCharge.comp boundaryBRSTCharge = 0 := by
  dsimp [boundaryBRSTCharge]
  rw [← Matrix.mulVecLin_mul, annihilationR_sq, Matrix.mulVecLin_zero]

/-- The concrete square-zero BRST operator. -/
def boundaryBRSTOperator : BRSTOperator NambuSpace where
  charge := boundaryBRSTCharge
  nilpotent := boundary_brst_nilpotent

/-- For the concrete two-component CAR charge, every cycle is a boundary. -/
theorem boundary_range_eq_ker :
    LinearMap.range boundaryBRSTCharge =
      LinearMap.ker boundaryBRSTCharge := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun boundary_brst_nilpotent x
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    have hv1 : v 1 = 0 := by
      have h := congrFun hv 0
      simpa [boundaryBRSTCharge, Matrix.mulVecLin_apply, Matrix.mulVec,
        dotProduct, annihilationR, Fin.sum_univ_two] using h
    let x : NambuSpace := fun i => if i = 1 then v 0 else 0
    refine ⟨x, ?_⟩
    ext i
    fin_cases i <;>
      simp [boundaryBRSTCharge, Matrix.mulVec, dotProduct, annihilationR, x, hv1]

/-- The native cohomology type of the concrete CAR charge. -/
abbrev BoundaryBRSTCohomology :=
  BRSTOperator.Cohomology boundaryBRSTOperator

end InfoGeometry.Quantum.BRSTNambuGorkovNilpotentBridge
