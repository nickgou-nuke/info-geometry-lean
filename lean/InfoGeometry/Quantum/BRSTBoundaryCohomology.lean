import Mathlib
import InfoGeometry.Quantum.MajoranaPfaffianNaturalClosure

/-!
# BRST Cohomology of a Square-Zero CAR Charge

This module constructs cohomology as cycles modulo boundaries for an arbitrary
square-zero real linear map.  It then computes the concrete two-component
complex induced by the CAR annihilation matrix.

No Majorana operator is claimed to be nilpotent: the differential is the
nilpotent CAR annihilation operator `annihilationR`.
-/

open InfoGeometry.MajoranaPfaffianNaturalClosure

namespace InfoGeometry.Quantum.BRSTBoundaryCohomology

/-- A square-zero real linear differential. -/
structure SquareZeroDifferential (V : Type*) [AddCommGroup V] [Module ℝ V] where
  d : V →ₗ[ℝ] V
  sq_zero : d.comp d = 0

namespace SquareZeroDifferential

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Applying a square-zero differential twice gives zero. -/
theorem apply_sq_zero (D : SquareZeroDifferential V) (v : V) :
    D.d (D.d v) = 0 := by
  exact LinearMap.congr_fun D.sq_zero v

/-- The differential as a linear map from states into its cycle subspace. -/
def toCycles (D : SquareZeroDifferential V) :
    V →ₗ[ℝ] LinearMap.ker D.d where
  toFun v := ⟨D.d v, D.apply_sq_zero v⟩
  map_add' x y := by ext; exact D.d.map_add x y
  map_smul' c x := by ext; exact D.d.map_smul c x

/-- Boundaries as the range of the differential inside the cycle subspace. -/
def boundaries (D : SquareZeroDifferential V) :
    Submodule ℝ (LinearMap.ker D.d) :=
  LinearMap.range D.toCycles

/-- Cohomology is the quotient of cycles by boundaries. -/
abbrev Cohomology (D : SquareZeroDifferential V) :=
  (LinearMap.ker D.d) ⧸ D.boundaries

end SquareZeroDifferential

/-- The concrete two-component real CAR carrier. -/
abbrev NambuSpace := Fin 2 → ℝ

/-- The linear differential induced by the CAR annihilation matrix. -/
def carCharge : NambuSpace →ₗ[ℝ] NambuSpace :=
  Matrix.mulVecLin annihilationR

/-- The concrete CAR differential squares to zero. -/
theorem carCharge_sq_zero :
    carCharge.comp carCharge = 0 := by
  dsimp [carCharge]
  rw [← Matrix.mulVecLin_mul, annihilationR_sq, Matrix.mulVecLin_zero]

/-- The concrete CAR differential as a square-zero complex. -/
def carDifferential : SquareZeroDifferential NambuSpace where
  d := carCharge
  sq_zero := carCharge_sq_zero

/-- For the two-component CAR differential, every cycle is a boundary. -/
theorem carCharge_range_eq_ker :
    LinearMap.range carCharge = LinearMap.ker carCharge := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun carCharge_sq_zero x
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    have hv1 : v 1 = 0 := by
      have h := congrFun hv 0
      simpa [carCharge, Matrix.mulVecLin_apply, Matrix.mulVec,
        dotProduct, annihilationR, Fin.sum_univ_two] using h
    let x : NambuSpace := fun i => if i = 1 then v 0 else 0
    refine ⟨x, ?_⟩
    ext i
    fin_cases i <;>
      simp [carCharge, Matrix.mulVec, dotProduct, annihilationR, x, hv1]

/-- The boundary submodule fills the concrete cycle subspace. -/
theorem car_boundaries_eq_top :
    carDifferential.boundaries = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro z _
    rcases z with ⟨v, hv⟩
    have hrange : v ∈ LinearMap.range carCharge := by
      rw [carCharge_range_eq_ker]
      exact hv
    rcases hrange with ⟨w, hw⟩
    exact ⟨w, Subtype.ext hw⟩

/-- The cohomology of the concrete two-component CAR differential. -/
abbrev CARBoundaryCohomology :=
  carDifferential.Cohomology

/-- The concrete two-component CAR cohomology has exactly one class. -/
theorem carBoundaryCohomology_subsingleton :
    Subsingleton CARBoundaryCohomology := by
  unfold CARBoundaryCohomology SquareZeroDifferential.Cohomology
  rw [car_boundaries_eq_top]
  infer_instance

end InfoGeometry.Quantum.BRSTBoundaryCohomology
