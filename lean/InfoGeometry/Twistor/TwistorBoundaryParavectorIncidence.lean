import InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Geometry.PauliParavectorKernelBoundary
import Mathlib.Tactic.FinCases

/-!
# Null paravectors and Penrose soldering incidence

This owner supplies the missing horizontal soldering layer between the
repository's concrete Minkowski `(1,3)` slice and the complex Penrose
incidence carrier.

The same real paravector is read as a Hermitian `2 × 2` Pauli/soldering
matrix.  Its determinant is exactly the Minkowski quadratic invariant, hence
nullness is equivalent to singularity and to the existence of a nonzero
spinor kernel.

The Penrose incidence relation is then the already established map
`π ↦ (i X(p) π, π)`.

Important: singularity of `X(p)` does not by itself imply that every incident
complex twistor is null for the separate diagonal `(2,2)` Hermitian form in
`PenroseTwistor`.  No such false implication is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence

open BigOperators
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Geometry.PauliParavectorKernelBoundary

/-- Convert the repository's `ℝ × ℝ³` Minkowski slice to the geometry-facing
four-vector carrier `(t,x,y,z)`. -/
def minkowski13ToMinkowski4 : Minkowski13 →ₗ[ℝ] Minkowski4 where
  toFun p := ![p.1, p.2 0, p.2 1, p.2 2]
  map_add' p q := by
    funext i
    fin_cases i <;> simp
  map_smul' r p := by
    funext i
    fin_cases i <;> simp

/-- Minkowski quadratic invariant on the concrete `Minkowski13` carrier. -/
def minkowski13Norm (p : Minkowski13) : ℝ :=
  p.1 ^ 2 - ∑ i : Fin 3, p.2 i ^ 2

@[simp] theorem minkowski13ToMinkowski4_q (p : Minkowski13) :
    (minkowski13ToMinkowski4 p).q = minkowski13Norm p := by
  simp [minkowski13ToMinkowski4, Minkowski4.q, Minkowski4.t, Minkowski4.x,
    Minkowski4.y, Minkowski4.z, minkowski13Norm, Fin.sum_univ_three]

/-- The same invariant is the restriction of the native split `Q55` form. -/
theorem minkowski13Norm_eq_Q55_slice (p : Minkowski13) :
    minkowski13Norm p =
      InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p) := by
  rw [Q55_minkowskiSlice]
  rfl

/-- The Hermitian Pauli matrix is the soldering matrix `X(p)`. -/
def paravectorToSolderingMatrix (p : Minkowski13) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  pauliMatrix (minkowski13ToMinkowski4 p)

/-- Determinant of the soldering matrix equals the Minkowski quadratic
invariant. -/
theorem det_solderingMatrix_eq_minkowski_norm (p : Minkowski13) :
    Matrix.det (paravectorToSolderingMatrix p) =
      ((minkowski13Norm p : ℝ) : ℂ) := by
  rw [paravectorToSolderingMatrix, det_pauliMatrix,
    minkowski13ToMinkowski4_q]

/-- Null predicate on the concrete `(1,3)` paravector carrier. -/
def IsNullParavector (p : Minkowski13) : Prop :=
  minkowski13Norm p = 0

/-- Null paravectors are exactly singular soldering matrices. -/
theorem null_paravector_iff_det_zero (p : Minkowski13) :
    IsNullParavector p ↔ Matrix.det (paravectorToSolderingMatrix p) = 0 := by
  rw [IsNullParavector, det_solderingMatrix_eq_minkowski_norm]
  norm_cast

/-- Penrose incidence map associated with the paravector soldering matrix. -/
def boundaryIncidenceLinearMap (p : Minkowski13) :
    Spinor2 →ₗ[ℂ] Twistor4 :=
  incidenceLinearMap (paravectorToSolderingMatrix p)

/-- The incidence relation as an intrinsic predicate on a twistor. -/
def IncidentBoundaryParavector (p : Minkowski13) (Z : Twistor4) : Prop :=
  boundaryIncidenceLinearMap p Z.2 = Z

@[simp] theorem boundaryIncidenceLinearMap_snd
    (p : Minkowski13) (π : Spinor2) :
    (boundaryIncidenceLinearMap p π).2 = π :=
  rfl

/-- Coordinate form of the soldering incidence equation
`ω = i X(p) π`. -/
theorem boundaryIncidenceLinearMap_fst_apply
    (p : Minkowski13) (π : Spinor2) (a : Fin 2) :
    (boundaryIncidenceLinearMap p π).1 a =
      Complex.I * Matrix.mulVec (paravectorToSolderingMatrix p) π a := by
  simp [boundaryIncidenceLinearMap, omegaLinearMap_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Intrinsic incidence is equivalent to the explicit soldering equation. -/
theorem incidentBoundaryParavector_iff
    (p : Minkowski13) (Z : Twistor4) :
    IncidentBoundaryParavector p Z ↔
      ∀ a : Fin 2,
        Z.1 a = Complex.I *
          Matrix.mulVec (paravectorToSolderingMatrix p) Z.2 a := by
  constructor
  · intro h a
    have hfst : (boundaryIncidenceLinearMap p Z.2).1 = Z.1 :=
      congrArg Prod.fst h
    have ha := congrFun hfst a
    rw [boundaryIncidenceLinearMap_fst_apply] at ha
    exact ha.symm
  · intro h
    apply Prod.ext
    · funext a
      rw [boundaryIncidenceLinearMap_fst_apply]
      exact (h a).symm
    · rfl

/-- Every spinor generates an incident twistor, exactly as in the existing
Penrose incidence plane. -/
theorem boundaryIncidence_is_incident
    (p : Minkowski13) (π : Spinor2) :
    IncidentBoundaryParavector p (boundaryIncidenceLinearMap p π) := by
  rfl

/-- A null paravector has a nonzero kernel spinor for its soldering matrix. -/
theorem exists_nonzero_soldering_kernel_spinor_of_null
    (p : Minkowski13) (hp : IsNullParavector p) :
    ∃ π : Spinor2, π ≠ 0 ∧
      Matrix.mulVec (paravectorToSolderingMatrix p) π = 0 := by
  let v : Minkowski4 := minkowski13ToMinkowski4 p
  have hvq : v.q = 0 := by
    simpa [v, IsNullParavector] using hp
  have hdet : Matrix.det (pauliMatrix v) = 0 := by
    rw [det_pauliMatrix, hvq]
    simp
  obtain ⟨π, hπ, hker⟩ :=
    exists_nonzero_mem_pauliKernel_of_det_zero v hdet
  refine ⟨π, hπ, ?_⟩
  have hop : pauliOperator v π = 0 := LinearMap.mem_ker.mp hker
  simpa [pauliOperator_apply, paravectorToSolderingMatrix, v] using hop

/-- For a kernel spinor the incident twistor has zero `ω` component. -/
theorem kernel_spinor_incidence_fst_zero
    (p : Minkowski13) (π : Spinor2)
    (hπ : Matrix.mulVec (paravectorToSolderingMatrix p) π = 0) :
    (boundaryIncidenceLinearMap p π).1 = 0 := by
  funext a
  rw [boundaryIncidenceLinearMap_fst_apply, congrFun hπ a]
  simp

/-- A nonzero kernel spinor therefore gives a nonzero incident twistor. -/
theorem exists_nonzero_incident_twistor_of_null
    (p : Minkowski13) (hp : IsNullParavector p) :
    ∃ π : Spinor2,
      π ≠ 0 ∧
      IncidentBoundaryParavector p (boundaryIncidenceLinearMap p π) ∧
      (boundaryIncidenceLinearMap p π).1 = 0 := by
  obtain ⟨π, hπ, hker⟩ :=
    exists_nonzero_soldering_kernel_spinor_of_null p hp
  exact ⟨π, hπ, boundaryIncidence_is_incident p π,
    kernel_spinor_incidence_fst_zero p π hker⟩

/-- On the concrete Minkowski slice, the paravector null equation is exactly
native `Q55` nullness. -/
theorem null_paravector_iff_Q55_slice_null (p : Minkowski13) :
    IsNullParavector p ↔
      InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p) = 0 := by
  rw [IsNullParavector, ← minkowski13Norm_eq_Q55_slice]

end InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence
