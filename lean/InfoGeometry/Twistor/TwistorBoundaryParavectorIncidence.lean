import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
import InfoGeometry.Twistor.PenroseIncidence

/-!
# Minkowski paravector--Penrose incidence adapter

This file only connects the existing `(1,3)` slice and Pauli owner to the
existing complex Penrose incidence owner.  It does not identify ordinary
incidence with the Hermitian projective-null predicate.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence

open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Twistor.PenroseIncidence

def minkowski13ToMinkowski4 : Minkowski13 →ₗ[ℝ] Minkowski4 where
  toFun p := ⟨p.1, p.2 0, p.2 1, p.2 2⟩
  map_add' p q := by
    apply Minkowski4.ext <;> rfl
  map_smul' a p := by
    apply Minkowski4.ext <;> rfl

theorem minkowski13ToMinkowski4_apply (p : Minkowski13) :
    minkowski13ToMinkowski4 p = ⟨p.1, p.2 0, p.2 1, p.2 2⟩ := rfl

def paravectorQuadratic (p : Minkowski13) : ℝ :=
  p.1 ^ 2 - ∑ i : Fin 3, p.2 i ^ 2

@[simp] theorem paravectorQuadratic_eq_minkowski4_q (p : Minkowski13) :
    paravectorQuadratic p = Minkowski4.q (minkowski13ToMinkowski4 p) := by
  rw [minkowski13ToMinkowski4_apply]
  simp [paravectorQuadratic, Minkowski4.q, Fin.sum_univ_succ]
  ring_nf

def paravectorToSolderingMatrix (p : Minkowski13) : PauliMat :=
  pauliMatrix (minkowski13ToMinkowski4 p)

@[simp] theorem det_paravectorToSolderingMatrix (p : Minkowski13) :
    Matrix.det (paravectorToSolderingMatrix p) =
      ((paravectorQuadratic p : ℝ) : ℂ) := by
  rw [paravectorToSolderingMatrix, det_pauliMatrix,
    paravectorQuadratic_eq_minkowski4_q]

theorem null_paravector_iff_det_zero (p : Minkowski13) :
    paravectorQuadratic p = 0 ↔
      Matrix.det (paravectorToSolderingMatrix p) = 0 := by
  rw [det_paravectorToSolderingMatrix]
  exact Complex.ofReal_eq_zero.symm

theorem null_paravector_iff_nontrivial_kernel (p : Minkowski13) :
    paravectorQuadratic p = 0 ↔
      ∃ ψ : Spinor2, ψ ≠ 0 ∧
        Matrix.mulVec (paravectorToSolderingMatrix p) ψ = 0 := by
  rw [null_paravector_iff_det_zero, paravectorToSolderingMatrix]
  exact Matrix.exists_mulVec_eq_zero_iff.symm

def boundaryIncidenceLinearMap (p : Minkowski13) :
    Spinor2 →ₗ[ℂ] Twistor4 :=
  incidenceLinearMap (paravectorToSolderingMatrix p)

@[simp] theorem boundaryIncidenceLinearMap_apply
    (p : Minkowski13) (ψ : Spinor2) :
    boundaryIncidenceLinearMap p ψ =
      (Complex.I • Matrix.mulVec (paravectorToSolderingMatrix p) ψ, ψ) := by
  rfl

def IncidentBoundaryParavector (p : Minkowski13) (Z : Twistor4) : Prop :=
  ∃ ψ : Spinor2, Z = boundaryIncidenceLinearMap p ψ

theorem incident_boundary_exists_of_kernel
    {p : Minkowski13} (hp : paravectorQuadratic p = 0) :
    ∃ Z : Twistor4, IncidentBoundaryParavector p Z ∧ Z.2 ≠ 0 := by
  rcases (null_paravector_iff_nontrivial_kernel p).mp hp with ⟨ψ, hψ, hker⟩
  refine ⟨boundaryIncidenceLinearMap p ψ, ⟨ψ, rfl⟩, ?_⟩
  exact hψ

theorem incident_boundary_kernel_spinor
    {p : Minkowski13} {ψ : Spinor2}
    (hker : Matrix.mulVec (paravectorToSolderingMatrix p) ψ = 0) :
    boundaryIncidenceLinearMap p ψ = (0, ψ) := by
  simp [boundaryIncidenceLinearMap, incidenceLinearMap, hker]

end InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence
