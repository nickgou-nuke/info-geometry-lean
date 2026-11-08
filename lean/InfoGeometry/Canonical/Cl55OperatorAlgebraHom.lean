import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OperatorTKKAnomalyAnnihilation

/-!
# Functoriality of the operator Cl(5,5) boundary packet

The finite boundary relations are preserved by native algebra homomorphisms.
This is the algebraic stage needed before projecting the packet through a
categorical direct colimit: no limit, topology, or scalar realization is
introduced here.
-/

variable {A B : Type*} [Ring A] [Ring B]

namespace NoncommutativeGeometry

open InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary

theorem map_lie_bracket [Algebra ℚ A] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) (x y : A) :
    φ (lie_bracket x y) = lie_bracket (φ x) (φ y) := by
  simp only [lie_bracket, map_sub, map_mul]

theorem ringHom_map_lie_bracket (φ : A →+* B) (x y : A) :
    φ (lie_bracket x y) = lie_bracket (φ x) (φ y) := by
  simp only [lie_bracket, map_sub, map_mul]

theorem ringHom_map_operatorCl55 (e f : Fin 5 → A)
    [hCl : OperatorCl55 e f] [Algebra ℚ B] (φ : A →+* B) :
    OperatorCl55 (fun i => φ (e i)) (fun i => φ (f i)) := by
  constructor
  · intro i
    have h := congrArg φ (hCl.e_sq i)
    simpa only [map_mul, map_one] using h
  · intro i
    have h := congrArg φ (hCl.f_sq i)
    simpa only [map_mul, map_neg, map_one] using h
  · intro i j hij
    have h := congrArg φ (hCl.e_anti i j hij)
    simpa only [map_add, map_mul, map_zero] using h
  · intro i j hij
    have h := congrArg φ (hCl.f_anti i j hij)
    simpa only [map_add, map_mul, map_zero] using h
  · intro i j
    have h := congrArg φ (hCl.ef_anti i j)
    simpa only [map_add, map_mul, map_zero] using h

variable [Algebra ℚ A]

theorem map_boundary_annihilator_sq (e f : Fin 5 → A)
    [hCl : OperatorCl55 e f] [Algebra ℚ B] (φ : A →ₐ[ℚ] B) :
    φ (boundaryAnnihilator e f) * φ (boundaryAnnihilator e f) = 0 := by
  have h := congrArg φ (boundaryAnnihilator_sq (e := e) (f := f))
  simpa only [map_mul, map_zero] using h

theorem map_boundary_creator_sq (e f : Fin 5 → A)
    [hCl : OperatorCl55 e f] [Algebra ℚ B] (φ : A →ₐ[ℚ] B) :
    φ (boundaryCreator e f) * φ (boundaryCreator e f) = 0 := by
  have h := congrArg φ (boundaryCreator_sq (e := e) (f := f))
  simpa only [map_mul, map_zero] using h

theorem map_boundary_car (e f : Fin 5 → A)
    [hCl : OperatorCl55 e f] [Algebra ℚ B] (φ : A →ₐ[ℚ] B) :
    φ (boundaryAnnihilator e f) * φ (boundaryCreator e f) +
        φ (boundaryCreator e f) * φ (boundaryAnnihilator e f) = 1 := by
  have h := congrArg φ (projective_compensation_anticomm (e := e) (f := f))
  simpa only [map_add, map_mul, map_one] using h

theorem map_boundary_tkk_scale (e f : Fin 5 → A)
    [hCl : OperatorCl55 e f] [Algebra ℚ B] (φ : A →ₐ[ℚ] B) :
    φ (lie_bracket (lie_bracket (boundaryAnnihilator e f)
      (boundaryCreator e f)) (boundaryAnnihilator e f)) =
      φ (boundaryAnnihilator e f + boundaryAnnihilator e f) := by
  exact congrArg φ (projective_boundary_tkk_scale_symmetry (e := e) (f := f))

theorem map_boundary_tkk_scale_readout (e f : Fin 5 → A)
    [hCl : OperatorCl55 e f] [Algebra ℚ B] (φ : A →ₐ[ℚ] B) :
    lie_bracket (lie_bracket (φ (boundaryAnnihilator e f))
      (φ (boundaryCreator e f))) (φ (boundaryAnnihilator e f)) =
      φ (boundaryAnnihilator e f) + φ (boundaryAnnihilator e f) := by
  rw [← map_lie_bracket, ← map_lie_bracket]
  simpa only [map_add] using
    congrArg φ (projective_boundary_tkk_scale_symmetry (e := e) (f := f))

theorem ringHom_map_boundary_annihilator_sq (e f : Fin 5 → A)
    [hCl : OperatorCl55 e f] (φ : A →+* B) :
    φ (boundaryAnnihilator e f) * φ (boundaryAnnihilator e f) = 0 := by
  have h := congrArg φ (boundaryAnnihilator_sq (e := e) (f := f))
  simpa only [map_mul, map_zero] using h

theorem ringHom_map_boundary_creator_sq (e f : Fin 5 → A)
    [hCl : OperatorCl55 e f] (φ : A →+* B) :
    φ (boundaryCreator e f) * φ (boundaryCreator e f) = 0 := by
  have h := congrArg φ (boundaryCreator_sq (e := e) (f := f))
  simpa only [map_mul, map_zero] using h

theorem ringHom_map_boundary_car (e f : Fin 5 → A)
    [hCl : OperatorCl55 e f] (φ : A →+* B) :
    φ (boundaryAnnihilator e f) * φ (boundaryCreator e f) +
        φ (boundaryCreator e f) * φ (boundaryAnnihilator e f) = 1 := by
  have h := congrArg φ (projective_compensation_anticomm (e := e) (f := f))
  simpa only [map_add, map_mul, map_one] using h

theorem ringHom_map_boundary_tkk_scale (e f : Fin 5 → A)
    [hCl : OperatorCl55 e f] (φ : A →+* B) :
    lie_bracket (lie_bracket (φ (boundaryAnnihilator e f))
      (φ (boundaryCreator e f))) (φ (boundaryAnnihilator e f)) =
      φ (boundaryAnnihilator e f) + φ (boundaryAnnihilator e f) := by
  rw [← ringHom_map_lie_bracket, ← ringHom_map_lie_bracket]
  simpa only [map_add] using
    congrArg φ (projective_boundary_tkk_scale_symmetry (e := e) (f := f))

end NoncommutativeGeometry
