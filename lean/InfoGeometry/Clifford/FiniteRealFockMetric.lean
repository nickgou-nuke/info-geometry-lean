/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FockTailExteriorBasis
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Finite real metric on the native exterior-Fock carrier

Named induced structures are activated locally only.
The tail linear isometry is derived from the accepted exterior basis transport,
not from the zero-quadratic isometry. No scalar extension or completion.
-/

noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

/-- Coordinates in the exact exterior basis, with the finite l2 target norm. -/
def fockCoordinates (n : ℕ) :
    InfoGeometry.Clifford.SpinorSpace (Vector n) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Finset (Fin n)) :=
  (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra.equivFun.trans
    (WithLp.linearEquiv 2 ℝ (Finset (Fin n) → ℝ)).symm

@[simp] theorem fockCoordinates_apply (n : ℕ)
    (x : InfoGeometry.Clifford.SpinorSpace (Vector n)) (S : Finset (Fin n)) :
    fockCoordinates n x S = (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra.equivFun x S := rfl

/-- Pullback of the Euclidean norm through the injective native basis coordinates. -/
abbrev fockNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (InfoGeometry.Clifford.SpinorSpace (Vector n)) :=
  NormedAddCommGroup.induced _ _ (fockCoordinates n).toLinearMap
    (fockCoordinates n).injective

attribute [local instance] fockNormedAddCommGroup

/-- Pullback of the real Euclidean inner product, using the same induced norm. -/
abbrev fockInnerProductSpace (n : ℕ) :
    InnerProductSpace ℝ (InfoGeometry.Clifford.SpinorSpace (Vector n)) :=
  InnerProductSpace.induced (fockCoordinates n).toLinearMap

attribute [local instance] fockInnerProductSpace

/-- The metric is exactly the coordinate l2 metric. -/
theorem fock_norm_eq_coordinates (n : ℕ)
    (x : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    ‖x‖ = ‖fockCoordinates n x‖ := rfl

/-- The pulled-back inner product is the finite sum in the exact exterior basis. -/
theorem fock_inner_eq_sum (n : ℕ)
    (x y : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    inner ℝ x y = ∑ S : Finset (Fin n),
      (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra.equivFun x S *
      (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra.equivFun y S := by
  change inner ℝ (fockCoordinates n x) (fockCoordinates n y) = _
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, fockCoordinates_apply]

/-- The actual exterior basis is orthonormal for this induced metric. -/
theorem fock_exteriorBasis_inner (n : ℕ) (S T : Finset (Fin n)) :
    inner ℝ ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S)
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra T) =
        if S = T then 1 else 0 := by
  rw [fock_inner_eq_sum]
  simp [Module.Basis.equivFun_self]

/-- Inner-product preservation on two basis vectors uses the actual tail transport. -/
theorem fockTailMap_inner_basis (n : ℕ) (S T : Finset (Fin n)) :
    inner ℝ
      (fockTailMap n ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S))
      (fockTailMap n ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra T)) =
    inner ℝ ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S)
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra T) := by
  rw [fockTailMap_exteriorBasis, fockTailMap_exteriorBasis,
    fock_exteriorBasis_inner, fock_exteriorBasis_inner]
  simp only [(Finset.map_injective (Fin.succEmb n)).eq_iff]

/-- The native tail map preserves the positive real inner product on all vectors. -/
theorem fockTailMap_inner (n : ℕ)
    (x y : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    inner ℝ (fockTailMap n x) (fockTailMap n y) = inner ℝ x y := by
  let b := (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [b, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, fockTailMap_inner_basis]

/-- Hilbert-metric linear isometry with the exact native algebraic tail map. -/
def fockTailLinearIsometry (n : ℕ) :
    InfoGeometry.Clifford.SpinorSpace (Vector n) →ₗᵢ[ℝ]
      InfoGeometry.Clifford.SpinorSpace (Vector (n + 1)) :=
  (fockTailMap n).toLinearMap.isometryOfInner (fockTailMap_inner n)

@[simp] theorem fockTailLinearIsometry_apply (n : ℕ)
    (x : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    fockTailLinearIsometry n x = fockTailMap n x := rfl

/-- Norm preservation is for the induced positive metric, not the zero quadratic form. -/
theorem fockTailMap_norm (n : ℕ)
    (x : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    ‖fockTailMap n x‖ = ‖x‖ :=
  (fockTailLinearIsometry n).norm_map x

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
