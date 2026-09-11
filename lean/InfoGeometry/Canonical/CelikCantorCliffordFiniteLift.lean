import InfoGeometry.Canonical.CelikCantorCliffordUniversal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CelikCantorClifford
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Tactic

/-!
# Concrete finite Clifford lift for the rank-one Çelik Pauli packet

This file closes the first nontrivial instance of the native Clifford
universal property.  The Pauli pair `U,V` is assembled into a linear map on
`ℂ × ℂ`; its square is the standard sum-of-squares quadratic form, so
`CliffordAlgebra.lift` produces the actual algebra homomorphism.
-/

open scoped Matrix

namespace InfoGeometry.Canonical.CelikCantorClifford

abbrev RankOneCarrier : Type := ℂ × ℂ
abbrev RankOneMatrix : Type := Matrix (Fin 2) (Fin 2) ℂ

noncomputable def rankOneQuadratic : QuadraticForm ℂ RankOneCarrier :=
  QuadraticMap.sq.prod QuadraticMap.sq

@[simp] theorem rankOneQuadratic_apply (x : RankOneCarrier) :
    rankOneQuadratic x = x.1 ^ 2 + x.2 ^ 2 := by
  simp [rankOneQuadratic, QuadraticMap.prod_apply]
  ring

noncomputable def rankOneGenerator : RankOneCarrier →ₗ[ℂ] RankOneMatrix where
  toFun x := x.1 • U + x.2 • V
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, V, Matrix.add_apply] <;> ring
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, V, Matrix.smul_apply]

set_option maxHeartbeats 800000 in
theorem rankOneGenerator_sq (x : RankOneCarrier) :
    rankOneGenerator x * rankOneGenerator x =
      (rankOneQuadratic x) • (1 : RankOneMatrix) := by
  rcases x with ⟨a, b⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneGenerator, rankOneQuadratic_apply, U, V,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    ring

  theorem rankOneGenerator_square_preserving (x : RankOneCarrier) :
    rankOneGenerator x * rankOneGenerator x =
      (algebraMap ℂ RankOneMatrix) (rankOneQuadratic x) := by
  simpa [Algebra.algebraMap_eq_smul_one] using rankOneGenerator_sq x

noncomputable def rankOneCliffordLift :
    CliffordAlgebra rankOneQuadratic →ₐ[ℂ] RankOneMatrix :=
  CliffordAlgebra.lift rankOneQuadratic
    ⟨rankOneGenerator, rankOneGenerator_square_preserving⟩

@[simp] theorem rankOneCliffordLift_ι (x : RankOneCarrier) :
    rankOneCliffordLift (CliffordAlgebra.ι rankOneQuadratic x) =
      rankOneGenerator x := by
  exact CliffordAlgebra.lift_ι_apply
    rankOneGenerator rankOneGenerator_square_preserving x

theorem rankOneCliffordLift_ι_first :
    rankOneCliffordLift (CliffordAlgebra.ι rankOneQuadratic (1, 0)) = U := by
  rw [rankOneCliffordLift_ι]
  simp [rankOneGenerator, U, V]

theorem rankOneCliffordLift_ι_second :
    rankOneCliffordLift (CliffordAlgebra.ι rankOneQuadratic (0, 1)) = V := by
  rw [rankOneCliffordLift_ι]
  simp [rankOneGenerator, U, V]

theorem rankOneCliffordLift_unique
    {φ ψ : CliffordAlgebra rankOneQuadratic →ₐ[ℂ] RankOneMatrix}
    (h : ∀ x, φ (CliffordAlgebra.ι rankOneQuadratic x) =
      ψ (CliffordAlgebra.ι rankOneQuadratic x)) :
    φ = ψ := by
  exact cliffordAlgHom_unique_of_generator_eq h

end InfoGeometry.Canonical.CelikCantorClifford
