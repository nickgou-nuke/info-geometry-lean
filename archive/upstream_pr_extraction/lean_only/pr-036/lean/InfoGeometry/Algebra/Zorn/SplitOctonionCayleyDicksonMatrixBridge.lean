import InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Cayley--Dickson/Witt dictionary for the split-octonion carrier

This is a composition bridge over the existing `SplitQuaternionCore` and
`SplitOctonionWittPlanes` owners.  It does not install an associative matrix
algebra structure on the full split-octonion carrier.
-/

namespace InfoGeometry.Algebra.Zorn.SplitOctonionCayleyDicksonMatrixBridge

open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev Carrier := InfoGeometry.Algebra.Zorn.SplitQuaternionCore.CZ

abbrev quaternionBasisUnit (a : Fin 4) : Carrier :=
  InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.quaternionBasis a

abbrev ellBasisUnit (a : Fin 4) : Carrier :=
  InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.ellBasis a

theorem quaternion_basis_square (a : Fin 4) :
    zMul (quaternionBasisUnit a) (quaternionBasisUnit a) =
      if a = 0 then 1 else -1 := by
  fin_cases a
  · exact one_zMul 1
  · exact i_sq
  · exact j_sq
  · exact kQuaternion_sq

theorem ell_lift_square (a : Fin 4) :
    zMul (ellBasisUnit a) (ellBasisUnit a) = 1 := by
  fin_cases a
  · change zMul (zMul lUnit 1) (zMul lUnit 1) = 1
    rw [zMul_one]
    exact l_sq
  · ext i <;>
      simp [ellBasis, quaternionBasis, iUnit, lUnit, zMul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    all_goals (try fin_cases i) <;> norm_num
  · ext i <;>
      simp [ellBasis, quaternionBasis, jUnit, lUnit, zMul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    all_goals (try fin_cases i) <;> norm_num
  · ext i <;>
      simp [ellBasis, quaternionBasis, kQuaternionUnit, lUnit, zMul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    all_goals (try fin_cases i) <;> norm_num

theorem split_octonion_basis_square_packet :
    zMul (quaternionBasisUnit 0) (quaternionBasisUnit 0) = 1 ∧
    zMul (quaternionBasisUnit 1) (quaternionBasisUnit 1) = -1 ∧
    zMul (quaternionBasisUnit 2) (quaternionBasisUnit 2) = -1 ∧
    zMul (quaternionBasisUnit 3) (quaternionBasisUnit 3) = -1 ∧
    (∀ a : Fin 4,
      zMul (ellBasisUnit a) (ellBasisUnit a) = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ell_lift_square⟩
  · exact one_zMul 1
  · exact i_sq
  · exact j_sq
  · exact kQuaternion_sq

theorem split_quaternion_slice_associative
    (X Y Z : Carrier)
    (hX : X ∈ coreSubmodule) (hY : Y ∈ coreSubmodule)
    (hZ : Z ∈ coreSubmodule) :
    zMul (zMul X Y) Z = zMul X (zMul Y Z) :=
  InfoGeometry.Algebra.Zorn.SplitQuaternionCore.assoc X Y Z hX hY hZ

theorem full_carrier_has_nonzero_associator :
    ∃ X Y Z : InfoGeometry.Algebra.ZornVectorMatrix ℝ,
      InfoGeometry.Algebra.ZornVectorMatrix.associator X Y Z ≠ 0 := by
  exact ⟨InfoGeometry.Algebra.ZornVectorMatrix.U 0,
    InfoGeometry.Algebra.ZornVectorMatrix.U 1,
    InfoGeometry.Algebra.ZornVectorMatrix.U 2,
    InfoGeometry.Algebra.ZornVectorMatrix.associator_U_zero_U_one_U_two_ne_zero⟩

end InfoGeometry.Algebra.Zorn.SplitOctonionCayleyDicksonMatrixBridge
