import InfoGeometry.Clifford.Cl55SpinorRepresentationGeneration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.CliffordTower
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank
open InfoGeometry.Clifford.SpinorRep
open scoped TensorProduct

noncomputable section

private noncomputable def splitOneToPair :
    InfoGeometry.CliffordTower.SplitSpace 1 ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun := fun x => x.1
  invFun := fun x => (x, 0)
  left_inv := by
    intro x
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.elim0 i
  right_inv := by
    intro x
    rfl
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro r x
    rfl

private noncomputable def splitOneToPairIsometry :
    QuadraticMap.IsometryEquiv (Qsplit 1)
      InfoGeometry.CliffordTower.Q11 where
  toLinearEquiv := splitOneToPair
  map_app' := by
    intro x
    simp [splitOneToPair, Qsplit,
      InfoGeometry.CliffordTower.Q11,
      InfoGeometry.Clifford.Cl11Matrix.q11,
      InfoGeometry.Clifford.splitQ11_apply]

private noncomputable def splitCl11Equiv :
    SplitClNNAlg 1 ≃ₐ[ℝ]
      CliffordAlgebra InfoGeometry.CliffordTower.Q11 :=
  CliffordAlgebra.equivOfIsometry splitOneToPairIsometry

theorem splitClNNAlg_finrank_one :
    Module.finrank ℝ (SplitClNNAlg 1) = 4 := by
  rw [splitCl11Equiv.toLinearEquiv.finrank_eq]
  have hq : InfoGeometry.CliffordTower.Q11 =
      InfoGeometry.Clifford.Cl11Matrix.q11 := by
    ext v
    simp [InfoGeometry.CliffordTower.Q11,
      InfoGeometry.Clifford.Cl11Matrix.q11,
      InfoGeometry.Clifford.splitQ11_apply,
      CliffordAlgebraQuaternion.Q]
    ring
  rw [hq]
  exact InfoGeometry.Clifford.Cl11Matrix.finrank_cl11

theorem splitClNNAlg_finrank_four :
    Module.finrank ℝ (SplitClNNAlg 4) = 256 := by
  calc
    Module.finrank ℝ (SplitClNNAlg 4) =
        4 * Module.finrank ℝ (SplitClNNAlg 3) := by
      simpa using splitClNNAlg_finrank_succ 3
    _ = 4 * (4 * Module.finrank ℝ (SplitClNNAlg 2)) := by
      rw [splitClNNAlg_finrank_succ 2]
    _ = 4 * (4 * (4 * Module.finrank ℝ (SplitClNNAlg 1))) := by
      rw [splitClNNAlg_finrank_succ 1]
    _ = 256 := by
      rw [splitClNNAlg_finrank_one]

theorem splitClNNAlg_finrank_five :
    Module.finrank ℝ (SplitClNNAlg 5) = 1024 := by
  calc
    Module.finrank ℝ (SplitClNNAlg 5) =
        4 * Module.finrank ℝ (SplitClNNAlg 4) := by
      simpa using splitClNNAlg_finrank_succ 4
    _ = 4 * (4 * Module.finrank ℝ (SplitClNNAlg 3)) := by
      rw [splitClNNAlg_finrank_succ 3]
    _ = 4 * (4 * (4 * Module.finrank ℝ (SplitClNNAlg 2))) := by
      rw [splitClNNAlg_finrank_succ 2]
    _ = 4 * (4 * (4 * (4 * Module.finrank ℝ (SplitClNNAlg 1)))) := by
      rw [splitClNNAlg_finrank_succ 1]
    _ = 1024 := by
      rw [splitClNNAlg_finrank_one]


theorem splitClNNAlg_finiteDimensional_five :
    FiniteDimensional ℝ (SplitClNNAlg 5) := by
  letI : FiniteDimensional ℝ
      (CliffordAlgebra InfoGeometry.CliffordTower.Q11) := by
    have hq : InfoGeometry.CliffordTower.Q11 =
        InfoGeometry.Clifford.Cl11Matrix.q11 := by
      ext v
      simp [InfoGeometry.CliffordTower.Q11,
        InfoGeometry.Clifford.Cl11Matrix.q11,
        InfoGeometry.Clifford.splitQ11_apply,
        CliffordAlgebraQuaternion.Q]
      ring
    rw [hq]
    exact LinearEquiv.finiteDimensional
      InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.toLinearEquiv.symm
  have gradedFinite (n : ℕ) [FiniteDimensional ℝ (SplitClNNAlg n)] :
      FiniteDimensional ℝ (SplitClNNTensorStep n) := by
    let e : SplitClNNTensorStep n ≃ₗ[ℝ]
        TensorProduct ℝ
          (CliffordAlgebra InfoGeometry.CliffordTower.Q11)
          (CliffordAlgebra (Qsplit n)) :=
      (GradedTensorProduct.of ℝ
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (CliffordAlgebra.evenOdd (Qsplit n))).symm
    exact LinearEquiv.finiteDimensional e.symm
  letI : FiniteDimensional ℝ (SplitClNNAlg 1) := by
    exact LinearEquiv.finiteDimensional splitCl11Equiv.symm.toLinearEquiv
  letI : FiniteDimensional ℝ (SplitClNNTensorStep 1) := gradedFinite 1
  letI : FiniteDimensional ℝ (SplitClNNAlg 2) := by
    exact LinearEquiv.finiteDimensional
      (splitCliffordTensorStepEquiv 1).symm.toLinearEquiv
  letI : FiniteDimensional ℝ (SplitClNNTensorStep 2) := gradedFinite 2
  letI : FiniteDimensional ℝ (SplitClNNAlg 3) := by
    exact LinearEquiv.finiteDimensional
      (splitCliffordTensorStepEquiv 2).symm.toLinearEquiv
  letI : FiniteDimensional ℝ (SplitClNNTensorStep 3) := gradedFinite 3
  letI : FiniteDimensional ℝ (SplitClNNAlg 4) := by
    exact LinearEquiv.finiteDimensional
      (splitCliffordTensorStepEquiv 3).symm.toLinearEquiv
  letI : FiniteDimensional ℝ (SplitClNNTensorStep 4) := gradedFinite 4
  exact LinearEquiv.finiteDimensional
    (splitCliffordTensorStepEquiv 4).symm.toLinearEquiv

theorem cl55_finrank :
    Module.finrank ℝ Cl55 = 1024 := by
  rw [cl55ToSplitCl55.toLinearEquiv.finrank_eq]
  exact splitClNNAlg_finrank_five

theorem spinorMatrix_finrank :
    Module.finrank ℝ (SpinorMatrix 5) = 1024 := by
  simp [SpinorMatrix, Module.finrank_matrix]

noncomputable def cl55SpinorAlgEquiv :
    Cl55 ≃ₐ[ℝ] SpinorMatrix 5 :=
  letI : FiniteDimensional ℝ (SplitClNNAlg 5) :=
    splitClNNAlg_finiteDimensional_five
  letI : FiniteDimensional ℝ Cl55 :=
    LinearEquiv.finiteDimensional cl55ToSplitCl55.toLinearEquiv.symm
  cl55SpinorAlgEquiv_of_surjective
    cl55SpinorRepresentation_surjective (by
      rw [cl55_finrank, spinorMatrix_finrank])

theorem cl55SpinorAlgEquiv_toAlgHom_eq_representation :
    cl55SpinorAlgEquiv.toAlgHom = cl55SpinorRepresentation := by
  change (AlgEquiv.ofBijective cl55SpinorRepresentation _).toAlgHom =
    cl55SpinorRepresentation
  rfl

theorem realSplitPinSpinorUnitRepresentation_injective :
    Function.Injective realSplitPinSpinorUnitRepresentation := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  have hcoe := congrArg
      (fun u : (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ =>
        (u : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)) hgh
  have hrep :
      cl55SpinorRepresentation ((g : Cl55ˣ) : Cl55) =
        cl55SpinorRepresentation ((h : Cl55ˣ) : Cl55) := by
    simpa only [realSplitPinSpinorUnitRepresentation_coe] using hcoe
  exact cl55SpinorAlgEquiv.injective (by
    simpa only [cl55SpinorAlgEquiv_toAlgHom_eq_representation] using hrep)

end

end InfoGeometry.Clifford.Clifford55
