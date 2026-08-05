import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Clifford.Cl55RealSplitPin
import InfoGeometry.Clifford.Cl55RealSplitPinAction
import InfoGeometry.Canonical.SplitCliffordTensorBridge

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.CliffordTower
open InfoGeometry.Canonical.SplitCliffordTensorBridge

noncomputable section

private def q55ToFin10 : V55 ≃ₗ[ℝ] (Fin 10 → ℝ) :=
  { toFun := fun v =>
      ![v.1 0, v.1 1, v.1 2, v.1 3, v.1 4,
        v.2 0, v.2 1, v.2 2, v.2 3, v.2 4]
    invFun := fun f =>
      (![f 0, f 1, f 2, f 3, f 4],
        ![f 5, f 6, f 7, f 8, f 9])
    left_inv := by
      intro v
      apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
    right_inv := by
      intro f
      funext i
      fin_cases i <;> rfl
    map_add' := by
      intro v w
      funext i
      fin_cases i <;> rfl
    map_smul' := by
      intro c v
      funext i
      fin_cases i <;> rfl }

private def q55ToSplit5 : V55 ≃ₗ[ℝ] SplitSpace 5 :=
  q55ToFin10.trans vec55SplitEquiv

theorem qsplit5_q55ToSplit5 (v : V55) :
    Qsplit 5 (q55ToSplit5 v) = Q55 v := by
  change Qsplit 5 (vec55SplitEquiv (q55ToFin10 v)) = Q55 v
  rw [splitQ_vec55SplitEquiv]
  simp [q55ToFin10, q55Real, Q55_apply, Fin.sum_univ_succ]
  ring

private noncomputable def q55ToSplit5Isometry :
    QuadraticMap.IsometryEquiv Q55 (Qsplit 5) where
  toLinearEquiv := q55ToSplit5
  map_app' := qsplit5_q55ToSplit5

noncomputable def cl55ToSplitCl55 :
    Cl55 ≃ₐ[ℝ] SplitCl55Alg :=
  CliffordAlgebra.equivOfIsometry q55ToSplit5Isometry

noncomputable def cl55ToCl11TensorCl44 :
    Cl55 ≃ₐ[ℝ] SplitClNNTensorStep 4 :=
  cl55ToSplitCl55.trans splitCl55_headCl11TensorCl44Equiv

/-- The native real spinor representation transported from the canonical
    split Clifford model to the `Q55` presentation. -/
noncomputable def cl55SpinorRepresentation :
    Cl55 →ₐ[ℝ] InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  (InfoGeometry.Clifford.SpinorRep.spinorRepresentation 5).comp
    cl55ToSplitCl55.toAlgHom

theorem cl55SpinorRepresentation_ι (v : V55) :
    cl55SpinorRepresentation (ι55 v) =
      InfoGeometry.Clifford.SpinorRep.recursiveGamma 5 (q55ToSplit5 v) := by
  dsimp [cl55SpinorRepresentation, cl55ToSplitCl55,
    CliffordAlgebra.equivOfIsometry]
  rw [CliffordAlgebra.map_apply_ι]
  exact InfoGeometry.Clifford.SpinorRep.spinorRepresentation_ι 5
    (q55ToSplit5 v)

theorem cl55SpinorRepresentation_surjective_iff_gamma_generate :
    Function.Surjective cl55SpinorRepresentation ↔
      Algebra.adjoin ℝ
          (Set.range (InfoGeometry.Clifford.SpinorRep.recursiveGamma 5)) = ⊤ := by
  constructor
  · intro h
    apply
      (InfoGeometry.Clifford.SpinorRep.spinorRepresentation_surjective_iff_gamma_generate 5).mp
    intro y
    rcases h y with ⟨z, hz⟩
    exact ⟨cl55ToSplitCl55 z, hz⟩
  · intro h
    have hs :=
      (InfoGeometry.Clifford.SpinorRep.spinorRepresentation_surjective_iff_gamma_generate 5).mpr h
    intro y
    rcases hs y with ⟨x, hx⟩
    rcases cl55ToSplitCl55.surjective x with ⟨z, hz⟩
    exact ⟨z, by simpa [cl55SpinorRepresentation] using
      (congrArg (fun a =>
        InfoGeometry.Clifford.SpinorRep.spinorRepresentation 5 a) hz).trans hx⟩

noncomputable def cl55SpinorAlgEquiv_of_surjective
    [FiniteDimensional ℝ Cl55]
    (hs : Function.Surjective cl55SpinorRepresentation)
    (hfin : Module.finrank ℝ Cl55 =
      Module.finrank ℝ (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)) :
    Cl55 ≃ₐ[ℝ] InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 := by
  apply AlgEquiv.ofBijective cl55SpinorRepresentation
  constructor
  · exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr
      (show Function.Surjective cl55SpinorRepresentation.toLinearMap from hs)
  · exact hs

/-- The native `pinGroup Q55` action transported to invertible spinor matrices.
    This records the spinor lift without asserting faithfulness or identifying
    the kernel. -/
noncomputable def pin55SpinorUnitRepresentation :
    Pin55 →* (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ :=
  (Units.map cl55SpinorRepresentation.toRingHom).comp pinToUnits

/-- The spinor representation restricted to the corrected split Pin subgroup.

This is only the algebraic unit-valued action.  It deliberately does not
assert faithfulness, identify a kernel, or identify `realSplitPin55` with
Mathlib's `pinGroup Q55`. -/
noncomputable def realSplitPinSpinorUnitRepresentation :
    realSplitPin55 →* (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ :=
  (Units.map cl55SpinorRepresentation.toRingHom).comp
    (Subgroup.subtype realSplitPin55)

theorem realSplitPinSpinorUnitRepresentation_coe
    (g : realSplitPin55) :
    ((realSplitPinSpinorUnitRepresentation g :
        (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
      cl55SpinorRepresentation ((g : Cl55ˣ) : Cl55) := by
  exact Units.coe_map cl55SpinorRepresentation.toRingHom.toMonoidHom
    (g : Cl55ˣ)

noncomputable def involuteSpinorAlgHom :
    Cl55 →ₐ[ℝ] InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  cl55SpinorRepresentation.comp (CliffordAlgebra.involute (Q := Q55))

noncomputable def involuteSpinorUnitHom :
    Cl55ˣ →* (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ :=
  Units.map involuteSpinorAlgHom.toRingHom.toMonoidHom

noncomputable def realSplitPinTwistedSpinorUnitRepresentation :
    realSplitPin55 →* (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ :=
  involuteSpinorUnitHom.comp (Subgroup.subtype realSplitPin55)

private lemma spinorMatrixUnit_inv_coe
    (U : (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
    (↑(U⁻¹) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
      (↑U : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)⁻¹ := by
  letI := Units.invertible U
  have hdet :
      IsUnit (Matrix.det
        (↑U : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)) :=
    Matrix.isUnit_det_of_invertible
      (↑U : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)
  calc
    (↑(U⁻¹) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
        (↑(U⁻¹) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) * 1 := by
          rw [mul_one]
    _ = (↑(U⁻¹) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        ((↑U : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
          (↑U : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)⁻¹) := by
      rw [Matrix.mul_nonsing_inv
        (↑U : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) hdet]
    _ = ((↑(U⁻¹) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
          (↑U : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)) *
        (↑U : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)⁻¹ := by
      rw [mul_assoc]
    _ = (1 : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        (↑U : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)⁻¹ := by
      rw [Units.inv_mul]
    _ = (↑U : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)⁻¹ := by
      rw [one_mul]

theorem realSplitPinTwistedSpinorUnitRepresentation_apply_ι
    (g : realSplitPin55) (v : V55) :
    ((realSplitPinTwistedSpinorUnitRepresentation g :
        (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) *
        cl55SpinorRepresentation (ι55 v) *
      ((realSplitPinSpinorUnitRepresentation g :
        (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ)⁻¹ :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
      cl55SpinorRepresentation (realSplitPinTwistedAdj g v) := by
  dsimp [realSplitPinTwistedSpinorUnitRepresentation,
    involuteSpinorUnitHom, realSplitPinSpinorUnitRepresentation]
  change cl55SpinorRepresentation
      (CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55)) *
        cl55SpinorRepresentation (ι55 v) *
      (cl55SpinorRepresentation ((g : Cl55ˣ) : Cl55))⁻¹ = _
  have hU :
      cl55SpinorRepresentation ((g : Cl55ˣ) : Cl55) =
        ((Units.map cl55SpinorRepresentation.toRingHom.toMonoidHom
          (g : Cl55ˣ) :
            (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ) :
          InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
    exact (Units.coe_map cl55SpinorRepresentation.toRingHom.toMonoidHom
      (g : Cl55ˣ)).symm
  rw [hU, ← spinorMatrixUnit_inv_coe]
  change cl55SpinorRepresentation
      (CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55)) *
        cl55SpinorRepresentation (ι55 v) *
      cl55SpinorRepresentation (↑((g : Cl55ˣ)⁻¹) : Cl55) = _
  rw [← map_mul, ← map_mul]
  rfl

end

end InfoGeometry.Clifford.Clifford55
