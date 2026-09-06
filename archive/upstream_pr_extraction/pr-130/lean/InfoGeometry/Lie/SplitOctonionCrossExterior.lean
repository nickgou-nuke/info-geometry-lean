import InfoGeometry.Lie.SplitOctonionCrossTensor
import Mathlib.Tactic

/-!
# The native Zorn cross product on the second exterior power

This owner linearizes the already-proved native `Fin 3` Zorn cross product
through Mathlib's universal property of the second exterior power.  It then
uses the three concrete basis wedges and the exact finite-dimensional rank
calculation to prove that the resulting map is a linear equivalence.

No abstract cross-product interface or Hodge-star assumption is introduced.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCrossExterior

open InfoGeometry.Canonical
open InfoGeometry.Lie.SplitOctonionCrossTensor

abbrev Vec3 := Fin 3 → ℝ
abbrev Bivector3 := ⋀[ℝ]^2 Vec3

/-! The exterior map is owned by `SplitOctonionCrossTensor`. -/

theorem nativeCrossExteriorMap_ιMulti_fun (v : Fin 2 → Vec3) :
    nativeCrossExteriorMap (exteriorPower.ιMulti ℝ 2 v) =
      ZornMatrix.cross (v 0) (v 1) := by
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
    (SplitOctonionCrossTensor.nativeCrossExteriorMap_ιMulti (v 0) (v 1))

@[simp] theorem nativeCrossExteriorMap_ιMulti (u v : Vec3) :
    nativeCrossExteriorMap (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      ZornMatrix.cross u v := by
  exact SplitOctonionCrossTensor.nativeCrossExteriorMap_ιMulti u v

/-- The grade-two cross map is compatible with the native volume pairing on
generators.  This is the concrete Hodge-dual readout before extending the
pairing to an arbitrary bivector. -/
theorem nativeCrossExteriorMap_dot_ιMulti (u v w : Vec3) :
    ZornMatrix.dot u
        (nativeCrossExteriorMap (exteriorPower.ιMulti ℝ 2 ![v, w])) =
      nativeVolumeForm ![u, v, w] := by
  rw [nativeCrossExteriorMap_ιMulti,
    nativeVolumeForm_apply_eq_scalarTriple]
  rfl

private def basisVec (i : Fin 3) : Vec3 := Pi.single i 1

@[simp] theorem nativeCrossExteriorMap_basis12 :
    nativeCrossExteriorMap
        (exteriorPower.ιMulti ℝ 2 ![basisVec 1, basisVec 2]) =
      basisVec 0 := by
  rw [nativeCrossExteriorMap_ιMulti]
  funext i
  fin_cases i <;> simp [basisVec, ZornMatrix.cross]

@[simp] theorem nativeCrossExteriorMap_basis20 :
    nativeCrossExteriorMap
        (exteriorPower.ιMulti ℝ 2 ![basisVec 2, basisVec 0]) =
      basisVec 1 := by
  rw [nativeCrossExteriorMap_ιMulti]
  funext i
  fin_cases i <;> simp [basisVec, ZornMatrix.cross]

@[simp] theorem nativeCrossExteriorMap_basis01 :
    nativeCrossExteriorMap
        (exteriorPower.ιMulti ℝ 2 ![basisVec 0, basisVec 1]) =
      basisVec 2 := by
  rw [nativeCrossExteriorMap_ιMulti]
  funext i
  fin_cases i <;> simp [basisVec, ZornMatrix.cross]

theorem nativeCrossExteriorMap_surjective :
    Function.Surjective nativeCrossExteriorMap := by
  intro x
  refine ⟨
    x 0 • exteriorPower.ιMulti ℝ 2 ![basisVec 1, basisVec 2] +
      x 1 • exteriorPower.ιMulti ℝ 2 ![basisVec 2, basisVec 0] +
      x 2 • exteriorPower.ιMulti ℝ 2 ![basisVec 0, basisVec 1], ?_⟩
  rw [map_add, map_add, map_smul, map_smul, map_smul,
    nativeCrossExteriorMap_basis12, nativeCrossExteriorMap_basis20,
    nativeCrossExteriorMap_basis01]
  funext i
  fin_cases i <;> simp [basisVec]

theorem nativeCrossExteriorMap_finrank_eq :
    Module.finrank ℝ Bivector3 = Module.finrank ℝ Vec3 := by
  rw [exteriorPower.finrank_eq ℝ 2, Module.finrank_pi]
  norm_num

/-- In three dimensions, the native cross contraction identifies bivectors
with axial vectors. -/
def nativeCrossExteriorLinearEquiv : Bivector3 ≃ₗ[ℝ] Vec3 := by
  apply LinearEquiv.ofBijective nativeCrossExteriorMap
  constructor
  · exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      nativeCrossExteriorMap_finrank_eq).2 nativeCrossExteriorMap_surjective
  · exact nativeCrossExteriorMap_surjective

@[simp] theorem nativeCrossExteriorLinearEquiv_ιMulti (u v : Vec3) :
    nativeCrossExteriorLinearEquiv
        (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      ZornMatrix.cross u v := by
  exact nativeCrossExteriorMap_ιMulti u v

/-! ## Metric/volume characterization on arbitrary bivectors -/

/-- Dot pairing with a fixed vector as a native linear functional. -/
def nativeDotLeft (u : Vec3) : Vec3 →ₗ[ℝ] ℝ where
  toFun x := ZornMatrix.dot u x
  map_add' x y := by
    simp [ZornMatrix.dot]
    ring
  map_smul' r x := by
    simp [ZornMatrix.dot]
    ring

/-- Insertion of a vector into the first slot of the native volume form,
linearized on the remaining second exterior power. -/
def nativeVolumeContraction (u : Vec3) : Bivector3 →ₗ[ℝ] ℝ :=
  exteriorPower.alternatingMapLinearEquiv (nativeVolumeForm.curryLeft u)

theorem nativeVolumeContraction_ιMulti_fun
    (u : Vec3) (v : Fin 2 → Vec3) :
    nativeVolumeContraction u (exteriorPower.ιMulti ℝ 2 v) =
      nativeVolumeForm ![u, v 0, v 1] := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (nativeVolumeForm.curryLeft u) v

@[simp] theorem nativeVolumeContraction_ιMulti
    (u v w : Vec3) :
    nativeVolumeContraction u (exteriorPower.ιMulti ℝ 2 ![v, w]) =
      nativeVolumeForm ![u, v, w] := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (nativeVolumeForm.curryLeft u) ![v, w]

/-- The grade-two cross map is the metric dual of contraction with the native
volume form, for every bivector rather than only decomposable generators. -/
theorem nativeDot_crossExterior_eq_volumeContraction (u : Vec3) :
    (nativeDotLeft u).comp nativeCrossExteriorMap =
      nativeVolumeContraction u := by
  apply exteriorPower.alternatingMapLinearEquiv.symm.injective
  ext v
  simp only [exteriorPower.alternatingMapLinearEquiv_symm_apply]
  rw [LinearMap.compAlternatingMap_apply,
    LinearMap.compAlternatingMap_apply]
  change ZornMatrix.dot u
      (nativeCrossExteriorMap (exteriorPower.ιMulti ℝ 2 v)) =
    nativeVolumeContraction u (exteriorPower.ιMulti ℝ 2 v)
  rw [nativeCrossExteriorMap_ιMulti_fun,
    nativeVolumeContraction_ιMulti_fun]
  exact (nativeVolumeForm_apply_eq_scalarTriple u (v 0) (v 1)).symm

theorem nativeDot_crossExterior_apply_eq_volumeContraction
    (u : Vec3) (beta : Bivector3) :
    ZornMatrix.dot u (nativeCrossExteriorMap beta) =
      nativeVolumeContraction u beta := by
  have h := LinearMap.congr_fun
    (nativeDot_crossExterior_eq_volumeContraction u) beta
  exact h

end InfoGeometry.Lie.SplitOctonionCrossExterior
