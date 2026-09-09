import InfoGeometry.Clifford.FanoOctonionParavector
import InfoGeometry.Clifford.ProjectedCliffordAssociatorDefect

/-!
# A concrete Fano-plane projected-associator theorem

The Fano paravector chart supplies a native nonzero associator theorem.  The
second theorem transports the same proved nonvanishing statement through the
existing `ProjectedCliffordShadow` interface.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Clifford.FanoProjectedAssociator

open InfoGeometry.Clifford.FanoOctonionParavector
open InfoGeometry.Clifford.OctonionParavectorBridge
open InfoGeometry.Clifford.ProjectedCliffordAssociatorDefect

private def x0 : Paravector R7 := imaginary (basisVector 0)
private def x1 : Paravector R7 := imaginary (basisVector 1)
private def x4 : Paravector R7 := imaginary (basisVector 4)

theorem fano_associator_eq :
    paravectorMul fanoOctonionParavectorData
        (paravectorMul fanoOctonionParavectorData x0 x1) x4 -
      paravectorMul fanoOctonionParavectorData x0
        (paravectorMul fanoOctonionParavectorData x1 x4) =
      imaginary (2 • basisVector 5) := by
  have h01 : fanoOctonionParavectorData.cross
      (basisVector 0) (basisVector 1) = basisVector 2 := by
    ext i
    fin_cases i <;>
      simp [fanoOctonionParavectorData, fanoCross, fanoCrossRaw, basisVector,
        Pi.single_apply]
  have h24 : fanoOctonionParavectorData.cross
      (basisVector 2) (basisVector 4) = basisVector 5 := by
    ext i
    fin_cases i <;>
      simp [fanoOctonionParavectorData, fanoCross, fanoCrossRaw, basisVector,
        Pi.single_apply]
  have h14 : fanoOctonionParavectorData.cross
      (basisVector 1) (basisVector 4) = basisVector 6 := by
    ext i
    fin_cases i <;>
      simp [fanoOctonionParavectorData, fanoCross, fanoCrossRaw, basisVector,
        Pi.single_apply]
  have h06 : fanoOctonionParavectorData.cross
      (basisVector 0) (basisVector 6) = -basisVector 5 := by
    ext i
    fin_cases i <;>
      simp [fanoOctonionParavectorData, fanoCross, fanoCrossRaw, basisVector,
        Pi.single_apply]
  have hleft :
      paravectorMul fanoOctonionParavectorData
          (paravectorMul fanoOctonionParavectorData x0 x1) x4 =
        imaginary (basisVector 5) := by
    dsimp [x0, x1, x4]
    rw [imaginary_mul_imaginary, h01]
    have hinner01 :
        fanoOctonionParavectorData.inner (basisVector 0) (basisVector 1) = 0 := by
      simp [fanoOctonionParavectorData, dot7, basisVector,
        Pi.single_apply, Fin.sum_univ_seven]
    rw [hinner01]
    simp only [neg_zero]
    change paravectorMul fanoOctonionParavectorData
      (imaginary (basisVector 2)) (imaginary (basisVector 4)) = _
    rw [imaginary_mul_imaginary, h24]
    have hinner24 :
        fanoOctonionParavectorData.inner (basisVector 2) (basisVector 4) = 0 := by
      simp [fanoOctonionParavectorData, dot7, basisVector,
        Pi.single_apply, Fin.sum_univ_seven]
    rw [hinner24]
    ext <;>
      norm_num [imaginary, basisVector, Pi.single_apply]
  have hright :
      paravectorMul fanoOctonionParavectorData x0
          (paravectorMul fanoOctonionParavectorData x1 x4) =
        -imaginary (basisVector 5) := by
    dsimp [x0, x1, x4]
    rw [imaginary_mul_imaginary]
    rw [h14]
    have hinner14 :
        fanoOctonionParavectorData.inner (basisVector 1) (basisVector 4) = 0 := by
      simp [fanoOctonionParavectorData, dot7, basisVector,
        Pi.single_apply, Fin.sum_univ_seven]
    rw [hinner14]
    simp only [neg_zero]
    change paravectorMul fanoOctonionParavectorData
      (imaginary (basisVector 0)) (imaginary (basisVector 6)) = _
    rw [imaginary_mul_imaginary, h06]
    have hinner06 :
        fanoOctonionParavectorData.inner (basisVector 0) (basisVector 6) = 0 := by
      simp [fanoOctonionParavectorData, dot7, basisVector,
        Pi.single_apply, Fin.sum_univ_seven]
    rw [hinner06]
    ext <;>
      norm_num [imaginary, basisVector, Pi.single_apply]
  rw [hleft, hright]
  ext k <;> simp [imaginary, basisVector] <;> ring

theorem fano_associator_ne_zero :
    paravectorMul fanoOctonionParavectorData
        (paravectorMul fanoOctonionParavectorData x0 x1) x4 -
      paravectorMul fanoOctonionParavectorData x0
        (paravectorMul fanoOctonionParavectorData x1 x4) ≠ 0 := by
  rw [fano_associator_eq]
  intro h
  have h5 := congrArg Prod.snd h
  have hcoord := congrFun h5 ⟨5, by decide⟩
  have : (1 : ℝ) = 0 := by
    simpa [imaginary, basisVector, Pi.single_apply] using hcoord
  norm_num at this

theorem fano_shadow_leakage_readout_ne_zero
    {Cl : Type*} [Ring Cl] [Algebra ℝ Cl]
    (S : ProjectedCliffordShadow fanoOctonionParavectorData Cl) :
    S.projectParavector (
        S.includeParavector x0 *
            ambientLeakage fanoOctonionParavectorData S
              (S.includeParavector x1 * S.includeParavector x4) -
          ambientLeakage fanoOctonionParavectorData S
              (S.includeParavector x0 * S.includeParavector x1) *
            S.includeParavector x4) ≠ 0 := by
  rw [← projectedParavectorAssociator_eq_leakage
    fanoOctonionParavectorData S x0 x1 x4]
  exact fano_associator_ne_zero

end InfoGeometry.Clifford.FanoProjectedAssociator
