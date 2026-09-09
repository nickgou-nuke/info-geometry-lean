import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Canonical.NativeToeplitzCuntzThree
import InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge

/-!
# Native three-generator Toeplitz--Cuntz bridge

The canonical three-generator interface is instantiated by the existing
noncommutative tensor/RingQuot carrier `CuntzToeplitzAlg 3`.  No scalar or
commutative diagonal model is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzTensorToeplitzThreeBridge

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Canonical.NativeToeplitzCuntzThree
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open ToeplitzCuntzThreeGenerators

abbrev NativeToeplitzThree := CuntzToeplitzAlg 3

theorem native_initial_relation (i j : Fin 3) :
    star (generator i) * generator j = if i = j then 1 else 0 :=
  NativeToeplitzCuntzThree.initialRelation i j

theorem native_resolution :
    excitation + vacuumDefect = (1 : NativeToeplitzThree) :=
  NativeToeplitzCuntzThree.resolution

theorem native_defect_is_self_adjoint_direct :
    star vacuumDefect = vacuumDefect :=
  NativeToeplitzCuntzThree.vacuumDefect_selfAdjoint

private abbrev i0 : Fin 3 := ⟨0, by decide⟩
private abbrev i1 : Fin 3 := ⟨1, by decide⟩
private abbrev i2 : Fin 3 := ⟨2, by decide⟩

def nativeToeplitzThreeGenerators :
    ToeplitzCuntzThreeGenerators NativeToeplitzThree where
  V1 := toeplitzS 3 i0
  V2 := toeplitzS 3 i1
  V3 := toeplitzS 3 i2
  V1_isometry := by simpa only [star_toeplitzS] using toeplitz_orthogonality 3 i0 i0
  V2_isometry := by simpa only [star_toeplitzS] using toeplitz_orthogonality 3 i1 i1
  V3_isometry := by simpa only [star_toeplitzS] using toeplitz_orthogonality 3 i2 i2
  V1_V2_ortho := by simpa only [star_toeplitzS] using toeplitz_orthogonality 3 i0 i1
  V2_V1_ortho := by simpa only [star_toeplitzS] using toeplitz_orthogonality 3 i1 i0
  V2_V3_ortho := by simpa only [star_toeplitzS] using toeplitz_orthogonality 3 i1 i2
  V3_V2_ortho := by simpa only [star_toeplitzS] using toeplitz_orthogonality 3 i2 i1
  V1_V3_ortho := by simpa only [star_toeplitzS] using toeplitz_orthogonality 3 i0 i2
  V3_V1_ortho := by simpa only [star_toeplitzS] using toeplitz_orthogonality 3 i2 i0

@[simp] theorem native_V1 :
    nativeToeplitzThreeGenerators.V1 = toeplitzS 3 i0 := rfl

@[simp] theorem native_V2 :
    nativeToeplitzThreeGenerators.V2 = toeplitzS 3 i1 := rfl

@[simp] theorem native_V3 :
    nativeToeplitzThreeGenerators.V3 = toeplitzS 3 i2 := rfl

theorem native_three_resolution :
    nativeToeplitzThreeGenerators.P1 +
        nativeToeplitzThreeGenerators.P2 +
        nativeToeplitzThreeGenerators.P3 +
        nativeToeplitzThreeGenerators.P0 = (1 : NativeToeplitzThree) := by
  exact toeplitzCuntz3_resolution nativeToeplitzThreeGenerators

theorem native_defect_is_projection :
    nativeToeplitzThreeGenerators.P0 * nativeToeplitzThreeGenerators.P0 =
      nativeToeplitzThreeGenerators.P0 := by
  exact defectProjection_sq nativeToeplitzThreeGenerators

theorem native_defect_is_self_adjoint :
    star nativeToeplitzThreeGenerators.P0 = nativeToeplitzThreeGenerators.P0 := by
  exact defectProjection_star nativeToeplitzThreeGenerators

end InfoGeometry.Canonical.CuntzTensorToeplitzThreeBridge
