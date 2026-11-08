import InfoGeometry.Clifford.Cl11Quaternion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl44Witt

/-!
# Native split-quaternion sector inside `Cl(4,4)`

The first positive/negative orthogonal pair in the diagonal `(4,4)` space
defines a quadratic-form-preserving inclusion of the `(1,1)` plane.  The
native Clifford universal property therefore supplies an algebra morphism
from `Cl(1,1)` into `Cl(4,4)`.  Since the source is Mathlib's split quaternion
algebra through `CliffordAlgebraQuaternion.equiv`, this is the precise
four-dimensional split-quaternion packet selected from the eight generators.
-/

namespace InfoGeometry.Clifford.Cl44SplitQuaternionSector

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford.Cl11Quaternion

/-- Inclusion of the first split orthogonal plane in the `(4,4)` carrier. -/
noncomputable def planeGenerator : (ℝ × ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun v := v.1 • eVec 0 + v.2 • fVec 0
  map_add' u v := by
    simp [add_smul]
    module
  map_smul' c v := by
    simp [smul_add, smul_smul]

/-- The selected plane preserves the split quadratic form. -/
theorem planeGenerator_isometry (v : ℝ × ℝ) :
    splitQ44 (planeGenerator v) = Q11 v := by
  rcases v with ⟨a, b⟩
  simp [planeGenerator, eVec, fVec, splitQ44_apply, Q11,
    CliffordAlgebraQuaternion.Q]
  ring

/-- The selected plane followed by the native `Cl(4,4)` generator map. -/
noncomputable def targetGenerator : (ℝ × ℝ) →ₗ[ℝ] Cl44 :=
  (CliffordAlgebra.ι splitQ44).comp planeGenerator

theorem targetGenerator_sq (v : ℝ × ℝ) :
    targetGenerator v * targetGenerator v = algebraMap ℝ Cl44 (Q11 v) := by
  change CliffordAlgebra.ι splitQ44 (planeGenerator v) *
      CliffordAlgebra.ι splitQ44 (planeGenerator v) = _
  rw [CliffordAlgebra.ι_sq_scalar, planeGenerator_isometry]

/-- Native algebra morphism selecting the `Cl(1,1)` sector of `Cl(4,4)`. -/
noncomputable def cl11Sector : Cl11 →ₐ[ℝ] Cl44 :=
  CliffordAlgebra.lift Q11 ⟨targetGenerator, targetGenerator_sq⟩

@[simp] theorem cl11Sector_ι (v : ℝ × ℝ) :
    cl11Sector (CliffordAlgebra.ι Q11 v) =
      CliffordAlgebra.ι splitQ44 (planeGenerator v) := by
  rw [cl11Sector, CliffordAlgebra.lift_ι_apply]
  rfl

/-- The positive source generator maps to the first positive `Cl(4,4)` generator. -/
theorem cl11Sector_positiveGenerator :
    cl11Sector (CliffordAlgebra.ι Q11 (1, 0)) = e 0 := by
  rw [cl11Sector_ι]
  simp [planeGenerator, e]

/-- The negative source generator maps to the first negative `Cl(4,4)` generator. -/
theorem cl11Sector_negativeGenerator :
    cl11Sector (CliffordAlgebra.ι Q11 (0, 1)) = f 0 := by
  rw [cl11Sector_ι]
  simp [planeGenerator, f]

/--
The same selected sector with Mathlib's split-quaternion algebra as its
domain.  This is an algebra morphism, so multiplication and the bilinear
Clifford relations are transported rather than re-proved coordinatewise.
-/
noncomputable def splitQuaternionSector : Hsplit →ₐ[ℝ] Cl44 :=
  cl11Sector.comp
    (CliffordAlgebraQuaternion.equiv
      (R := ℝ) (c₁ := (1 : ℝ)) (c₂ := (-1 : ℝ))).symm.toAlgHom

end InfoGeometry.Clifford.Cl44SplitQuaternionSector
