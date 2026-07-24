import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import InfoGeometry.Canonical.SplitOctonionClassificationCore

/-!
# Zorn legitimate facts

This file closes the constructive statements that are still honest and
classical in the explicit Zorn carrier:

* the carrier has real finrank `8`;
* it has a nonzero null vector;
* it is noncommutative;
* the bundled Zorn carrier has a concrete nonzero associator witness.

No wrapper theorems, no classification claims, no exceptional-group claims.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornLegitimateFacts

open scoped BigOperators

namespace Explicit

open InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-- The concrete basis vector `(1,0,0)` in `Vec3`. -/
def v0 : Vec3 := ![1, 0, 0]

/-- The explicit coordinate Zorn carrier has real finrank `8`. -/
theorem zornCoord_finrank_eq_8 : Module.finrank ℝ ZornCoord = 8 := by
  simp [ZornCoord, Vec3]

/-- The upper nilpotent block is null. -/
theorem upperVectorZorn_isNull (x : Vec3) :
    IsZornNull (upperVectorZorn x) := by
  simp [IsZornNull, zornNorm, upperVectorZorn, dot3]

/-- The lower nilpotent block is null. -/
theorem lowerVectorZorn_isNull (x : Vec3) :
    IsZornNull (lowerVectorZorn x) := by
  simp [IsZornNull, zornNorm, lowerVectorZorn, dot3]

/-- A concrete nonzero null vector exists in the explicit Zorn carrier. -/
theorem zornCoord_has_nonzero_null_vector :
    ∃ z : ZornCoord, z ≠ 0 ∧ IsZornNull z := by
  refine ⟨upperVectorZorn v0, ?_, upperVectorZorn_isNull v0⟩
  intro h
  have hx : v0 = (0 : Vec3) := by
    have hx' := congrArg (fun z : ZornCoord => z.2.2.1) h
    change v0 = (0 : Vec3) at hx'
    exact hx'
  have hx0 := congrArg (fun v : Vec3 => v 0) hx
  simpa [v0] using hx0

/-- The explicit Zorn carrier is noncommutative. -/
theorem zornCoord_noncommutative_exists :
    ∃ x y : ZornCoord, zornMul x y ≠ zornMul y x := by
  refine ⟨upperVectorZorn v0, lowerVectorZorn v0, ?_⟩
  intro h
  have ha := congrArg (fun z : ZornCoord => z.1) h
  simp [zornMul, upperVectorZorn, lowerVectorZorn, zornMk, dot3, cross3,
    v0, zornA, zornB, zornX, zornY] at ha

end Explicit

namespace Bundled

open InfoGeometry.Canonical.SplitOctonionClassificationCore
open SplitOctonionClassificationCore.ZornMatrix

/-- The bundled Zorn carrier has a concrete nonzero associator witness. -/
theorem zornMatrix_nonassociative_exists :
    ∃ x y z : InfoGeometry.Canonical.ZornMatrix ℝ,
      SplitOctonionClassificationCore.ZornMatrix.associator (R := ℝ) x y z ≠ 0 := by
  let x : InfoGeometry.Canonical.ZornMatrix ℝ :=
    lower SplitOctonionClassificationCore.ZornMatrix.e0
  have hy : x.y ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : Fin 3 → ℝ => v 0) h
    simp [x, lower, SplitOctonionClassificationCore.ZornMatrix.e0] at h0
  rcases nonzero_associator_of_y_ne_zero (R := ℝ) x hy with ⟨y, z, hz⟩
  exact ⟨x, y, z, hz⟩

end Bundled

end InfoGeometry.Canonical.ZornLegitimateFacts
