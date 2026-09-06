import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
import InfoGeometry.Clifford.Clifford55

/-!
# Finite Witt embedding into the `Cl(5,5)` vector carrier

This owner records only the finite quadratic embedding of the split-octonion
coordinate carrier into the native `(5,5)` Witt carrier.  It is not a spin
representation or an exceptional-to-Clifford intertwiner.
-/

namespace InfoGeometry.Lie.SplitOctonionCl55WittEmbeddingBridge

noncomputable section

open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
open InfoGeometry.Clifford.Clifford55

/-- The `(4,4)` carrier as the first four positive/negative coordinates of `V55`.
The half-sum/half-difference coordinates identify the two quadratic forms. -/
def wittToV55 (x : Coord) : V55 :=
  (![ (x 0 + x 4) / 2,
      (x 1 - x 5) / 2,
      (x 2 - x 6) / 2,
      (x 3 - x 7) / 2, 0],
   ![ (x 0 - x 4) / 2,
      (x 1 + x 5) / 2,
      (x 2 + x 6) / 2,
      (x 3 + x 7) / 2, 0])

/-- The finite Witt embedding as a native linear map.

This is still only a carrier-level map: no spin representation or exceptional
algebra action is being asserted here. -/
def wittToV55Linear : Coord →ₗ[ℝ] V55 where
  toFun := wittToV55
  map_add' x y := by
    ext i <;> fin_cases i <;> simp [wittToV55] <;> ring
  map_smul' c x := by
    ext i <;> fin_cases i <;> simp [wittToV55] <;> ring

/-- The canonical left-inverse projection from `V55` to the split-octonion
coordinate carrier. -/
def v55ToWitt (v : V55) : Coord :=
  ![v.1 0 + v.2 0, v.1 1 + v.2 1, v.1 2 + v.2 2, v.1 3 + v.2 3,
    v.1 0 - v.2 0, v.2 1 - v.1 1, v.2 2 - v.1 2, v.2 3 - v.1 3]

/-- The projection back to the split-octonion carrier as a linear map. -/
def v55ToWittLinear : V55 →ₗ[ℝ] Coord where
  toFun := v55ToWitt
  map_add' x y := by
    ext i <;> fin_cases i <;> simp [v55ToWitt] <;> ring
  map_smul' c x := by
    ext i <;> fin_cases i <;> simp [v55ToWitt] <;> ring

@[simp] theorem v55ToWitt_wittToV55 (x : Coord) :
    v55ToWitt (wittToV55 x) = x := by
  ext i
  fin_cases i <;> dsimp [v55ToWitt, wittToV55] <;> ring_nf

@[simp] theorem v55ToWittLinear_wittToV55Linear (x : Coord) :
    v55ToWittLinear (wittToV55Linear x) = x := by
  exact v55ToWitt_wittToV55 x

theorem wittToV55Linear_injective :
    Function.Injective wittToV55Linear := by
  intro x y hxy
  have hproj := congrArg v55ToWittLinear hxy
  simpa using hproj

/-- The `(4,4)` split-octonion Witt norm is the restriction of `Q55`. -/
theorem Q55_wittToV55 (x : Coord) :
    Q55 (wittToV55 x) = wittNorm x := by
  simp [wittToV55, Q55_apply, wittNorm, Fin.sum_univ_succ]
  ring_nf

theorem Q55_wittToV55Linear (x : Coord) :
    Q55 (wittToV55Linear x) = wittNorm x := by
  exact Q55_wittToV55 x

end
end InfoGeometry.Lie.SplitOctonionCl55WittEmbeddingBridge
