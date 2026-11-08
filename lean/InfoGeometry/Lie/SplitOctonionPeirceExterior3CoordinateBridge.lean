import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionPeirceDecompositionBridge

/-!
# The `1 + 3 + 3 + 1` graded coordinate carrier

This owner records the finite-dimensional graded vector-space shadow suggested by
the Peirce decomposition.  It is deliberately a coordinate carrier, not yet an
`ExteriorAlgebra`: the wedge/contraction intertwiner is a separate theorem edge.
The four fields are ordered as degree `0`, degree `1`, degree `2`, and degree `3`.
-/

namespace InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

open InfoGeometry.Lie.SplitOctonionPeirceDecompositionBridge

abbrev Exterior3Coordinates := ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) × ℝ

abbrev PeirceCarrier := InfoGeometry.Algebra.FiniteSpin.Vec8R

def toPeirce : Exterior3Coordinates →ₗ[ℝ] PeirceCarrier where
  toFun x := ![x.1, x.2.1 0, x.2.1 1, x.2.1 2,
    x.2.2.2, x.2.2.1 0, x.2.2.1 1, x.2.2.1 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp

def fromPeirce : PeirceCarrier →ₗ[ℝ] Exterior3Coordinates where
  toFun x :=
    (x 0, ![x 1, x 2, x 3], ![x 5, x 6, x 7], x 4)
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

noncomputable def peirceExterior3Equiv :
    Exterior3Coordinates ≃ₗ[ℝ] PeirceCarrier :=
  { toPeirce with
    invFun := fromPeirce
    left_inv := by
      intro x
      rcases x with ⟨a, b, c, d⟩
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext i
          fin_cases i <;> rfl
        · apply Prod.ext
          · funext i
            fin_cases i <;> rfl
          · rfl
    right_inv := by
      intro x
      funext i
      fin_cases i <;> simp [toPeirce, fromPeirce] }

theorem peirceExterior3Equiv_apply (x : Exterior3Coordinates) :
    peirceExterior3Equiv x = toPeirce x := rfl

theorem peirceExterior3_resolution (x : PeirceCarrier) :
    proj11 x + proj10 x + proj01 x + proj00 x = x :=
  peirce_resolution_of_identity x

end InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
