import InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Coordinate bridge for the G₂ Cartan/parameter reflections

The native Cartan reflections and the declared parameter dual reflections use
different rank-two coordinates.  This owner records the change of coordinates
as an explicit linear equivalence.  The matrix is a small CAS candidate; its
invertibility and later intertwining identities are checked by Lean.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanParameterCoordinates

open InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant

abbrev Parameter := InfoGeometry.Algebra.FiniteSpin.Vec2R

def changeLinear : Parameter →ₗ[ℝ] Parameter where
  toFun s := ![3 * s 0 + 3 * s 1, s 0 + 2 * s 1]
  map_add' := by
    intro s t
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro a s
    ext i
    fin_cases i <;> simp <;> ring

def change : Parameter ≃ₗ[ℝ] Parameter :=
  LinearEquiv.ofBijective changeLinear (by
    constructor
    · intro s t h
      ext i
      fin_cases i
      · have h0 := congrFun h 0
        have h1 := congrFun h 1
        dsimp [changeLinear] at h0 h1
        have hs0 : s 0 = t 0 := by linarith [h0, h1]
        simpa using hs0
      · have h0 := congrFun h 0
        have h1 := congrFun h 1
        dsimp [changeLinear] at h0 h1
        have hs1 : s 1 = t 1 := by linarith [h0, h1]
        simpa using hs1
    · intro t
      refine ⟨![(2 * t 0 - 3 * t 1) / 3, (-t 0 + 3 * t 1) / 3], ?_⟩
      ext i
      fin_cases i
      · simp [changeLinear]
        ring
      · simp [changeLinear]
        ring)

@[simp] theorem change_apply (s : Parameter) :
    change s = ![3 * s 0 + 3 * s 1, s 0 + 2 * s 1] := rfl

@[simp] theorem change_symm_apply (t : Parameter) :
    change.symm t = ![(2 * t 0 - 3 * t 1) / 3,
      (-t 0 + 3 * t 1) / 3] := by
  apply change.injective
  rw [change.apply_symm_apply]
  ext i
  fin_cases i
  · simp [change, changeLinear]
    ring
  · simp [change, changeLinear]
    ring

def nativeShortCoordinate (s : Parameter) : Parameter :=
  ![-s 0, s 0 + s 1]

def nativeLongCoordinate (s : Parameter) : Parameter :=
  ![s 1, s 0]

theorem change_short_intertwining (s : Parameter) :
    change (nativeShortCoordinate s) =
      canonicalShortReflectionDualReal (change s) := by
  ext i
  fin_cases i
  · simp [change, changeLinear, nativeShortCoordinate,
      canonicalShortReflectionDualReal]
    ring
  · simp [change, changeLinear, nativeShortCoordinate,
      canonicalShortReflectionDualReal]
    ring

theorem change_long_intertwining (s : Parameter) :
    change (nativeLongCoordinate s) =
      canonicalLongReflectionDualReal (change s) := by
  ext i
  fin_cases i
  · simp [change, changeLinear, nativeLongCoordinate,
      canonicalLongReflectionDualReal]
    ring
  · simp [change, changeLinear, nativeLongCoordinate,
      canonicalLongReflectionDualReal]
    ring

theorem change_det_ne_zero : (3 : ℝ) ≠ 0 := by norm_num

end InfoGeometry.Lie.CanonicalZornG2CartanParameterCoordinates
