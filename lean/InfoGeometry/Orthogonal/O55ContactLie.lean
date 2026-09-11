import InfoGeometry.Orthogonal.O55ContactCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Native orthogonal endomorphism lane over the `(5,5)` contact carrier. -/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

abbrev End55 := Module.End ℝ Vector55

def IsSplitSkew (A : End55) : Prop :=
  ∀ x y, splitPairing (A x) y + splitPairing x (A y) = 0

@[simp] theorem isSplitSkew_zero : IsSplitSkew (0 : End55) := by
  intro x y
  simp

theorem isSplitSkew_add {A B : End55}
    (hA : IsSplitSkew A) (hB : IsSplitSkew B) :
    IsSplitSkew (A + B) := by
  intro x y
  simp only [LinearMap.add_apply, splitPairing_add_left,
    splitPairing_add_right]
  linarith [hA x y, hB x y]

theorem isSplitSkew_smul {A : End55} (hA : IsSplitSkew A) (c : ℝ) :
    IsSplitSkew (c • A) := by
  intro x y
  simp only [LinearMap.smul_apply, splitPairing_smul_left,
    splitPairing_smul_right]
  calc
    c * splitPairing (A x) y + c * splitPairing x (A y) =
        c * (splitPairing (A x) y + splitPairing x (A y)) := by ring
    _ = c * 0 := by rw [hA x y]
    _ = 0 := by ring

theorem isSplitSkew_commutator {A B : End55}
    (hA : IsSplitSkew A) (hB : IsSplitSkew B) :
    IsSplitSkew ⁅A, B⁆ := by
  change IsSplitSkew (A * B - B * A)
  intro x y
  have hAB := hA (B x) y
  have hBA := hB (A x) y
  have hAy := hA x (B y)
  have hBy := hB x (A y)
  change splitPairing (A (B x) - B (A x)) y +
      splitPairing x (A (B y) - B (A y)) = 0
  rw [splitPairing_sub_left, splitPairing_sub_right]
  linarith

def splitOrthogonalLie : LieSubalgebra ℝ End55 where
  carrier := {A | IsSplitSkew A}
  zero_mem' := isSplitSkew_zero
  add_mem' := fun hA hB => isSplitSkew_add hA hB
  smul_mem' := by
    intro c A hA
    exact isSplitSkew_smul hA c
  lie_mem' := fun hA hB => isSplitSkew_commutator hA hB

abbrev O55Lie := splitOrthogonalLie

def contactEulerEnd : End55 where
  toFun x i := contactWeightR i * x i
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' c x := by
    ext i
    simp [contactWeightR]
    ring

@[simp] theorem contactEulerEnd_apply (x : Vector55) (i : Fin 10) :
    contactEulerEnd x i = contactWeightR i * x i := rfl

theorem contactEuler_isSplitSkew : IsSplitSkew contactEulerEnd := by
  intro x y
  simp [splitPairing, contactEulerEnd, contactWeightR, contactWeight]
  ring

def contactEuler : O55Lie :=
  ⟨contactEulerEnd, contactEuler_isSplitSkew⟩

@[simp] theorem contactEuler_mem :
    (contactEuler : End55) = contactEulerEnd := rfl

theorem contactEuler_cube :
    contactEulerEnd * contactEulerEnd * contactEulerEnd = contactEulerEnd := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;>
    simp [Module.End.mul_apply, contactEulerEnd, contactWeightR,
      contactWeight]

end InfoGeometry.Orthogonal.O55Contact
