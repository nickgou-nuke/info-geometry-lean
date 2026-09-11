import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionImaginaryTensor

/-!
# The native imaginary split-octonion cross and scalar three-form

The commutator construction is the honest vector-valued cross product on the
trace-zero carrier.  This owner records its alternating readout against the
existing native determinant polarization; it does not assert a stable-form or
`G₂` classification theorem.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryThreeForm

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionImaginaryAction

abbrev Imaginary := SplitOctonionImaginaryAction.Imaginary

def imaginaryCross (X Y : Imaginary) : Imaginary :=
  ⟨(1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1), by
    rw [mem_imaginary_iff]
    change traceLinear ((1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1)) = 0
    simp only [map_smul, map_sub]
    change (1 / 2 : ℝ) •
      (realZornTrace (X.1 * Y.1) - realZornTrace (Y.1 * X.1)) = 0
    rw [realZornTrace_mul_comm]
    simp⟩

theorem imaginaryCross_swap (X Y : Imaginary) :
    imaginaryCross Y X = -imaginaryCross X Y := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (Y.1 * X.1 - X.1 * Y.1) =
    -((1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1))
  module

@[simp] theorem imaginaryCross_self (X : Imaginary) :
    imaginaryCross X X = 0 := by
  apply Subtype.ext
  simp [imaginaryCross]

def imaginaryThreeForm (X Y Z : Imaginary) : ℝ :=
  imaginaryPolarBilin (imaginaryCross X Y) Z

theorem imaginaryThreeForm_eq_imaginaryCommutatorForm
    (X Y Z : Imaginary) :
    imaginaryThreeForm X Y Z =
      InfoGeometry.Lie.SplitOctonionImaginaryTensor.imaginaryCommutatorForm
        X Y Z := by
  rfl

theorem imaginaryThreeForm_swap (X Y Z : Imaginary) :
    imaginaryThreeForm Y X Z = -imaginaryThreeForm X Y Z := by
  unfold imaginaryThreeForm
  rw [imaginaryCross_swap]
  simp only [map_neg]
  rfl

theorem imaginaryThreeForm_self (X Z : Imaginary) :
    imaginaryThreeForm X X Z = 0 := by
  unfold imaginaryThreeForm
  rw [imaginaryCross_self]
  simp

theorem imaginaryThreeForm_cyclic (X Y Z : Imaginary) :
    imaginaryThreeForm X Y Z = imaginaryThreeForm Y Z X := by
  rw [imaginaryThreeForm_eq_imaginaryCommutatorForm,
    imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact InfoGeometry.Lie.SplitOctonionImaginaryTensor.imaginaryCommutatorForm_cyclic
    X Y Z

theorem imaginaryThreeForm_swap_last_two (X Y Z : Imaginary) :
    imaginaryThreeForm X Z Y = -imaginaryThreeForm X Y Z := by
  rw [imaginaryThreeForm_eq_imaginaryCommutatorForm,
    imaginaryThreeForm_eq_imaginaryCommutatorForm]
  exact InfoGeometry.Lie.SplitOctonionImaginaryTensor.imaginaryCommutatorForm_swap_last_two
    X Y Z

theorem imaginaryThreeForm_alternating (X Y Z : Imaginary) :
    imaginaryThreeForm X Y Z = -imaginaryThreeForm Y X Z := by
  exact imaginaryThreeForm_swap Y X Z

end InfoGeometry.Lie.SplitOctonionImaginaryThreeForm
