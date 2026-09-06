import InfoGeometry.Lie.SplitOctonionImaginaryTensor
import InfoGeometry.Lie.SplitOctonionEllPolarization

/-!
# The native `ell` polarization of the imaginary split-octonions

This file restricts the native commutator with `lUnit` to the trace-zero
subspace.  The carrier, product, polar form, and three-form are inherited
from the existing Zorn owners; no replacement carrier or assumed eigenspace
structure is introduced.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryEllPolarization

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionImaginaryTensor
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CZ := CanonicalZorn
abbrev Imaginary := InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary
abbrev EndImaginary := Module.End ℝ Imaginary

def imaginaryEllCommutator : EndImaginary where
  toFun X :=
    ⟨ellCommutator X.1, by
      rw [mem_imaginary_iff]
      rw [ellCommutator_apply]
      change traceLinear (lUnit * X.1 - X.1 * lUnit) = 0
      rw [map_sub]
      change realZornTrace (lUnit * X.1) - realZornTrace (X.1 * lUnit) = 0
      rw [realZornTrace_mul_comm X.1 lUnit]
      simp⟩
  map_add' X Y := by
    apply Subtype.ext
    exact map_add ellCommutator X.1 Y.1
  map_smul' r X := by
    apply Subtype.ext
    exact map_smul ellCommutator r X.1

@[simp] theorem imaginaryEllCommutator_apply (X : Imaginary) :
    imaginaryEllCommutator X = ⟨ellCommutator X.1, by
      rw [mem_imaginary_iff]
      rw [ellCommutator_apply]
      change traceLinear (lUnit * X.1 - X.1 * lUnit) = 0
      rw [map_sub]
      change realZornTrace (lUnit * X.1) - realZornTrace (X.1 * lUnit) = 0
      rw [realZornTrace_mul_comm X.1 lUnit]
      simp⟩ := rfl

def imaginaryEllT : EndImaginary := (1 / 2 : ℝ) • imaginaryEllCommutator

@[simp] theorem imaginaryEllT_apply (X : Imaginary) :
    imaginaryEllT X = (1 / 2 : ℝ) • imaginaryEllCommutator X := rfl

def imaginaryEllContraction (X Y : Imaginary) : ℝ :=
    imaginaryCommutatorForm ellImaginary X Y

/-! The distinguished imaginary axis acts by the same commutator contraction
as the native imaginary cross product.  This is the concrete bridge between
the para-complex operator and the alternating three-form owner. -/

theorem imaginaryEllT_eq_cross (X : Imaginary) :
    imaginaryEllT X = imaginaryCross ellImaginary X := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (lUnit * X.1 - X.1 * lUnit) =
    (1 / 2 : ℝ) • (ellImaginary.1 * X.1 - X.1 * ellImaginary.1)
  rfl

theorem imaginaryEllContraction_eq_polar_cross (X Y : Imaginary) :
    imaginaryEllContraction X Y =
      imaginaryPolarBilin (imaginaryEllT X) Y := by
  rw [imaginaryEllContraction, imaginaryEllT_eq_cross]
  change imaginaryPolarBilin (imaginaryCross ellImaginary X) Y =
    imaginaryPolarBilin (imaginaryCross ellImaginary X) Y
  rfl

theorem imaginaryEllContraction_eq_three_form (X Y : Imaginary) :
    imaginaryEllContraction X Y =
      imaginaryCommutatorForm ellImaginary X Y := rfl

theorem imaginaryEllContraction_swap (X Y : Imaginary) :
    imaginaryEllContraction Y X = -imaginaryEllContraction X Y := by
  unfold imaginaryEllContraction
  have h := imaginaryCommutatorForm_swap_last_two ellImaginary X Y
  linarith

theorem imaginaryEllContraction_self (X : Imaginary) :
    imaginaryEllContraction X X = 0 := by
  unfold imaginaryEllContraction
  exact imaginaryCommutatorForm_self_last ellImaginary X

end InfoGeometry.Lie.SplitOctonionImaginaryEllPolarization
