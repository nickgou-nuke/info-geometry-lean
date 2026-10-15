import InfoGeometry.Canonical.SplitOctonionThreeColorSplitQuaternionCores
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# The associative algebra carried by one coloured core

The ambient split-octonion carrier is not given a ring structure here.  The
ring instance below is restricted to the closed associative subtype
`colorCore c`.
-/

namespace InfoGeometry.Canonical

open SplitQuaternionAssociativeCoassociativeCalibrationBridge

noncomputable section

def colorCoreMul (c : SplitOctonionColour) (x y : colorCore c) : colorCore c :=
  ⟨splitOctonionMulQ x.1 y.1, colorCore_closed_mul c x.2 y.2⟩

def colorCoreOne (c : SplitOctonionColour) : colorCore c :=
  ⟨rationalBasis .one, by
    change rationalBasis .one ∈ threeColorCore c
    rw [← modularPolarized_one]
    exact (threeColorCore c).add_mem
      (modularNPlus_mem_threeColorCore c)
      (modularNMinus_mem_threeColorCore c)⟩

instance colorCoreMulInst (c : SplitOctonionColour) : Mul (colorCore c) :=
  ⟨colorCoreMul c⟩

instance colorCoreOneInst (c : SplitOctonionColour) : One (colorCore c) :=
  ⟨colorCoreOne c⟩

theorem colorCore_mul_assoc_subtype
    (c : SplitOctonionColour) (x y z : colorCore c) :
    x * y * z = x * (y * z) := by
  apply Subtype.ext
  exact colorCore_mul_assoc c x.2 y.2 z.2

theorem colorCore_one_mul (c : SplitOctonionColour) (x : colorCore c) :
    colorCoreOne c * x = x := by
  have h : ∀ y : StandardRationalSplitOctonion, y ∈ colorCore c →
      splitOctonionMulQ (rationalBasis .one) y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem p hp =>
        rcases hp with ⟨p, rfl⟩
        fin_cases p <;> cases c <;> native_decide
    | zero => rw [splitOctonionMulQ_zero_right]
    | add x y hx hy ihx ihy =>
        rw [splitOctonionMulQ_add_right, ihx, ihy]
    | smul a x hx ih =>
        rw [splitOctonionMulQ_smul_right, ih]
  apply Subtype.ext
  exact h x.1 x.2

theorem colorCore_mul_one (c : SplitOctonionColour) (x : colorCore c) :
    x * colorCoreOne c = x := by
  have h : ∀ y : StandardRationalSplitOctonion, y ∈ colorCore c →
      splitOctonionMulQ y (rationalBasis .one) = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem p hp =>
        rcases hp with ⟨p, rfl⟩
        fin_cases p <;> cases c <;> native_decide
    | zero => rw [splitOctonionMulQ_zero_left]
    | add x y hx hy ihx ihy =>
        rw [splitOctonionMulQ_add_left, ihx, ihy]
    | smul a x hx ih =>
        rw [splitOctonionMulQ_smul_left, ih]
  apply Subtype.ext
  exact h x.1 x.2

noncomputable instance colorCoreRing (c : SplitOctonionColour) :
    Ring (colorCore c) :=
  { (inferInstance : AddCommGroup (colorCore c)) with
    mul := (· * ·)
    one := 1
    mul_assoc := colorCore_mul_assoc_subtype c
    one_mul := colorCore_one_mul c
    mul_one := colorCore_mul_one c
    left_distrib := fun x y z => by
      apply Subtype.ext
      exact splitOctonionMulQ_add_right x.1 y.1 z.1
    right_distrib := fun x y z => by
      apply Subtype.ext
      exact splitOctonionMulQ_add_left x.1 y.1 z.1
    zero_mul := fun x => by
      apply Subtype.ext
      exact splitOctonionMulQ_zero_left x.1
    mul_zero := fun x => by
      apply Subtype.ext
      exact splitOctonionMulQ_zero_right x.1 }

noncomputable instance colorCoreAlgebra (c : SplitOctonionColour) :
    Algebra ℚ (colorCore c) :=
  Algebra.ofModule
    (fun r x y => by
      apply Subtype.ext
      exact splitOctonionMulQ_smul_left r x.1 y.1)
    (fun r x y => by
      apply Subtype.ext
      exact splitOctonionMulQ_smul_right r x.1 y.1)

end

end InfoGeometry.Canonical
