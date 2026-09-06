import InfoGeometry.Canonical.SplitOctonionThreeColorSplitQuaternionCores
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

instance colorCoreNonUnitalSemiring (c : SplitOctonionColour) :
    NonUnitalSemiring (colorCore c) := by
  letI : NonUnitalNonAssocSemiring (colorCore c) :=
    { left_distrib := by
        intro x y z
        apply Subtype.ext
        exact splitOctonionMulQ_add_right x.1 y.1 z.1
      right_distrib := by
        intro x y z
        apply Subtype.ext
        exact splitOctonionMulQ_add_left x.1 y.1 z.1
      zero_mul := by
        intro x
        apply Subtype.ext
        exact splitOctonionMulQ_zero_left x.1
      mul_zero := by
        intro x
        apply Subtype.ext
        exact splitOctonionMulQ_zero_right x.1 }
  letI : NonUnitalSemiring (colorCore c) :=
    NonUnitalSemiring.mk (colorCore_mul_assoc_subtype c)
  exact this

noncomputable instance colorCoreModule (c : SplitOctonionColour) :
    Module ℚ (colorCore c) :=
  (colorCore c).module

noncomputable instance colorCoreSemiring (c : SplitOctonionColour) :
    Semiring (colorCore c) := by
  letI : NonUnitalSemiring (colorCore c) := colorCoreNonUnitalSemiring c
  letI : Module ℚ (colorCore c) := colorCoreModule c
  letI : NatCast (colorCore c) :=
    ⟨fun n => n • (1 : colorCore c)⟩
  refine Semiring.mk (colorCore_one_mul c) (colorCore_mul_one c)
    (natCast_zero := by
      change (0 : ℕ) • (1 : colorCore c) = 0
      exact zero_nsmul _)
    (natCast_succ := by
      intro n
      change (n + 1) • (1 : colorCore c) =
        n • (1 : colorCore c) + 1
      rw [succ_nsmul])
    (npow := npowRecAuto) ?_ ?_
  · intro x
    rfl
  · intro n x
    rfl

noncomputable instance colorCoreAlgebra (c : SplitOctonionColour) :
    Algebra ℚ (colorCore c) := by
  letI : Module ℚ (colorCore c) := colorCoreModule c
  letI : Semiring (colorCore c) := colorCoreSemiring c
  exact Algebra.ofModule
    (fun r x y => by
      apply Subtype.ext
      change splitOctonionMulQ (r • x.1) y.1 =
        r • splitOctonionMulQ x.1 y.1
      exact splitOctonionMulQ_smul_left r x.1 y.1)
    (fun r x y => by
      apply Subtype.ext
      change splitOctonionMulQ x.1 (r • y.1) =
        r • splitOctonionMulQ x.1 y.1
      exact splitOctonionMulQ_smul_right r x.1 y.1)

end

end InfoGeometry.Canonical
