import InfoGeometry.Canonical.SplitOctonionThreeColorDiracCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionLeftRegularAssociatorDefect

namespace InfoGeometry.Canonical

open SplitOctonionColour
open SplitQuaternionAssociativeCoassociativeCalibrationBridge

noncomputable section

/-!
# Colour-local Dirac operator representation

The colour-local Dirac element is represented by left multiplication on the
associative colour core.  This file stays on the finite algebraic layer: it
does not claim any Hilbert-space or spectral-triple structure.
-/

/-- Left multiplication by the colour-local Dirac element on the associative
colour core. -/
def colorDiracLeftOp
    (c : SplitOctonionColour) (a b : ℚ) :
    colorCore c →ₗ[ℚ] colorCore c :=
  colorCoreLeftMul c ⟨colorDirac c a b, colorDirac_mem_colorCore c a b⟩

/-- The scalar square term as an element of the associative colour core. -/
def colorDiracSqCore
    (c : SplitOctonionColour) (a b : ℚ) : colorCore c :=
  ⟨(a * b) • rationalBasis .one,
    by
      have hunit : rationalBasis .one ∈ colorCore c := by
        rw [← modularPolarized_one]
        exact (colorCore c).add_mem
          (modularNPlus_mem_threeColorCore c)
          (modularNMinus_mem_threeColorCore c)
      exact (colorCore c).smul_mem (a * b) hunit⟩

@[simp] theorem colorDiracLeftOp_apply
    (c : SplitOctonionColour) (a b : ℚ) (x : colorCore c) :
    colorDiracLeftOp c a b x =
      colorCoreLeftMul c ⟨colorDirac c a b, colorDirac_mem_colorCore c a b⟩ x :=
  rfl

/-- The square of the colour-local Dirac operator on a vector `x` is the
left-regular action of the scalar mass term `ab · 1`. -/
theorem colorDiracLeftOp_sq_apply
    (c : SplitOctonionColour) (a b : ℚ) (x : colorCore c) :
    colorDiracLeftOp c a b (colorDiracLeftOp c a b x) =
      colorCoreLeftMul c (colorDiracSqCore c a b) x := by
  have hcomp :=
    colorCoreLeftRegular_map_mul c
      ⟨colorDirac c a b, colorDirac_mem_colorCore c a b⟩
      ⟨colorDirac c a b, colorDirac_mem_colorCore c a b⟩
  have hcore :
      (⟨splitOctonionMulQ (colorDirac c a b) (colorDirac c a b),
        colorCore_closed_mul c (colorDirac_mem_colorCore c a b)
          (colorDirac_mem_colorCore c a b)⟩ : colorCore c) =
      colorDiracSqCore c a b := by
    apply Subtype.ext
    exact colorDirac_sq c a b
  have h := congrArg (fun F : colorCore c →ₗ[ℚ] colorCore c => F x) hcomp
  rw [hcore] at h
  simpa [colorDiracLeftOp, LinearMap.comp_apply] using h

/-- The square of the colour-local Dirac operator is the left-regular action
of the scalar mass term `ab · 1`. -/
theorem colorDiracLeftOp_sq
    (c : SplitOctonionColour) (a b : ℚ) :
    (colorDiracLeftOp c a b).comp (colorDiracLeftOp c a b) =
      colorCoreLeftMul c (colorDiracSqCore c a b) := by
  apply LinearMap.ext
  intro x
  simpa [LinearMap.comp_apply] using colorDiracLeftOp_sq_apply c a b x

/-- The balanced colour-local Dirac operator, with equal coefficients on the
two chiral legs. -/
def balancedColorDiracLeftOp
    (c : SplitOctonionColour) (m : ℚ) :
    colorCore c →ₗ[ℚ] colorCore c :=
  colorDiracLeftOp c m m

/-- Balanced square law: `D_c(m)^2 = m^2 · 1` on the associative colour core. -/
theorem balancedColorDiracLeftOp_sq_apply
    (c : SplitOctonionColour) (m : ℚ) (x : colorCore c) :
    balancedColorDiracLeftOp c m (balancedColorDiracLeftOp c m x) =
      colorCoreLeftMul c (colorDiracSqCore c m m) x := by
  simpa [balancedColorDiracLeftOp, pow_two] using
    colorDiracLeftOp_sq_apply c m m x

/-- Balanced square law: `D_c(m)^2 = m^2 · 1` on the associative colour core. -/
theorem balancedColorDiracLeftOp_sq
    (c : SplitOctonionColour) (m : ℚ) :
    (balancedColorDiracLeftOp c m).comp (balancedColorDiracLeftOp c m) =
      colorCoreLeftMul c (colorDiracSqCore c m m) := by
  apply LinearMap.ext
  intro x
  simpa [LinearMap.comp_apply] using balancedColorDiracLeftOp_sq_apply c m x

end

end InfoGeometry.Canonical
