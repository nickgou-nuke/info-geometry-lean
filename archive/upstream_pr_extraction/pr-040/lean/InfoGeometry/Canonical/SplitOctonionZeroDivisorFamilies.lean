import Mathlib
import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Canonical.ZornVectorMatrixRationalEquiv

namespace InfoGeometry.Canonical

open scoped BigOperators

/-!
  The PDF source uses primitive idempotents and nilpotents in a split-octonion
  algebra.  This owner records only the finite rational algebraic shadow.
  The integral carrier cannot contain the halves, so the definitions live in
  the rational coordinate extension.  No particle-spectrum interpretation is
  asserted here.
-/

def rationalBasisVector (b : IntegralSplitBasis) : StandardRationalSplitOctonion :=
  Pi.single b 1

def rationalOne : StandardRationalSplitOctonion := rationalBasisVector .one
def rationalL : StandardRationalSplitOctonion := rationalBasisVector .l
def rationalI : StandardRationalSplitOctonion := rationalBasisVector .i
def rationalIL : StandardRationalSplitOctonion := rationalBasisVector .il
def rationalJ : StandardRationalSplitOctonion := rationalBasisVector .j
def rationalJL : StandardRationalSplitOctonion := rationalBasisVector .jl
def rationalK : StandardRationalSplitOctonion := rationalBasisVector .k
def rationalKL : StandardRationalSplitOctonion := rationalBasisVector .kl

def rationalBasisMul
    (p q : IntegralSplitBasis) : StandardRationalSplitOctonion :=
  fun r => (basisMul p q r : ℚ)

def rationalSplitOctonionMul
    (x y : StandardRationalSplitOctonion) : StandardRationalSplitOctonion :=
  ∑ p : IntegralSplitBasis, ∑ q : IntegralSplitBasis,
    (x p * y q) • rationalBasisMul p q

def rationalHyperbolicProjectorPlus : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (rationalOne + rationalL)

def rationalHyperbolicProjectorMinus : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (rationalOne - rationalL)

def rationalRedNilpotentPlus : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (rationalL + rationalI)

def rationalRedNilpotentMinus : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (rationalL - rationalI)

def rationalGreenNilpotentPlus : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (rationalL + rationalJ)

def rationalGreenNilpotentMinus : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (rationalL - rationalJ)

def rationalBlueNilpotentPlus : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (rationalL + rationalK)

def rationalBlueNilpotentMinus : StandardRationalSplitOctonion :=
  (1 / 2 : ℚ) • (rationalL - rationalK)

theorem rational_hyperbolic_projector_plus_idempotent :
    rationalSplitOctonionMul
        rationalHyperbolicProjectorPlus
        rationalHyperbolicProjectorPlus =
      rationalHyperbolicProjectorPlus := by
  ext r <;> fin_cases r <;> native_decide

theorem rational_hyperbolic_projector_minus_idempotent :
    rationalSplitOctonionMul
        rationalHyperbolicProjectorMinus
        rationalHyperbolicProjectorMinus =
      rationalHyperbolicProjectorMinus := by
  ext r <;> fin_cases r <;> native_decide

theorem rational_hyperbolic_projectors_orthogonal :
    rationalSplitOctonionMul
        rationalHyperbolicProjectorPlus
        rationalHyperbolicProjectorMinus = 0 := by
  ext r <;> fin_cases r <;> native_decide

theorem rational_hyperbolic_projectors_complete :
    rationalHyperbolicProjectorPlus + rationalHyperbolicProjectorMinus =
      rationalOne := by
  ext r <;> fin_cases r <;>
    simp [rationalHyperbolicProjectorPlus, rationalHyperbolicProjectorMinus,
      rationalOne, rationalL, rationalBasisVector] <;> ring

theorem rational_red_nilpotent_plus_sq_zero :
    rationalSplitOctonionMul rationalRedNilpotentPlus rationalRedNilpotentPlus = 0 := by
  ext r <;> fin_cases r <;> native_decide

theorem rational_red_nilpotent_minus_sq_zero :
    rationalSplitOctonionMul rationalRedNilpotentMinus rationalRedNilpotentMinus = 0 := by
  ext r <;> fin_cases r <;> native_decide

theorem rational_green_nilpotent_plus_sq_zero :
    rationalSplitOctonionMul rationalGreenNilpotentPlus rationalGreenNilpotentPlus = 0 := by
  ext r <;> fin_cases r <;> native_decide

theorem rational_green_nilpotent_minus_sq_zero :
    rationalSplitOctonionMul rationalGreenNilpotentMinus rationalGreenNilpotentMinus = 0 := by
  ext r <;> fin_cases r <;> native_decide

theorem rational_blue_nilpotent_plus_sq_zero :
    rationalSplitOctonionMul rationalBlueNilpotentPlus rationalBlueNilpotentPlus = 0 := by
  ext r <;> fin_cases r <;> native_decide

theorem rational_blue_nilpotent_minus_sq_zero :
    rationalSplitOctonionMul rationalBlueNilpotentMinus rationalBlueNilpotentMinus = 0 := by
  ext r <;> fin_cases r <;> native_decide

theorem rational_red_nilpotents_are_distinct :
    rationalRedNilpotentPlus ≠ rationalRedNilpotentMinus := by
  intro h
  have hcoord : (2 : ℚ)⁻¹ = -(2 : ℚ)⁻¹ := by
    simpa [rationalRedNilpotentPlus, rationalRedNilpotentMinus,
      rationalI, rationalL, rationalBasisVector] using
      congrArg (fun x => x IntegralSplitBasis.i) h
  norm_num at hcoord

end InfoGeometry.Canonical
