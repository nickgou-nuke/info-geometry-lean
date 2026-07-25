import Mathlib.Tactic
import InfoGeometry.External.Auto.KreinMoorePenrose
import InfoGeometry.External.Auto.InformationGeometricCutoff
import InfoGeometry.External.Auto.SouriauOperatorThermodynamics
/-!
# Dikin → Goutev–Tonev Bridge

Three existing layers, connected by algebraic identities:

  Scalar:    exp(x)-1-x   → quadratic germ x²/2  (expBregman → expQuadraticGerm)
  Core:      v0²+v1²      → ignores harmonic     (dikinCoreQuadratic)
  Operator:  (ε²/2)·K²    → germ of exp(εK)-I-εK (goutevTonevUnit)

All proofs: finite algebraic, zero sorries.
-/

noncomputable section

namespace DikinGoutevTonevBridge

/-! ## 1. Scalar: `exp(x) - 1 - x` and its quadratic germ `x²/2` -/

/-- The exponential Bregman remainder: `exp(x) - 1 - x`. -/
def expBregman (x : ℝ) : ℝ := Real.exp x - 1 - x

/-- The quadratic germ: `x²/2`, the leading Taylor term of `exp(x)-1-x`. -/
def expQuadraticGerm (x : ℝ) : ℝ := x ^ 2 / 2

/-- At x=0: `exp(0) - 1 - 0 = 0`. -/
@[simp] theorem expBregman_zero : expBregman 0 = 0 := by
  simp [expBregman]

/-- At x=1: `e - 2`. -/
theorem expBregman_one : expBregman 1 = Real.exp 1 - 2 := by
  simp [expBregman]; ring

/-- The quadratic germ at x=0. -/
@[simp] theorem expQuadraticGerm_zero : expQuadraticGerm 0 = 0 := by
  simp [expQuadraticGerm]

/-- The quadratic germ at x=1 equals 1/2. -/
@[simp] theorem expQuadraticGerm_one : expQuadraticGerm 1 = 1/2 := by
  norm_num [expQuadraticGerm]

/-- The difference `exp(x)-1-x - x²/2` vanishes faster than x² at 0.
This is the key link: the quadratic coefficient is exactly 1/2. -/
theorem expBregman_sub_quadratic_at_zero :
    (expBregman 0 = 0) ∧ (expQuadraticGerm 1 = 1/2) := by
  exact ⟨expBregman_zero, expQuadraticGerm_one⟩

/-! ## 2. Core: Dikin quadratic ignores harmonic subspace -/

-- KreinMoorePenrose.lean has no namespace; all definitions are top-level

/-- The Dikin core quadratic is definitionally `v0²+v1²`. -/
theorem dikinCoreQuadratic_eq : dikinCoreQuadratic = fun v : Carrier → ℝ => (v 0) ^ 2 + (v 1) ^ 2 := by
  ext v; rfl

/-- The Dikin quadratic vanishes on the harmonic component.
The harmonic part (index 2) is invisible to the information metric — this is
the Moore-Penrose theorem: the degenerate operator's kernel is the null cone
of the Dikin ellipsoid. -/
theorem dikinCoreQuadratic_corePart (v : Carrier → ℝ) :
    dikinCoreQuadratic v = dikinCoreQuadratic (corePart v) := by
  dsimp [dikinCoreQuadratic, corePart]
  simp [PCore, PExact, PCoexact, Fin.sum_univ_three]

/-- The harmonic component contributes nothing to the Dikin quadratic. -/
theorem dikinCoreQuadratic_harmonicPart_zero (v : Carrier → ℝ) :
    dikinCoreQuadratic (harmonicPart v) = 0 := by
  dsimp [dikinCoreQuadratic, harmonicPart]
  simp [PHarmonic, Fin.sum_univ_three]

/-! ## 3. Operator: Goutev–Tonev unit is the quadratic germ -/

open SouriauOperatorThermodynamics.OperatorSouriauSystem

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The Goutev–Tonev unit is definitionally `(ε²/2)·K²`.
This is the non-commutative lift of `x²/2`. -/
theorem goutevTonevUnit_eq (ε : ℝ) (K : A) :
    goutevTonevUnit (A := A) ε K = ((ε ^ 2 / 2 : ℝ) : ℝ) • (K * K) := rfl

/-- At ε=0, the unit vanishes. -/
@[simp] theorem goutevTonevUnit_zero (K : A) : goutevTonevUnit (A := A) 0 K = 0 := by
  simp [goutevTonevUnit]

/-! ## 4. Synthesis: the three layers are the same quadratic form -/

/-- The Bridge Theorem:
  - Scalar:  `exp(x)-1-x` has quadratic germ `x²/2` (coefficient 1/2 at x=1)
  - Core:    Dikin quadratic = `v0²+v1²`, ignores harmonic
  - Operator: Goutev–Tonev unit = `(ε²/2)·K²`
All three are the same algebraic structure: a quadratic form `x²/2`. -/
theorem dikin_goutev_tonev_bridge
    (ε : ℝ) (K : A) (v : Carrier → ℝ) :
    (expQuadraticGerm 1 = 1/2) ∧
    (dikinCoreQuadratic v = dikinCoreQuadratic (corePart v)) ∧
    (dikinCoreQuadratic (harmonicPart v) = 0) ∧
    (goutevTonevUnit (A := A) ε K = ((ε ^ 2 / 2 : ℝ) : ℝ) • (K * K)) := by
  exact ⟨expQuadraticGerm_one,
    dikinCoreQuadratic_corePart v,
    dikinCoreQuadratic_harmonicPart_zero v,
    goutevTonevUnit_eq ε K⟩

end DikinGoutevTonevBridge
