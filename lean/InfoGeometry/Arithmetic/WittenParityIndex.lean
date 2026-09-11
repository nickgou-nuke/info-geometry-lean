import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.RamanujanDefectTower

namespace InfoGeometry.Arithmetic.WittenParityIndex

/-!
# The Thermodynamics of the Möbius/Witten Parity Index

This module verifies the finite algebraic parity sequence `(+1, -1, +1, -1)`
for the first four symbolic Ramanujan-defect shapes.

It is intentionally finite: it does not assert the Riemann hypothesis, analytic
continuation, convergence of Ramanujan's formula, or a physical Witten-index
theorem.  It records the closed polynomial parity that can be checked by the
Lean kernel and connects that parity to the verified finite Bernoulli readouts
owned by `RamanujanDefectTower`.

#### BUCKET 1: CLOSED FINITE THEOREMS
`D1_even_parity`, `D2_odd_parity`, `D3_even_parity`, `D4_odd_parity`,
`witten_parity_index_evaluation`, and
`ramanujan_defect_layers_follow_witten_sequence`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
Analytic Ramanujan odd-zeta transformation, thermodynamic/KMS interpretation,
and any Riemann-hypothesis-level statement.

The mathematical objects correspond to:
- n = 1 : ζ(3) defect => Even Parity (+1)
- n = 2 : ζ(5) defect => Odd Parity  (-1)
- n = 3 : ζ(7) defect => Even Parity (+1)
- n = 4 : ζ(9) defect => Odd Parity  (-1)
-/

section AlgebraicParity

variable (α β : ℝ)
variable (c0 c1 c2 : ℝ)

/-! ## 1. n = 1: ζ(3) Defect (Even / +1 Parity) -/

def D1 (x y : ℝ) : ℝ := c0 * x^2 - c1 * x * y + c0 * y^2

theorem D1_even_parity : D1 c0 c1 α β = D1 c0 c1 β α := by
  unfold D1
  ring

/-! ## 2. n = 2: ζ(5) Defect (Odd / -1 Parity) -/

def D2 (x y : ℝ) : ℝ := c0 * x^3 - c1 * x^2 * y + c1 * x * y^2 - c0 * y^3

theorem D2_odd_parity : D2 c0 c1 β α = - D2 c0 c1 α β := by
  unfold D2
  ring

/-! ## 3. n = 3: ζ(7) Defect (Even / +1 Parity) -/

def D3 (x y : ℝ) : ℝ := c0 * x^4 - c1 * x^3 * y + c2 * x^2 * y^2 - c1 * x * y^3 + c0 * y^4

theorem D3_even_parity : D3 c0 c1 c2 α β = D3 c0 c1 c2 β α := by
  unfold D3
  ring

/-! ## 4. n = 4: ζ(9) Defect (Odd / -1 Parity) -/

def D4 (x y : ℝ) : ℝ := c0 * x^5 - c1 * x^4 * y + c2 * x^3 * y^2 - c2 * x^2 * y^3 + c1 * x * y^4 - c0 * y^5

theorem D4_odd_parity : D4 c0 c1 c2 β α = - D4 c0 c1 c2 α β := by
  unfold D4
  ring

/-! ## 5. The Graded Witten Parity Index -/

/-- The displayed four-layer parity factor: `+1` on odd `n`, `-1` on even `n`. -/
def witten_parity_factor (n : ℕ) : ℝ :=
  if n % 2 = 1 then 1 else -1

theorem witten_parity_index_evaluation :
  witten_parity_factor 1 = 1 ∧
  witten_parity_factor 2 = -1 ∧
  witten_parity_factor 3 = 1 ∧
  witten_parity_factor 4 = -1 := by
  unfold witten_parity_factor
  norm_num

end AlgebraicParity

open InfoGeometry.Arithmetic.RamanujanDefectTower
open InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

/-!
The symbolic polynomial sequence above matches the already verified finite
Bernoulli readouts for `ζ(3)`, `ζ(5)`, `ζ(7)`, and `ζ(9)`.
-/

theorem ramanujan_defect_layers_follow_witten_sequence :
    DefectParityTarget 1 (ramanujanBernoulliSide aperyBernoulliReadout 1) ∧
      DefectParityTarget 2 (ramanujanBernoulliSide zetaFiveBernoulliReadout 2) ∧
      DefectParityTarget 3 (ramanujanBernoulliSide zetaSevenBernoulliReadout 3) ∧
      DefectParityTarget 4 (ramanujanBernoulliSide zetaNineBernoulliReadout 4) := by
  exact ⟨zeta3_defect_parity, zeta5_defect_parity,
    zeta7_defect_parity, zeta9_defect_parity⟩

end InfoGeometry.Arithmetic.WittenParityIndex
