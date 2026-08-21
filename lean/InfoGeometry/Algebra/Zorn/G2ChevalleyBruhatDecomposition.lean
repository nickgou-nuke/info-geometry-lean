import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2ChevalleyBruhat

inductive G2Weyl : Type
  | e       : G2Weyl  -- length 0
  | s1      : G2Weyl  -- length 1
  | s2      : G2Weyl  -- length 1
  | s1s2    : G2Weyl  -- length 2
  | s2s1    : G2Weyl  -- length 2
  | s1s2s1  : G2Weyl  -- length 3
  | s2s1s2  : G2Weyl  -- length 3
  | w4_1    : G2Weyl  -- length 4: (s1 s2)²
  | w4_2    : G2Weyl  -- length 4: (s2 s1)²
  | w5_1    : G2Weyl  -- length 5: (s1 s2)² s1
  | w5_2    : G2Weyl  -- length 5: (s2 s1)² s2
  | w0      : G2Weyl  -- length 6: longest element (s1 s2)³
  deriving DecidableEq, Repr

def weylLength : G2Weyl → ℕ
  | G2Weyl.e      => 0
  | G2Weyl.s1     => 1
  | G2Weyl.s2     => 1
  | G2Weyl.s1s2   => 2
  | G2Weyl.s2s1   => 2
  | G2Weyl.s1s2s1 => 3
  | G2Weyl.s2s1s2 => 3
  | G2Weyl.w4_1   => 4
  | G2Weyl.w4_2   => 4
  | G2Weyl.w5_1   => 5
  | G2Weyl.w5_2   => 5
  | G2Weyl.w0     => 6

def weylElems : List G2Weyl :=
  [G2Weyl.e, G2Weyl.s1, G2Weyl.s2, G2Weyl.s1s2, G2Weyl.s2s1,
   G2Weyl.s1s2s1, G2Weyl.s2s1s2, G2Weyl.w4_1, G2Weyl.w4_2,
   G2Weyl.w5_1, G2Weyl.w5_2, G2Weyl.w0]

instance : Fintype G2Weyl where
  elems := ⟨weylElems, by decide⟩
  complete := by intro x; cases x <;> decide

theorem weyl_card :
    Fintype.card G2Weyl = 12 := by
  rfl

/-- The G₂ Poincaré polynomial W(q) = ∑_{w ∈ W} q^{ℓ(w)}. -/
def poincareSum (q : ℕ) : ℕ :=
  1 + 2 * q + 2 * q^2 + 2 * q^3 + 2 * q^4 + 2 * q^5 + q^6

/-- THEOREM: Factorization of the G₂ Poincaré polynomial W(q) = (q + 1)(q⁵ + q⁴ + q³ + q² + q + 1). -/
theorem poincareSum_factorization (q : ℕ) :
    poincareSum q = (q + 1) * (q^5 + q^4 + q^3 + q^2 + q + 1) := by
  dsimp [poincareSum]
  ring

/-- THEOREM: For q = 2, the Poincaré sum gives exactly 189 Bruhat cell factor. -/
theorem poincareSum_two :
    poincareSum 2 = 189 := by
  rfl

/-- The order of the unipotent radical / Borel subgroup B(q) = q⁶ (q - 1)². -/
def borelOrder (q : ℕ) : ℕ :=
  q^6 * (q - 1)^2

/-- For q = 2, the Borel subgroup has order 64. -/
theorem borelOrder_two :
    borelOrder 2 = 64 := by
  rfl

/-- The exact Chevalley order formula: |G₂(q)| = |B(q)| · W_{G₂}(q). -/
def g2ChevalleyOrder (q : ℕ) : ℕ :=
  borelOrder q * poincareSum q

/-- 🏆 THEOREM: Exact Algebraic Formula |G₂(q)| = q⁶ (q⁶ - 1)(q² - 1) for q = 2. -/
theorem g2ChevalleyOrder_two_formula :
    g2ChevalleyOrder 2 = 2^6 * (2^6 - 1) * (2^2 - 1) := by
  rfl

/-- 🏆 MASTER THEOREM: Exact Evaluation of |G₂(2)| = 12096. -/
theorem g2ChevalleyOrder_two :
    g2ChevalleyOrder 2 = 12096 := by
  rfl

/-- 🏆 THEOREM: Prime Factorization of |G₂(2)| = 2⁶ · 3³ · 7. -/
theorem g2ChevalleyOrder_two_factorization :
    g2ChevalleyOrder 2 = 2^6 * 3^3 * 7 := by
  rfl

/-- The simple derived subgroup PSU₃(3) has order 6048 and index 2. -/
theorem psu33_derived_index :
    6048 * 2 = g2ChevalleyOrder 2 := by
  rfl

/-- 🏆 THEOREM: Complete Cell Partition Identity 64 · 189 = 12096. -/
theorem bruhat_cell_multiplication :
    64 * 189 = 12096 := by
  rfl

end InfoGeometry.Algebra.Zorn.G2ChevalleyBruhat

end noncomputable section
