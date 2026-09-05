import InfoGeometry.Canonical.O55FiveGradeClosure
import InfoGeometry.Canonical.O55FiveGradeWeights
import InfoGeometry.Quantum.FiveGradedKramersModule

/-!
# Native O(5,5) five grades and Kramers grade reversal

`O55FiveGradeClosure` already owns the actual adjoint eigenspaces in
`Cl(5,5)` and proves the named `±2`, `±1`, and `0` lanes.  This file does not
replace that owner.  It supplies the missing exact bridge to the complex
square-minus-one Kramers module.

The Clifford inversion `thetaOp` and the antiunitary Kramers operator induce
the same permutation of grade labels,

`-2 ↔ +2`, `-1 ↔ +1`, `0 ↔ 0`,

but they remain different maps: `thetaOp² = +1`, whereas `T² = -1` on the
spinor carrier.
-/

noncomputable section

namespace InfoGeometry.Clifford.O55FiveGradeKramersBridge

open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Canonical.O55FiveGradeClosure
open InfoGeometry.Quantum.ComplexKramersAntiunitary
open InfoGeometry.Quantum.FiveGradedKramersModule

/-- Translate the already-owned conformal grade labels to the finite Kramers
weight labels. -/
def toKramersWeight : ConformalGrade → Weight
  | .negTwo => .minus2
  | .negOne => .minus1
  | .zero => .zero
  | .posOne => .plus1
  | .posTwo => .plus2

/-- Reverse translation of the finite labels. -/
def ofKramersWeight : Weight → ConformalGrade
  | .minus2 => .negTwo
  | .minus1 => .negOne
  | .zero => .zero
  | .plus1 => .posOne
  | .plus2 => .posTwo

/-- The two five-element index types are canonically equivalent. -/
def gradeLabelEquiv : ConformalGrade ≃ Weight where
  toFun := toKramersWeight
  invFun := ofKramersWeight
  left_inv g := by cases g <;> rfl
  right_inv w := by cases w <;> rfl

@[simp] theorem toKramersWeight_value (g : ConformalGrade) :
    (toKramersWeight g).value = toInt g := by
  cases g <;> rfl

@[simp] theorem toKramersWeight_swap (g : ConformalGrade) :
    toKramersWeight g.swap = (toKramersWeight g).opposite := by
  cases g <;> rfl

@[simp] theorem ofKramersWeight_opposite (w : Weight) :
    ofKramersWeight w.opposite = (ofKramersWeight w).swap := by
  cases w <;> rfl

/-- Parity quotient of the native O(5,5) integer grade. -/
def o55FiveParity (g : ConformalGrade) : ZMod 2 :=
  (toInt g : ZMod 2)

@[simp] theorem o55FiveParity_swap (g : ConformalGrade) :
    o55FiveParity g.swap = o55FiveParity g := by
  cases g <;> norm_num [o55FiveParity, toInt, ConformalGrade.swap]

@[simp] theorem o55FiveParity_negTwo :
    o55FiveParity ConformalGrade.negTwo = 0 := by rfl

@[simp] theorem o55FiveParity_negOne :
    o55FiveParity ConformalGrade.negOne = 1 := by rfl

@[simp] theorem o55FiveParity_zero :
    o55FiveParity ConformalGrade.zero = 0 := by rfl

@[simp] theorem o55FiveParity_posOne :
    o55FiveParity ConformalGrade.posOne = 1 := by rfl

@[simp] theorem o55FiveParity_posTwo :
    o55FiveParity ConformalGrade.posTwo = 0 := by rfl

/-- Include a spinor in the Kramers fibre carrying a native conformal grade
label. -/
def includeConformalGrade (g : ConformalGrade) : H2 →ₗ[ℂ] Carrier :=
  include (toKramersWeight g)

@[simp] theorem includeConformalGrade_hasGrade
    (g : ConformalGrade) (v : H2) :
    HasGrade (toInt g) (includeConformalGrade g v) := by
  simpa [includeConformalGrade] using
    include_hasGrade (toKramersWeight g) v

/-- Kramers transport realizes exactly the same grade-label swap as the native
Clifford inversion. -/
theorem kramers_includeConformalGrade
    (g : ConformalGrade) (v : H2) :
    kramers (includeConformalGrade g v) =
      includeConformalGrade g.swap (timeReversal v) := by
  simpa [includeConformalGrade, toKramersWeight_swap] using
    kramers_include (toKramersWeight g) v

/-- Kramers transport reverses the native O(5,5) integer weight and preserves
its parity quotient. -/
theorem kramers_o55_grade_parity_packet
    (g : ConformalGrade) (v : H2) :
    HasGrade (-toInt g) (kramers (includeConformalGrade g v)) ∧
      o55FiveParity g.swap = o55FiveParity g ∧
      kramers (kramers (includeConformalGrade g v)) =
        -includeConformalGrade g v := by
  exact ⟨kramers_hasGrade_neg (includeConformalGrade_hasGrade g v),
    o55FiveParity_swap g,
    kramers_sq (includeConformalGrade g v)⟩

/-- The native Clifford inversion and the Kramers operator have the same grade
permutation on their separate carriers. -/
theorem theta_and_kramers_share_grade_swap
    (g : ConformalGrade) (x : Alg 5)
    (hx : x ∈ gradeSpace g) (v : H2) :
    thetaOp x ∈ gradeSpace g.swap ∧
      kramers (includeConformalGrade g v) =
        includeConformalGrade g.swap (timeReversal v) := by
  exact ⟨theta_maps g x hx,
    kramers_includeConformalGrade g v⟩

/-- The actual O(5,5) commutator grade and its derived parity add together. -/
theorem o55_commutator_multigrade
    (g h k : ConformalGrade) {x y : Alg 5}
    (hx : x ∈ gradeSpace g) (hy : y ∈ gradeSpace h)
    (hgrade : toInt k = toInt g + toInt h) :
    x * y - y * x ∈ gradeSpace k ∧
      o55FiveParity k = o55FiveParity g + o55FiveParity h := by
  constructor
  · exact gradeSpace_commutator_of_sum g h k hx hy hgrade
  · unfold o55FiveParity
    rw [hgrade, Int.cast_add]

/-- Re-export the genuinely occupied five lanes from the existing O(5,5)
closure owner. -/
theorem native_o55_five_lane_packet :
    u5 ∈ gradeSpace ConformalGrade.posOne ∧
      u4 ∈ gradeSpace ConformalGrade.posOne ∧
      v5 ∈ gradeSpace ConformalGrade.negOne ∧
      v4 ∈ gradeSpace ConformalGrade.negOne ∧
      D ∈ gradeSpace ConformalGrade.zero ∧
      u5 * u4 - u4 * u5 ∈ gradeSpace ConformalGrade.posTwo ∧
      v5 * v4 - v4 * v5 ∈ gradeSpace ConformalGrade.negTwo := by
  exact ⟨u5_grade, u4_grade, v5_grade, v4_grade, D_grade,
    u5_u4_commutator_grade_pos_two,
    v5_v4_commutator_grade_neg_two⟩

/-- Complete O(5,5) five-grade/Kramers packet. -/
theorem o55_five_grade_kramers_packet
    (g : ConformalGrade) (x : Alg 5)
    (hx : x ∈ gradeSpace g) (v : H2) :
    thetaOp x ∈ gradeSpace g.swap ∧
      HasGrade (-toInt g) (kramers (includeConformalGrade g v)) ∧
      o55FiveParity g.swap = o55FiveParity g ∧
      kramers (kramers (includeConformalGrade g v)) =
        -includeConformalGrade g v := by
  exact ⟨theta_maps g x hx,
    (kramers_o55_grade_parity_packet g v).1,
    (kramers_o55_grade_parity_packet g v).2.1,
    (kramers_o55_grade_parity_packet g v).2.2⟩

end InfoGeometry.Clifford.O55FiveGradeKramersBridge
