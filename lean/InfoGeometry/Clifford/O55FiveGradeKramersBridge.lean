import InfoGeometry.Canonical.O55FiveGradeClosure
import InfoGeometry.Canonical.O55FiveGradeWeights
import InfoGeometry.Quantum.FiveGradedKramersModule

/-! Bridge between the native O(5,5) five-grade carrier and the finite
Kramers fibre.  The carriers and their involutions remain distinct. -/

noncomputable section
namespace InfoGeometry.Clifford.O55FiveGradeKramersBridge

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Canonical.O55FiveGradeClosure
open InfoGeometry.Quantum.ComplexKramersAntiunitary
open InfoGeometry.Quantum.FiveGradedKramersModule

def toKramersWeight : ConformalGrade → Weight
  | .negTwo => .minus2 | .negOne => .minus1 | .zero => .zero
  | .posOne => .plus1 | .posTwo => .plus2

def ofKramersWeight : Weight → ConformalGrade
  | .minus2 => .negTwo | .minus1 => .negOne | .zero => .zero
  | .plus1 => .posOne | .plus2 => .posTwo

def gradeLabelEquiv : ConformalGrade ≃ Weight where
  toFun := toKramersWeight
  invFun := ofKramersWeight
  left_inv g := by cases g <;> rfl
  right_inv w := by cases w <;> rfl

@[simp] theorem toKramersWeight_value (g : ConformalGrade) :
    (toKramersWeight g).value = toInt g := by cases g <;> rfl

@[simp] theorem toKramersWeight_swap (g : ConformalGrade) :
    toKramersWeight g.swap = (toKramersWeight g).opposite := by
  cases g <;> rfl

def o55FiveParity (g : ConformalGrade) : ZMod 2 := (toInt g : ZMod 2)

@[simp] theorem o55FiveParity_swap (g : ConformalGrade) :
    o55FiveParity g.swap = o55FiveParity g := by
  cases g <;> decide

def includeConformalGrade (g : ConformalGrade) : H2 →ₗ[ℂ] Carrier :=
  fibreInclude (toKramersWeight g)

@[simp] theorem includeConformalGrade_hasGrade (g : ConformalGrade) (v : H2) :
    HasGrade (toInt g) (includeConformalGrade g v) := by
  simpa [includeConformalGrade] using include_hasGrade (toKramersWeight g) v

theorem kramers_includeConformalGrade (g : ConformalGrade) (v : H2) :
    kramers (includeConformalGrade g v) =
      includeConformalGrade g.swap (timeReversal v) := by
  simpa [includeConformalGrade, toKramersWeight_swap] using
    kramers_include (toKramersWeight g) v

theorem kramers_o55_grade_parity_packet (g : ConformalGrade) (v : H2) :
    HasGrade (-toInt g) (kramers (includeConformalGrade g v)) ∧
      o55FiveParity g.swap = o55FiveParity g ∧
      kramers (kramers (includeConformalGrade g v)) =
        -includeConformalGrade g v := by
  exact ⟨kramers_hasGrade_neg (includeConformalGrade_hasGrade g v),
    o55FiveParity_swap g, kramers_sq (includeConformalGrade g v)⟩

theorem theta_and_kramers_share_grade_swap (g : ConformalGrade) (x : Alg 5)
    (hx : x ∈ gradeSpace g) (v : H2) :
    thetaOp x ∈ gradeSpace g.swap ∧
      kramers (includeConformalGrade g v) =
        includeConformalGrade g.swap (timeReversal v) := by
  exact ⟨theta_maps g x hx, kramers_includeConformalGrade g v⟩

theorem native_o55_five_lane_packet :
    u5 ∈ gradeSpace ConformalGrade.posOne ∧
      u4 ∈ gradeSpace ConformalGrade.posOne ∧
      v5 ∈ gradeSpace ConformalGrade.negOne ∧
      v4 ∈ gradeSpace ConformalGrade.negOne ∧
      D ∈ gradeSpace ConformalGrade.zero := by
  exact ⟨u5_grade, u4_grade, v5_grade, v4_grade, D_grade⟩

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
end noncomputable section
