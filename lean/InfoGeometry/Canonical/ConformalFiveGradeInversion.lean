import InfoGeometry.Canonical.ConformalInversionCore

/-!
# InfoGeometry.Canonical.ConformalFiveGradeInversion

Direct canonical five-graded conformal inversion.

This file keeps the projective closure local and canonical:

* a five-grade label type,
* an inversion that is involutive,
* the grade-swap law `k ↦ -k`,
* and the corresponding fixed zero-grade stability.

No bridge surface is imported here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConformalFiveGradeInversion

/-- The five conformal grades. -/
inductive ConformalGrade where
  | negTwo
  | negOne
  | zero
  | posOne
  | posTwo
  deriving DecidableEq, Repr

namespace ConformalGrade

/-- The grade-swapping involution on the five conformal grades. -/
def swap : ConformalGrade → ConformalGrade
  | negTwo => posTwo
  | negOne => posOne
  | zero => zero
  | posOne => negOne
  | posTwo => negTwo

@[simp] theorem swap_negTwo : swap negTwo = posTwo := rfl
@[simp] theorem swap_negOne : swap negOne = posOne := rfl
@[simp] theorem swap_zero : swap zero = zero := rfl
@[simp] theorem swap_posOne : swap posOne = negOne := rfl
@[simp] theorem swap_posTwo : swap posTwo = negTwo := rfl

@[simp] theorem swap_swap (k : ConformalGrade) : swap (swap k) = k := by
  cases k <;> rfl

end ConformalGrade

/--
A direct canonical five-graded conformal inversion.

`theta` is the projective inversion, `grade` records the conformal grade, and
`grade_swap` states that inversion exchanges the opposite grades and fixes the
middle grade.
-/
structure FiveGradedConformalInversion (L : Type*) where
  theta : L → L
  grade : L → ConformalGrade
  theta_involutive : Function.Involutive theta
  grade_swap : ∀ x : L, grade (theta x) = ConformalGrade.swap (grade x)

namespace FiveGradedConformalInversion

variable {L : Type*}
variable (G : FiveGradedConformalInversion L)

private theorem has_grade_swap (G : FiveGradedConformalInversion L) :
    ∀ x : L, G.grade (G.theta x) = ConformalGrade.swap (G.grade x) := by
  exact G.grade_swap

/-- The source sector: grade `+2`. -/
def sourceSet : Set L := {x | G.grade x = ConformalGrade.posTwo}

/-- The sink sector: grade `-2`. -/
def sinkSet : Set L := {x | G.grade x = ConformalGrade.negTwo}

/-- The outgoing boundary sector: grade `+1`. -/
def outgoingSet : Set L := {x | G.grade x = ConformalGrade.posOne}

/-- The incoming boundary sector: grade `-1`. -/
def incomingSet : Set L := {x | G.grade x = ConformalGrade.negOne}

/-- The modular center: grade `0`. -/
def centerSet : Set L := {x | G.grade x = ConformalGrade.zero}

@[simp] theorem theta_theta (x : L) : G.theta (G.theta x) = x :=
  G.theta_involutive x

/-- The five-graded inversion as a genuine self-equivalence of the carrier. -/
noncomputable def thetaEquiv : L ≃ L where
  toFun := G.theta
  invFun := G.theta
  left_inv := G.theta_involutive
  right_inv := G.theta_involutive

@[simp] theorem thetaEquiv_apply (x : L) :
    G.thetaEquiv x = G.theta x :=
  rfl

@[simp] theorem thetaEquiv_symm :
    G.thetaEquiv.symm = G.thetaEquiv := by
  apply Equiv.ext
  intro x
  rfl

theorem thetaEquiv_grade (x : L) :
    G.grade (G.thetaEquiv x) = ConformalGrade.swap (G.grade x) := by
  exact G.grade_swap x

@[simp] theorem grade_theta (x : L) :
    G.grade (G.theta x) = ConformalGrade.swap (G.grade x) :=
  G.has_grade_swap x

/--
The zero grade is stable under the inversion.

This is the canonical formulation of the mirror horizon fixed set at grade zero.
-/
@[simp] theorem zero_grade_survives_setwise
    {x : L}
    (hx : G.grade x = ConformalGrade.zero) :
    G.grade (G.theta x) = ConformalGrade.zero := by
  simpa [ConformalGrade.swap] using congrArg ConformalGrade.swap hx

/--
A negative-two grade point is carried to the positive-two grade.
-/
theorem fixed_negTwo_mem_posTwo
    {x : L}
    (hx : G.grade x = ConformalGrade.negTwo) :
    G.grade (G.theta x) = ConformalGrade.posTwo := by
  simpa [ConformalGrade.swap] using congrArg ConformalGrade.swap hx

/--
A positive-two grade point is carried to the negative-two grade.
-/
theorem fixed_posTwo_mem_negTwo
    {x : L}
    (hx : G.grade x = ConformalGrade.posTwo) :
    G.grade (G.theta x) = ConformalGrade.negTwo := by
  simpa [ConformalGrade.swap] using congrArg ConformalGrade.swap hx

/--
A negative-one grade point is carried to the positive-one grade.
-/
theorem fixed_negOne_mem_posOne
    {x : L}
    (hx : G.grade x = ConformalGrade.negOne) :
    G.grade (G.theta x) = ConformalGrade.posOne := by
  simpa [ConformalGrade.swap] using congrArg ConformalGrade.swap hx

/--
A positive-one grade point is carried to the negative-one grade.
-/
theorem fixed_posOne_mem_negOne
    {x : L}
    (hx : G.grade x = ConformalGrade.posOne) :
    G.grade (G.theta x) = ConformalGrade.negOne := by
  simpa [ConformalGrade.swap] using congrArg ConformalGrade.swap hx

/-- The source sector is carried to the sink sector. -/
theorem mem_source_iff_mem_sink (x : L) :
    x ∈ G.sourceSet ↔ G.theta x ∈ G.sinkSet := by
  change G.grade x = ConformalGrade.posTwo ↔ G.grade (G.theta x) = ConformalGrade.negTwo
  constructor
  · intro hx
    have hθ : G.grade (G.theta x) = ConformalGrade.negTwo :=
      fixed_posTwo_mem_negTwo (G := G) (x := x) hx
    simpa using hθ
  · intro hx
    have hθθ : G.grade (G.theta (G.theta x)) = ConformalGrade.posTwo := by
      have := fixed_negTwo_mem_posTwo (G := G) (x := G.theta x) hx
      simpa using this
    simpa using hθθ

/-- The incoming sector is carried to the outgoing sector. -/
theorem mem_incoming_iff_mem_outgoing (x : L) :
    x ∈ G.incomingSet ↔ G.theta x ∈ G.outgoingSet := by
  change G.grade x = ConformalGrade.negOne ↔ G.grade (G.theta x) = ConformalGrade.posOne
  constructor
  · intro hx
    have hθ : G.grade (G.theta x) = ConformalGrade.posOne :=
      fixed_negOne_mem_posOne (G := G) (x := x) hx
    simpa using hθ
  · intro hx
    have hθθ : G.grade (G.theta (G.theta x)) = ConformalGrade.negOne := by
      have := fixed_posOne_mem_negOne (G := G) (x := G.theta x) hx
      simpa using this
    simpa using hθθ

/-- The modular center is stable under inversion. -/
theorem mem_center_iff_mem_center (x : L) :
    x ∈ G.centerSet ↔ G.theta x ∈ G.centerSet := by
  change G.grade x = ConformalGrade.zero ↔ G.grade (G.theta x) = ConformalGrade.zero
  constructor
  · intro hx
    have hθ : G.grade (G.theta x) = ConformalGrade.zero :=
      zero_grade_survives_setwise (G := G) (x := x) hx
    simpa using hθ
  · intro hx
    have hθθ : G.grade (G.theta (G.theta x)) = ConformalGrade.zero := by
      have := zero_grade_survives_setwise (G := G) (x := G.theta x) hx
      simpa using this
    simpa using hθθ

end FiveGradedConformalInversion

end InfoGeometry.Canonical.ConformalFiveGradeInversion
