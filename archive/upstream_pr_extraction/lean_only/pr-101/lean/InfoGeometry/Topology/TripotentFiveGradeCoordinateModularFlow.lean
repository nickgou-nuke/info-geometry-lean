import InfoGeometry.Topology.TripotentFiveGradeMirrorTopological
import InfoGeometry.Topology.SymbolicLatentModularFlow

/-!
# Weighted modular flow on five-grade coordinates

The finite discrete grade carrier admits no nontrivial continuous real flow.
The real coordinate carrier does: each coordinate is dilated by the
exponential of its integer grade.  The mirror reverses this flow.
-/

namespace InfoGeometry.Topology.TripotentFiveGradeCoordinateModularFlow

open InfoGeometry.Physics.Algebra
open InfoGeometry.Topology
open InfoGeometry.Topology.TripotentFiveGradeMirrorTopological

noncomputable section

def gradeDilation (t : ℝ) (f : FiveGrade → ℝ) : FiveGrade → ℝ :=
  fun k => Real.exp (t * (fiveGradeValue k : ℝ)) * f k

theorem gradeDilation_apply (t : ℝ) (f : FiveGrade → ℝ) (k : FiveGrade) :
    gradeDilation t f k = Real.exp (t * (fiveGradeValue k : ℝ)) * f k := rfl

theorem continuous_gradeDilation :
    Continuous (fun p : ℝ × (FiveGrade → ℝ) => gradeDilation p.1 p.2) := by
  apply continuous_pi
  intro k
  exact
    (Real.continuous_exp.comp (continuous_fst.mul continuous_const)).mul
      (continuous_apply k |>.comp continuous_snd)

def fiveGradeCoordinateModularFlow :
    SymbolicLatentModularFlow (FiveGrade → ℝ) where
  act := gradeDilation
  continuous_act := continuous_gradeDilation
  zero_apply := by
    intro f
    funext k
    simp [gradeDilation]
  add_apply := by
    intro s t f
    funext k
    simp only [gradeDilation]
    have harg :
        (s + t) * (fiveGradeValue k : ℝ) =
          s * (fiveGradeValue k : ℝ) + t * (fiveGradeValue k : ℝ) := by
      ring
    rw [harg, Real.exp_add]
    ring

@[simp] theorem fiveGradeCoordinateModularFlow_apply
    (t : ℝ) (f : FiveGrade → ℝ) :
    fiveGradeCoordinateModularFlow.act t f = gradeDilation t f := rfl

def fiveGradeCoordinateMirrorInvolution :
    SymbolicLatentInvolution (FiveGrade → ℝ) where
  toFun := coordinateMirror
  continuous_toFun := continuous_coordinateMirror
  involutive := by
    intro f
    funext k
    simp [coordinateMirror]

theorem fiveGradeCoordinateMirror_reverses_flow
    (t : ℝ) (f : FiveGrade → ℝ) :
    fiveGradeCoordinateMirrorInvolution
        (fiveGradeCoordinateModularFlow.act t f) =
      fiveGradeCoordinateModularFlow.act (-t)
        (fiveGradeCoordinateMirrorInvolution f) := by
  funext k
  simp only [fiveGradeCoordinateMirrorInvolution, fiveGradeCoordinateModularFlow,
    gradeDilation, coordinateMirror, fiveGradeValue_mirror]
  simp only [Int.cast_neg]
  rw [show
      t * -(fiveGradeValue k : ℝ) =
        (-t) * (fiveGradeValue k : ℝ) by ring]

def fiveGradeCoordinateModularReversal :
    SymbolicLatentModularReversal fiveGradeCoordinateModularFlow where
  involution := fiveGradeCoordinateMirrorInvolution
  reverses_flow := fiveGradeCoordinateMirror_reverses_flow

end
end InfoGeometry.Topology.TripotentFiveGradeCoordinateModularFlow
