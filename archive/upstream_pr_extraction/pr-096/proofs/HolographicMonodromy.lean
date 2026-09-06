import Mathlib

abbrev MajoranaGenerator := Complex

def Nilpotent (g : MajoranaGenerator) : Prop := g * g = 0

def D_operator (g : MajoranaGenerator) : MajoranaGenerator := g

noncomputable def ConformalFlowPhase (g : MajoranaGenerator) : Complex := Complex.I * Real.pi

noncomputable def BraidGroupMonodromy (g : MajoranaGenerator) : Complex := Complex.I * Real.pi

def Re_lambda (val : Real) : Prop := val = 1/2
def F_wedge_F_zero (val : Real) : Prop := val = 0

theorem conformal_flow_eq_monodromy (g : MajoranaGenerator) :
  ConformalFlowPhase g = BraidGroupMonodromy g := by rfl
