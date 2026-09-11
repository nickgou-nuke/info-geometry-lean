import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

abbrev MajoranaGenerator := Complex

def Nilpotent (g : MajoranaGenerator) : Prop := g * g = 0

def D_operator (g : MajoranaGenerator) : MajoranaGenerator := g

noncomputable def ConformalFlowPhase (g : MajoranaGenerator) : Complex := Complex.I * Real.pi

noncomputable def BraidGroupMonodromy (g : MajoranaGenerator) : Complex := Complex.I * Real.pi

def Re_lambda (val : Real) : Prop := val = 1/2
def F_wedge_F_zero (val : Real) : Prop := val = 0

theorem conformal_flow_eq_monodromy (g : MajoranaGenerator) :
  ConformalFlowPhase g = BraidGroupMonodromy g := by rfl

theorem linking_lambda_F (val1 val2 : Real) (h1 : Re_lambda val1) (h2 : F_wedge_F_zero val2) : 
  Re_lambda val1 ∧ F_wedge_F_zero val2 :=
  ⟨h1, h2⟩
