import InfoGeometry.Clifford.Cl11GradingSl2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalChargeLinear

/-!
# The Cl(1,1) grading triple on a Freudenthal doublet

This owner couples the already verified native `sl₂` triple from
`Cl11GradingSl2` to two copies of the existing Freudenthal charge carrier.
It does not assert the missing mixed `E₈` bracket or construct a new
Freudenthal invariant.
-/

namespace InfoGeometry.Exceptional.FreudenthalCl11Doublet

open InfoGeometry.Exceptional.Freudenthal

noncomputable section

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

abbrev Doublet := FreudenthalCharge J × FreudenthalCharge J

def eAction : Module.End ℝ (Doublet (J := J)) where
  toFun z := (0, -z.1)
  map_add' x y := by
    simp
    abel
  map_smul' r x := by simp

def fAction : Module.End ℝ (Doublet (J := J)) where
  toFun z := (-z.2, 0)
  map_add' x y := by
    simp
    abel
  map_smul' r x := by simp

def hAction : Module.End ℝ (Doublet (J := J)) where
  toFun z := (-z.1, z.2)
  map_add' x y := by
    simp
    abel
  map_smul' r x := by simp

/-- A zero-grade endomorphism acts componentwise on the two Freudenthal
copies.  This is the concrete `g₀` action on the doublet carrier. -/
def zeroGradeDoubletAction
    (T : Module.End ℝ (FreudenthalCharge J)) :
    Module.End ℝ (Doublet (J := J)) where
  toFun z := (T z.1, T z.2)
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp] theorem zeroGradeDoubletAction_apply
    (T : Module.End ℝ (FreudenthalCharge J))
    (z : Doublet (J := J)) :
    zeroGradeDoubletAction T z = (T z.1, T z.2) := rfl

/-! The zero-grade action is independent of the `sl₂` grading direction. -/

theorem zeroGradeDoubletAction_commutes_e
    (T : Module.End ℝ (FreudenthalCharge J)) :
    ⁅zeroGradeDoubletAction T, eAction (J := J)⁆ = 0 := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨a, b⟩
  simp [Ring.lie_def, Module.End.mul_apply,
    zeroGradeDoubletAction, eAction]

theorem zeroGradeDoubletAction_commutes_f
    (T : Module.End ℝ (FreudenthalCharge J)) :
    ⁅zeroGradeDoubletAction T, fAction (J := J)⁆ = 0 := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨a, b⟩
  simp [Ring.lie_def, Module.End.mul_apply,
    zeroGradeDoubletAction, fAction]

theorem zeroGradeDoubletAction_commutes_h
    (T : Module.End ℝ (FreudenthalCharge J)) :
    ⁅zeroGradeDoubletAction T, hAction (J := J)⁆ = 0 := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨a, b⟩
  simp [Ring.lie_def, Module.End.mul_apply,
    zeroGradeDoubletAction, hAction]

/-! The diagonal zero-grade action is a genuine representation on the
doublet.  This is the componentwise Lie-action statement needed before
assembling any larger graded bracket. -/

theorem zeroGradeDoubletAction_commutator
    (T U : Module.End ℝ (FreudenthalCharge J)) :
    ⁅zeroGradeDoubletAction T, zeroGradeDoubletAction U⁆ =
      zeroGradeDoubletAction ⁅T, U⁆ := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨a, b⟩
  apply Prod.ext
  · rfl
  · rfl

/-- The componentwise zero-grade action is a genuine Lie representation on
the Freudenthal doublet. -/
noncomputable def zeroGradeDoubletActionLieHom :
    Module.End ℝ (FreudenthalCharge J) →ₗ⁅ℝ⁆
      Module.End ℝ (Doublet (J := J)) where
  toFun := zeroGradeDoubletAction
  map_add' T U := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨a, b⟩
    rfl
  map_smul' r T := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨a, b⟩
    rfl
  map_lie' := by
    intro T U
    exact (zeroGradeDoubletAction_commutator (J := J) T U).symm

theorem zeroGradeDoubletActionLieHom_injective :
    Function.Injective (zeroGradeDoubletActionLieHom (J := J)) := by
  intro T U h
  change zeroGradeDoubletAction T = zeroGradeDoubletAction U at h
  apply LinearMap.ext
  intro x
  have hx := congrArg
    (fun K : Module.End ℝ (Doublet (J := J)) => K (x, 0)) h
  change (zeroGradeDoubletAction T) (x, 0) =
    (zeroGradeDoubletAction U) (x, 0) at hx
  exact congrArg Prod.fst hx

@[simp] theorem eAction_apply (z : Doublet (J := J)) :
    eAction z = (0, -z.1) := rfl

@[simp] theorem fAction_apply (z : Doublet (J := J)) :
    fAction z = (-z.2, 0) := rfl

@[simp] theorem hAction_apply (z : Doublet (J := J)) :
    hAction z = (-z.1, z.2) := rfl

@[simp] theorem hAction_first_grade (x : FreudenthalCharge J) :
    hAction (J := J) (x, 0) = (-x, 0) := by
  simp [hAction]

@[simp] theorem hAction_second_grade (x : FreudenthalCharge J) :
    hAction (J := J) (0, x) = (0, x) := by
  simp [hAction]

@[simp] theorem eAction_second_to_first (x : FreudenthalCharge J) :
    eAction (J := J) (0, x) = (0, 0) := by
  simp [eAction]

@[simp] theorem eAction_first_to_second (x : FreudenthalCharge J) :
    eAction (J := J) (x, 0) = (0, -x) := by
  simp [eAction]

@[simp] theorem fAction_first_to_second (x : FreudenthalCharge J) :
    fAction (J := J) (x, 0) = (0, 0) := by
  simp [fAction]

@[simp] theorem fAction_second_to_first (x : FreudenthalCharge J) :
    fAction (J := J) (0, x) = (-x, 0) := by
  simp [fAction]

theorem bracket_h_e :
    ⁅hAction (J := J), eAction (J := J)⁆ =
      (2 : ℝ) • eAction (J := J) := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨⟨a, b, x, y⟩, z₂⟩
  simp [Ring.lie_def, Module.End.mul_apply, eAction, hAction,
    sub_eq_add_neg, two_smul]

theorem bracket_h_f :
    ⁅hAction (J := J), fAction (J := J)⁆ =
      (-2 : ℝ) • fAction (J := J) := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨z₁, ⟨a, b, x, y⟩⟩
  simp [Ring.lie_def, Module.End.mul_apply, fAction, hAction,
    sub_eq_add_neg, two_smul]

theorem bracket_e_f :
    ⁅eAction (J := J), fAction (J := J)⁆ = hAction (J := J) := by
  apply LinearMap.ext
  intro z
  ext <;> simp [Ring.lie_def, Module.End.mul_apply, eAction, fAction,
    hAction]

theorem cl11_sl2_doublet_relations :
    ⁅hAction (J := J), eAction (J := J)⁆ = (2 : ℝ) • eAction (J := J) ∧
      ⁅hAction (J := J), fAction (J := J)⁆ = (-2 : ℝ) • fAction (J := J) ∧
        ⁅eAction (J := J), fAction (J := J)⁆ = hAction (J := J) := by
  exact ⟨bracket_h_e, bracket_h_f, bracket_e_f⟩

theorem eAction_sq :
    eAction (J := J) * eAction (J := J) = 0 := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨a, b⟩
  simp [eAction, Module.End.mul_apply]

theorem fAction_sq :
    fAction (J := J) * fAction (J := J) = 0 := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨a, b⟩
  simp [fAction, Module.End.mul_apply]

theorem hAction_sq :
    hAction (J := J) * hAction (J := J) = 1 := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨a, b⟩
  simp [hAction, Module.End.mul_apply]

end
end InfoGeometry.Exceptional.FreudenthalCl11Doublet
