import Mathlib.Tactic

#check (inferInstance : AddCommGroup PUnit)
#check (inferInstance : Subsingleton PUnit)

example : (0 : PUnit) = PUnit.unit := rfl

instance : Zero PUnit := inferInstance

-- dummy

def f : PUnit → ℤ := fun _ => 0

example : ∀ x : PUnit, f x = 0 := by intro x; cases x; rfl
