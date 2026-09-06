import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.Real.Basic
import proofs.CartanTriality
import proofs.D4Cl11Tripotent

noncomputable section

namespace IsospinTKK

def my_alternating_group (n : ℕ) := alternatingGroup (Fin n)

theorem my_alternating_group_normal (n : ℕ) :
    Subgroup.Normal (my_alternating_group n) :=
  alternatingGroup.normal

theorem real_add_comm_thm (a b : ℝ) : a + b = b + a :=
  add_comm a b

end IsospinTKK
end noncomputable section
