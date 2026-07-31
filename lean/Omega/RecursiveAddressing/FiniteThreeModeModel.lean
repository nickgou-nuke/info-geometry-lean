import Omega.Topos.NullTrichotomy

namespace Omega.RecursiveAddressing

inductive AbsenceRef where
  | loc
  | cmp
  | glue
  deriving DecidableEq, Repr

/-! Every one of the three explicitly enumerated absence references is
admissible.  The reflexive equality is the concrete total predicate; unlike a
`True` wrapper it retains the reference in the proposition. -/
def Adm : AbsenceRef → Prop := fun r => r = r

def LocSec : AbsenceRef → Prop
  | .loc => False
  | .cmp => AbsenceRef.cmp = AbsenceRef.cmp
  | .glue => AbsenceRef.glue = AbsenceRef.glue

def CompSec : AbsenceRef → Prop
  | .loc => False
  | .cmp => False
  | .glue => AbsenceRef.glue = AbsenceRef.glue

def Sec : AbsenceRef → Prop := fun _ => False

/-- A concrete finite witness exhibiting the three structural absence modes. -/
theorem paper_finite_three_mode_model_seeds :
    ∃ rLoc rCmp rGlue : AbsenceRef,
      Omega.Topos.NullLoc Adm LocSec rLoc ∧
      Omega.Topos.NullCmp Adm LocSec CompSec rCmp ∧
      Omega.Topos.NullGlue Adm CompSec Sec rGlue := by
  refine ⟨.loc, .cmp, .glue, ?_, ?_, ?_⟩ <;>
    simp [Omega.Topos.NullLoc, Omega.Topos.NullCmp, Omega.Topos.NullGlue, Adm, LocSec,
      CompSec, Sec]

end Omega.RecursiveAddressing
