import Mathlib.Tactic

noncomputable section

variable {H : Type*}

/-! Finite readout for a selected forward channel. -/
def cooper_pair_cone (majorana_mode : H → H) (forward _backward : H) : H :=
  majorana_mode forward

/-- Null-volume boundary used as a definable subset of `ℂ`. -/
def null_boundary : Set ℂ := { z | z.re = 0 }

/-- Macroscopic causality condensate: the range of `majorana_mode`. -/
def causality_condensate (majorana_mode : H → H) : Set H := Set.range majorana_mode

/-- The readout is definitionally the selected forward channel. -/
theorem cooper_pair_cone_apply (majorana_mode : H → H) (forward _backward : H) :
    cooper_pair_cone majorana_mode forward _backward = majorana_mode forward := by
  rfl

end noncomputable section
