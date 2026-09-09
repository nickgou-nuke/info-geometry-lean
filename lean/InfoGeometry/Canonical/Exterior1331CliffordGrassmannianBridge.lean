import InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
import InfoGeometry.Canonical.ExteriorPluckerPureSpinorCompatibility

/-!
# The `1 + 3 + 3 + 1` exterior/Clifford index packet

This owner records the finite graded index data used by the existing
exterior-to-Peirce equivalence.  It deliberately does not identify Zorn
multiplication with the exterior product, nor claim that individual
homogeneous pieces are ideals.
-/

namespace InfoGeometry.Canonical.Exterior1331CliffordGrassmannianBridge

noncomputable section

def degree1331 : Fin 8 → Fin 4
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1
  | 4 => 3 | 5 => 2 | 6 => 2 | 7 => 2

def even1331 (i : Fin 8) : Prop := degree1331 i = 0 ∨ degree1331 i = 2
def odd1331 (i : Fin 8) : Prop := degree1331 i = 1 ∨ degree1331 i = 3

local instance : DecidablePred odd1331 := fun i => Classical.propDecidable _

theorem degree1331_packet :
    (Finset.univ.filter (fun i => degree1331 i = 0)).card = 1 ∧
      (Finset.univ.filter (fun i => degree1331 i = 1)).card = 3 ∧
      (Finset.univ.filter (fun i => degree1331 i = 2)).card = 3 ∧
      (Finset.univ.filter (fun i => degree1331 i = 3)).card = 1 := by
  decide

theorem even1331_card :
    (Finset.univ.filter (fun i => degree1331 i = 0 ∨ degree1331 i = 2)).card = 4 := by
  decide

theorem odd1331_card :
    (Finset.univ.filter (fun i => degree1331 i = 1 ∨ degree1331 i = 3)).card = 4 := by
  decide

theorem degree1331_dimensional_packet :
    1 + 3 + 3 + 1 = 8 := by norm_num

theorem degree1331_even_odd_packet :
    4 + 4 = 8 := by norm_num

