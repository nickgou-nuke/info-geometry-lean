import Mathlib.Data.ZMod.Units
import InfoGeometry.Canonical.GaloisZornTrialityBridge

namespace InfoGeometry.Canonical

open GaloisZornTrialityBridge

theorem zmod3_units_card : Fintype.card (ZMod 3)ˣ = 2 := by
  decide

theorem zmod3_additive_card : Fintype.card (Multiplicative (ZMod 3)) = 3 := by
  decide

theorem no_zmod3_units_triality_group_equiv :
    ¬ Nonempty ((ZMod 3)ˣ ≃* Multiplicative (ZMod 3)) := by
  rintro ⟨e⟩
  have hcard := Fintype.card_congr e.toEquiv
  rw [zmod3_units_card, zmod3_additive_card] at hcard
  omega

end InfoGeometry.Canonical
