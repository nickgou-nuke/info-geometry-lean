import InfoGeometry.Quantum.TriadicBogoliubovBridge
import InfoGeometry.Canonical.MongeAmpereDualSheetBridge

namespace InfoGeometry.Quantum.TriadicWeylBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.MongeAmpereDualSheetBridge
open TriadicBogoliubov

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- A doubled-space generator is Weyl-compatible when both cross-sheet blocks vanish. -/
def IsWeylCompatible (H : EndH) : Prop :=
  plusToMinusBlockMap (E := E) H = 0 ∧ minusToPlusBlockMap (E := E) H = 0

@[simp] theorem plusToMinusBlockMap_triadicGenerator {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (q a : ι → H₂) :
    plusToMinusBlockMap (E := E) (triadicGenerator (E := E) w q a) =
      ∑ i, w i • plusToMinusBlockMap (E := E) (dyadicKrein (E := E) (q i) (a i)) := by
  ext x
  simp [plusToMinusBlockMap, triadicGenerator, ContinuousLinearMap.comp_apply]

@[simp] theorem minusToPlusBlockMap_triadicGenerator {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (q a : ι → H₂) :
    minusToPlusBlockMap (E := E) (triadicGenerator (E := E) w q a) =
      ∑ i, w i • minusToPlusBlockMap (E := E) (dyadicKrein (E := E) (q i) (a i)) := by
  ext x
  simp [minusToPlusBlockMap, triadicGenerator, ContinuousLinearMap.comp_apply]

theorem triadicGenerator_blockDiagonal_of_compatibility {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (q a : ι → H₂)
    (h_compat : ∀ i, IsWeylCompatible (E := E) (dyadicKrein (E := E) (q i) (a i))) :
    IsWeylCompatible (E := E) (triadicGenerator (E := E) w q a) := by
  constructor
  · rw [plusToMinusBlockMap_triadicGenerator]
    apply Finset.sum_eq_zero
    intro i _
    simp [(h_compat i).1]
  · rw [minusToPlusBlockMap_triadicGenerator]
    apply Finset.sum_eq_zero
    intro i _
    simp [(h_compat i).2]

end InfoGeometry.Quantum.TriadicWeylBridge
