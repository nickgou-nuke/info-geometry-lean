import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace InfoGeometry.GrandUnification.HorizonCapacitance

open LinearMap
open FiniteDimensional

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
variable [FiniteDimensional R M]

/-! ### 1. Дефектният блок на Хоризонта (Q₀) -/

/-- Хоризонтът Q₀ се дефинира като подпространството, където Мьобиусовият туист 
    има фиксирани собствени модове (сърцевината на усукването на Клайн). -/
def HorizonDefectBlock (𝒯 : Module.End R M) : Subspace R M :=
  LinearMap.ker (𝒯 - LinearMap.id)

/-! ### 2. Алгебричен Капацитет на Хоризонта -/

/-- 
Капацитетът на Хоризонта като Холографски Кондензатор.
Математически, капацитетът е правопропорционален на размерността (броя Майоранови кванти)
на дефектния блок на Клайновата бутилка.
-/
noncomputable def horizon_capacitance (𝒯 : Module.End R M) : ℤ :=
  (Module.finrank R (HorizonDefectBlock 𝒯) : ℤ)

/-! ### 3. Rank-nullity for the fixed-point defect -/

/-- The fixed-point defect and the image of `𝒯 - id` have complementary
dimensions. Thus the finite-dimensional capacity is determined by the rank
of the deviation from the identity; a numerical value requires a separate
computation for a specified operator. -/
theorem horizon_capacitance_add_range_finrank (𝒯 : Module.End R M) :
    horizon_capacitance 𝒯 +
        (Module.finrank R (LinearMap.range (𝒯 - LinearMap.id)) : ℤ) =
      (Module.finrank R M : ℤ) := by
  unfold horizon_capacitance HorizonDefectBlock
  have h := LinearMap.finrank_range_add_finrank_ker (𝒯 - LinearMap.id)
  rw [add_comm] at h
  exact_mod_cast h

end InfoGeometry.GrandUnification.HorizonCapacitance
