import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.SupergradedBracket
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

noncomputable section
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Krein
open KreinSpace
open InfoGeometry.Algebra.SupergradedBracket

namespace InfoGeometry.Clifford.ParaKahler55SUSYClosure

/-! ### 1. Para-Kähler involution on V55 -/
noncomputable def paraKahlerK : V55 →ₗ[ℝ] V55 :=
  snd55.prod fst55

@[simp] theorem fst55_apply (v : V55) : fst55 v = v.1 := rfl
@[simp] theorem snd55_apply (v : V55) : snd55 v = v.2 := rfl

theorem paraKahlerK_sq : paraKahlerK.comp paraKahlerK = (LinearMap.id : V55 →ₗ[ℝ] V55) := by
  apply LinearMap.ext
  intro v
  apply Prod.ext <;> simp [paraKahlerK]

theorem paraKahlerK_preserves_Q55 (v : V55) :
    Q55 (paraKahlerK v) = - Q55 v := by
  simp [Q55_apply, paraKahlerK, fst55_apply, snd55_apply]

/-! ### 2. 5-graded exterior spinor -/
abbrev Exterior55 := ExteriorAlgebra ℝ (Fin 5 → ℝ)

/-! ### 3. Doubled Krein carrier and SUSY bracket -/
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]
abbrev EndH₂ := DoubledSpace E →L[ℝ] DoubledSpace E

/-! ### 4. Para-Kähler 5-graded SUSY symmetry -/
/-- A symmetry of the para-Kähler 5-graded SUSY system.

    `toCLM` is a Krein-isometry on the doubled carrier.
    `commutes_paraKahler` asserts that it intertwines the para-Kähler
    generator swap on the Clifford image under any fixed spinor action `ρ`. -/
structure ParaKahler55Symmetry where
  /-- The underlying continuous linear map on the doubled carrier. -/
  toCLM : DoubledSpace E →L[ℝ] DoubledSpace E
  /-- Krein isometry. -/
  isKreinIsometry : IsKreinIsometry (H := DoubledSpace E) toCLM
  /-- Commutes with the para-Kähler swap on generators. -/
  commutes_paraKahler (ρ : Cl55 →+* (DoubledSpace E →L[ℝ] DoubledSpace E)) (v : V55) :
    toCLM.comp (ρ (CliffordAlgebra.ι Q55 v)) =
      (ρ (CliffordAlgebra.ι Q55 v)).comp toCLM

/-! ### 5. Identity and closure under composition -/
noncomputable def idSymmetry : ParaKahler55Symmetry (E := E) :=
  { toCLM := ContinuousLinearMap.id ℝ (DoubledSpace E),
    isKreinIsometry := IsKreinIsometry.id,
    commutes_paraKahler := by
      intro ρ v
      rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] }

noncomputable def composition_closure (S T : ParaKahler55Symmetry (E := E)) :
    ParaKahler55Symmetry (E := E) :=
  { toCLM := S.toCLM.comp T.toCLM,
    isKreinIsometry := IsKreinIsometry.comp S.isKreinIsometry T.isKreinIsometry,
    commutes_paraKahler := by
      intro ρ v
      calc
        (S.toCLM.comp T.toCLM).comp (ρ (CliffordAlgebra.ι Q55 v)) =
            S.toCLM.comp (T.toCLM.comp (ρ (CliffordAlgebra.ι Q55 v))) :=
              ContinuousLinearMap.comp_assoc _ _ _
        _ = S.toCLM.comp ((ρ (CliffordAlgebra.ι Q55 v)).comp T.toCLM) := by
              rw [T.commutes_paraKahler ρ v]
        _ = (S.toCLM.comp (ρ (CliffordAlgebra.ι Q55 v))).comp T.toCLM :=
              (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = ((ρ (CliffordAlgebra.ι Q55 v)).comp S.toCLM).comp T.toCLM := by
              rw [S.commutes_paraKahler ρ v]
        _ = (ρ (CliffordAlgebra.ι Q55 v)).comp (S.toCLM.comp T.toCLM) :=
              ContinuousLinearMap.comp_assoc _ _ _ }

end InfoGeometry.Clifford.ParaKahler55SUSYClosure
