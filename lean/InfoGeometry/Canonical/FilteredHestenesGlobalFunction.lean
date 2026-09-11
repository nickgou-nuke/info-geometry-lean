import InfoGeometry.Canonical.FilteredHestenesGlobalOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open InfoGeometry.Krein
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredHestenesGlobalOperator

namespace InfoGeometry.Canonical.FilteredHestenesGlobalOperator.LinearFamily

variable {C : HestenesKreinCone} (F : LinearFamily C)

/-- Images of finite-stage operators depend only on the represented colimit
element.  This is the exact well-definedness condition for descent. -/
def RespectsConeRelation : Prop :=
  ∀ n x m y,
    C.ι n x = C.ι m y →
      C.ι n (F.op n x) = C.ι m (F.op m y)

variable (hsurj : JointlySurjective C)

/-- A chosen stage representing a colimit-carrier element. -/
def representativeStage (y : DoubledSpace C.LimitBase) : ℕ :=
  (hsurj y).choose

/-- A chosen finite-stage representative. -/
def representativeValue (y : DoubledSpace C.LimitBase) :
    DoubledSpace (C.Base (representativeStage hsurj y)) :=
  (hsurj y).choose_spec.choose

/-- The chosen representative maps to the original carrier element. -/
theorem representative_eq (y : DoubledSpace C.LimitBase) :
    C.ι (representativeStage hsurj y) (representativeValue hsurj y) = y :=
  (hsurj y).choose_spec.choose_spec

/-- Global function obtained by applying the finite-stage operator to a chosen
representative and returning to the filtered carrier. -/
def descendedFunction (y : DoubledSpace C.LimitBase) :
    DoubledSpace C.LimitBase :=
  C.ι (representativeStage hsurj y)
    (F.op (representativeStage hsurj y) (representativeValue hsurj y))

/-- Representative independence makes the chosen construction agree with
every canonical finite-stage representative. -/
theorem descendedFunction_ι
    (hrel : F.RespectsConeRelation)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    F.descendedFunction hsurj (C.ι n x) = C.ι n (F.op n x) := by
  unfold descendedFunction
  exact hrel
    (representativeStage hsurj (C.ι n x))
    (representativeValue hsurj (C.ι n x))
    n x
    (representative_eq hsurj (C.ι n x))

/-- The descended function is the unique function agreeing with the finite
operator family on every cone image. -/
theorem descendedFunction_unique
    (hrel : F.RespectsConeRelation)
    (T : DoubledSpace C.LimitBase → DoubledSpace C.LimitBase)
    (hT : ∀ n x, T (C.ι n x) = C.ι n (F.op n x)) :
    T = F.descendedFunction hsurj := by
  funext y
  obtain ⟨n, x, rfl⟩ := hsurj y
  rw [hT n x, F.descendedFunction_ι hsurj hrel n x]

/-- The finite-stage Hestenes law descends to the globally constructed
function. -/
theorem descendedFunction_clockAxis
    (hrel : F.RespectsConeRelation)
    (y : DoubledSpace C.LimitBase) :
    F.descendedFunction hsurj (clockAxis (E := C.LimitBase) y) =
      clockAxis (E := C.LimitBase) (F.descendedFunction hsurj y) := by
  obtain ⟨n, x, rfl⟩ := hsurj y
  have hι_phase :
      C.ι n (clockAxis (E := C.Base n) x) =
        clockAxis (E := C.LimitBase) (C.ι n x) := by
    have h := congrArg
      (fun L : DoubledSpace (C.Base n) →L[ℝ] DoubledSpace C.LimitBase => L x)
      (C.ι_hestenes n)
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    F.descendedFunction hsurj (clockAxis (E := C.LimitBase) (C.ι n x))
        =
      F.descendedFunction hsurj
        (C.ι n (clockAxis (E := C.Base n) x)) := by rw [hι_phase]
    _ = C.ι n (F.op n (clockAxis (E := C.Base n) x)) :=
      F.descendedFunction_ι hsurj hrel n _
    _ = C.ι n (clockAxis (E := C.Base n) (F.op n x)) := by
      rw [F.op_clockAxis n x]
    _ = clockAxis (E := C.LimitBase) (C.ι n (F.op n x)) := by
      have h := congrArg
        (fun L : DoubledSpace (C.Base n) →L[ℝ] DoubledSpace C.LimitBase =>
          L (F.op n x))
        (C.ι_hestenes n)
      simpa [ContinuousLinearMap.comp_apply] using h
    _ =
      clockAxis (E := C.LimitBase)
        (F.descendedFunction hsurj (C.ι n x)) := by
      rw [F.descendedFunction_ι hsurj hrel n x]

end InfoGeometry.Canonical.FilteredHestenesGlobalOperator.LinearFamily
