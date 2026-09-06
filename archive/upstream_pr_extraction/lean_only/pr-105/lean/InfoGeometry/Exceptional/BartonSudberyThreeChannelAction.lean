import InfoGeometry.Exceptional.BartonSudberyTrialityAction

/-!
# Three-channel triality action

This file packages the already verified component actions on the three tensor
channels into one finite `Fin 3` carrier.  It does not define the
Barton--Sudbery tensor--tensor bracket or claim Jacobi closure.
-/

namespace InfoGeometry.Exceptional.BartonSudberyThreeChannelAction


open InfoGeometry.Exceptional.CompositionTriality
open InfoGeometry.Exceptional.CompositionTriality.TrialityTriple
open InfoGeometry.Exceptional.BartonSudberyTrialityAction
open scoped TensorProduct

variable {R A B : Type*} [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  {mulA : A →ₗ[R] A →ₗ[R] A}
  {mulB : B →ₗ[R] B →ₗ[R] B}

abbrev ThreeTensorChannels (R A B : Type*) [CommRing R]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] := Fin 3 → (A ⊗[R] B)

def channelAction
    (T : TrialityTriple mulA) : Module.End R (ThreeTensorChannels R A B) where
  toFun x i := match i with
    | 0 => leftTrialityAction₁ (A := A) (B := B) T (x 0)
    | 1 => leftTrialityAction₂ (A := A) (B := B) T (x 1)
    | 2 => leftTrialityAction₃ (A := A) (B := B) T (x 2)
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' r x := by
    funext i
    fin_cases i <;> simp

@[simp] theorem channelAction_apply_zero
    (T : TrialityTriple mulA) (x : ThreeTensorChannels R A B) :
    channelAction (R := R) (A := A) (B := B) T x 0 =
      leftTrialityAction₁ (A := A) (B := B) T (x 0) := rfl

@[simp] theorem channelAction_apply_one
    (T : TrialityTriple mulA) (x : ThreeTensorChannels R A B) :
    channelAction (R := R) (A := A) (B := B) T x 1 =
      leftTrialityAction₂ (A := A) (B := B) T (x 1) := rfl

@[simp] theorem channelAction_apply_two
    (T : TrialityTriple mulA) (x : ThreeTensorChannels R A B) :
    channelAction (R := R) (A := A) (B := B) T x 2 =
      leftTrialityAction₃ (A := A) (B := B) T (x 2) := rfl

theorem channelAction_commutator
    (T U : TrialityTriple mulA) :
    channelAction (R := R) (A := A) (B := B) (commutator T U) =
      endCommutator
        (channelAction (R := R) (A := A) (B := B) T)
        (channelAction (R := R) (A := A) (B := B) U) := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i
  · change leftTrialityAction₁ (A := A) (B := B) (commutator T U) (x 0) = _
    rw [leftTrialityAction₁_commutator T U]
    rfl
  · change leftTrialityAction₂ (A := A) (B := B) (commutator T U) (x 1) = _
    rw [leftTrialityAction₂_commutator T U]
    rfl
  · change leftTrialityAction₃ (A := A) (B := B) (commutator T U) (x 2) = _
    rw [leftTrialityAction₃_commutator T U]
    rfl

def rightChannelAction
    (T : TrialityTriple mulB) : Module.End R (ThreeTensorChannels R A B) where
  toFun x i := match i with
    | 0 => rightTrialityAction₁ (A := A) (B := B) T (x 0)
    | 1 => rightTrialityAction₂ (A := A) (B := B) T (x 1)
    | 2 => rightTrialityAction₃ (A := A) (B := B) T (x 2)
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' r x := by
    funext i
    fin_cases i <;> simp

theorem rightChannelAction_commutator
    (T U : TrialityTriple mulB) :
    rightChannelAction (R := R) (A := A) (B := B) (commutator T U) =
      endCommutator
        (rightChannelAction (R := R) (A := A) (B := B) T)
        (rightChannelAction (R := R) (A := A) (B := B) U) := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i
  · change rightTrialityAction₁ (A := A) (B := B) (commutator T U) (x 0) = _
    rw [rightTrialityAction₁_commutator T U]
    rfl
  · change rightTrialityAction₂ (A := A) (B := B) (commutator T U) (x 1) = _
    rw [rightTrialityAction₂_commutator T U]
    rfl
  · change rightTrialityAction₃ (A := A) (B := B) (commutator T U) (x 2) = _
    rw [rightTrialityAction₃_commutator T U]
    rfl

end InfoGeometry.Exceptional.BartonSudberyThreeChannelAction
