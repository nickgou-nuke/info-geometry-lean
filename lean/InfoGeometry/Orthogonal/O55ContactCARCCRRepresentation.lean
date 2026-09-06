import InfoGeometry.Orthogonal.O55PinContactBridge
import InfoGeometry.Orthogonal.O55ContactGrading

/-!
# Faithful `so(5,5)` action on a common CAR--CCR carrier

The split-orthogonal Lie algebra acts diagonally on a doubled vector carrier.
The two copies support the exact one-mode CAR.  A countable occupation
coordinate supports the algebraic Heisenberg CCR.  The pointwise orthogonal
action commutes with both ladder systems and preserves contact degree.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

abbrev FermionCarrier55 := Vector55 × Vector55
abbrev FermionEnd55 := Module.End ℝ FermionCarrier55

def fermionAnnihilation : FermionEnd55 where
  toFun p := (p.2, 0)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

def fermionCreation : FermionEnd55 where
  toFun p := (0, p.1)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

@[simp] theorem fermionAnnihilation_apply (x y : Vector55) :
    fermionAnnihilation (x, y) = (y, 0) := rfl

@[simp] theorem fermionCreation_apply (x y : Vector55) :
    fermionCreation (x, y) = (0, x) := rfl

theorem fermionAnnihilation_sq :
    fermionAnnihilation * fermionAnnihilation = 0 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rfl

theorem fermionCreation_sq :
    fermionCreation * fermionCreation = 0 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rfl

theorem fermion_CAR :
    fermionAnnihilation * fermionCreation +
      fermionCreation * fermionAnnihilation = 1 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [Module.End.mul_apply, fermionAnnihilation, fermionCreation]

/-- Diagonal action on both CAR sheets. -/
def diagonalFermionAction (A : O55Lie) : FermionEnd55 where
  toFun p := ((A : End55) p.1, (A : End55) p.2)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

@[simp] theorem diagonalFermionAction_apply
    (A : O55Lie) (x y : Vector55) :
    diagonalFermionAction A (x, y) = ((A : End55) x, (A : End55) y) := rfl

def diagonalFermionRepresentationLinear :
    O55Lie →ₗ[ℝ] FermionEnd55 where
  toFun := diagonalFermionAction
  map_add' A B := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    rfl
  map_smul' c A := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    rfl

theorem diagonalFermionAction_bracket (A B : O55Lie) :
    diagonalFermionAction ⁅A, B⁆ =
      ⁅diagonalFermionAction A, diagonalFermionAction B⁆ := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext <;> rfl

def diagonalFermionRepresentation :
    O55Lie →ₗ⁅ℝ⁆ FermionEnd55 where
  toLinearMap := diagonalFermionRepresentationLinear
  map_lie' := by
    intro A B
    change diagonalFermionAction ⁅A, B⁆ =
      ⁅diagonalFermionAction A, diagonalFermionAction B⁆
    exact diagonalFermionAction_bracket A B

theorem diagonalFermionRepresentation_injective :
    Function.Injective diagonalFermionRepresentation := by
  intro A B h
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun h (x, 0)
  change ((A : End55) x, (A : End55) 0) =
    ((B : End55) x, (B : End55) 0) at hx
  exact congrArg Prod.fst hx

theorem diagonalFermion_commutes_annihilation (A : O55Lie) :
    diagonalFermionAction A * fermionAnnihilation =
      fermionAnnihilation * diagonalFermionAction A := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [Module.End.mul_apply, diagonalFermionAction,
    fermionAnnihilation]

theorem diagonalFermion_commutes_creation (A : O55Lie) :
    diagonalFermionAction A * fermionCreation =
      fermionCreation * diagonalFermionAction A := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [Module.End.mul_apply, diagonalFermionAction,
    fermionCreation]

abbrev CommonCarrier55 := ℕ → FermionCarrier55
abbrev CommonEnd55 := Module.End ℝ CommonCarrier55

def bosonCreation : CommonEnd55 where
  toFun f n := match n with
    | 0 => 0
    | m + 1 => f m
  map_add' f g := by
    funext n
    cases n <;> simp
  map_smul' c f := by
    funext n
    cases n <;> simp

def bosonAnnihilation : CommonEnd55 where
  toFun f n := (n + 1 : ℝ) • f (n + 1)
  map_add' f g := by
    funext n
    simp [smul_add]
  map_smul' c f := by
    funext n
    simp [smul_smul]
    ring

@[simp] theorem bosonCreation_zero (f : CommonCarrier55) :
    bosonCreation f 0 = 0 := rfl

@[simp] theorem bosonCreation_succ (f : CommonCarrier55) (n : ℕ) :
    bosonCreation f (n + 1) = f n := rfl

@[simp] theorem bosonAnnihilation_apply (f : CommonCarrier55) (n : ℕ) :
    bosonAnnihilation f n = (n + 1 : ℝ) • f (n + 1) := rfl

theorem boson_CCR :
    bosonAnnihilation * bosonCreation -
      bosonCreation * bosonAnnihilation = 1 := by
  apply LinearMap.ext
  intro f
  funext n
  cases n with
  | zero => simp [Module.End.mul_apply]
  | succ n =>
      simp [Module.End.mul_apply, Nat.cast_add, Nat.cast_one]
      module

def pointwiseLift (T : FermionEnd55) : CommonEnd55 where
  toFun f n := T (f n)
  map_add' f g := by
    funext n
    simp
  map_smul' c f := by
    funext n
    simp

@[simp] theorem pointwiseLift_apply
    (T : FermionEnd55) (f : CommonCarrier55) (n : ℕ) :
    pointwiseLift T f n = T (f n) := rfl

theorem pointwiseLift_mul (S T : FermionEnd55) :
    pointwiseLift (S * T) = pointwiseLift S * pointwiseLift T := by
  apply LinearMap.ext
  intro f
  funext n
  rfl

theorem pointwiseLift_bracket (S T : FermionEnd55) :
    pointwiseLift ⁅S, T⁆ = ⁅pointwiseLift S, pointwiseLift T⁆ := by
  apply LinearMap.ext
  intro f
  funext n
  rfl

def commonAction (A : O55Lie) : CommonEnd55 :=
  pointwiseLift (diagonalFermionAction A)

def commonRepresentationLinear : O55Lie →ₗ[ℝ] CommonEnd55 where
  toFun := commonAction
  map_add' A B := by
    apply LinearMap.ext
    intro f
    funext n
    rfl
  map_smul' c A := by
    apply LinearMap.ext
    intro f
    funext n
    rfl

theorem commonAction_bracket (A B : O55Lie) :
    commonAction ⁅A, B⁆ = ⁅commonAction A, commonAction B⁆ := by
  unfold commonAction
  rw [diagonalFermionAction_bracket, pointwiseLift_bracket]

def commonRepresentation : O55Lie →ₗ⁅ℝ⁆ CommonEnd55 where
  toLinearMap := commonRepresentationLinear
  map_lie' := by
    intro A B
    change commonAction ⁅A, B⁆ = ⁅commonAction A, commonAction B⁆
    exact commonAction_bracket A B

theorem commonRepresentation_injective :
    Function.Injective commonRepresentation := by
  intro A B h
  apply diagonalFermionRepresentation_injective
  apply LinearMap.ext
  rintro ⟨x, y⟩
  let f : CommonCarrier55 := fun _ => (x, y)
  have hf := LinearMap.congr_fun h f
  simpa [commonRepresentation, commonRepresentationLinear, commonAction,
    pointwiseLift, diagonalFermionRepresentation,
    diagonalFermionRepresentationLinear, diagonalFermionAction] using
    congrFun hf 0

theorem common_commutes_fermionAnnihilation (A : O55Lie) :
    commonAction A * pointwiseLift fermionAnnihilation =
      pointwiseLift fermionAnnihilation * commonAction A := by
  unfold commonAction
  rw [← pointwiseLift_mul, ← pointwiseLift_mul,
    diagonalFermion_commutes_annihilation]

theorem common_commutes_fermionCreation (A : O55Lie) :
    commonAction A * pointwiseLift fermionCreation =
      pointwiseLift fermionCreation * commonAction A := by
  unfold commonAction
  rw [← pointwiseLift_mul, ← pointwiseLift_mul,
    diagonalFermion_commutes_creation]

theorem common_commutes_bosonCreation (A : O55Lie) :
    commonAction A * bosonCreation = bosonCreation * commonAction A := by
  apply LinearMap.ext
  intro f
  funext n
  cases n <;> simp [commonAction, Module.End.mul_apply]

theorem common_commutes_bosonAnnihilation (A : O55Lie) :
    commonAction A * bosonAnnihilation = bosonAnnihilation * commonAction A := by
  apply LinearMap.ext
  intro f
  funext n
  simp [commonAction, Module.End.mul_apply]

def commonCommutator (S T : CommonEnd55) : CommonEnd55 := S * T - T * S

def representedEuler : CommonEnd55 := commonAction contactEuler

def IsRepresentedGrade (k : ℤ) (T : CommonEnd55) : Prop :=
  commonCommutator representedEuler T = (k : ℝ) • T

theorem commonRepresentation_preserves_grade
    {k : ℤ} {A : O55Lie}
    (hA : A ∈ realContactGradeSpace k) :
    IsRepresentedGrade k (commonAction A) := by
  unfold IsRepresentedGrade representedEuler commonCommutator
  have hsource : ⁅contactEuler, A⁆ = (k : ℝ) • A := by
    apply Subtype.ext
    exact hA
  calc
    commonAction contactEuler * commonAction A -
        commonAction A * commonAction contactEuler =
      commonAction ⁅contactEuler, A⁆ := by
        symm
        exact commonAction_bracket contactEuler A
    _ = commonAction ((k : ℝ) • A) := by rw [hsource]
    _ = (k : ℝ) • commonAction A := by
      exact commonRepresentationLinear.map_smul (k : ℝ) A

theorem common_carrier_packet
    {k : ℤ} {A : O55Lie} (hA : A ∈ realContactGradeSpace k) :
    fermionAnnihilation * fermionAnnihilation = 0 ∧
      fermionCreation * fermionCreation = 0 ∧
      fermionAnnihilation * fermionCreation +
        fermionCreation * fermionAnnihilation = 1 ∧
      bosonAnnihilation * bosonCreation -
        bosonCreation * bosonAnnihilation = 1 ∧
      IsRepresentedGrade k (commonAction A) ∧
      commonAction A * pointwiseLift fermionAnnihilation =
        pointwiseLift fermionAnnihilation * commonAction A ∧
      commonAction A * pointwiseLift fermionCreation =
        pointwiseLift fermionCreation * commonAction A ∧
      commonAction A * bosonCreation = bosonCreation * commonAction A ∧
      commonAction A * bosonAnnihilation = bosonAnnihilation * commonAction A := by
  exact ⟨fermionAnnihilation_sq, fermionCreation_sq, fermion_CAR,
    boson_CCR, commonRepresentation_preserves_grade hA,
    common_commutes_fermionAnnihilation A,
    common_commutes_fermionCreation A,
    common_commutes_bosonCreation A,
    common_commutes_bosonAnnihilation A⟩

end InfoGeometry.Orthogonal.O55Contact
