import Mathlib
import InfoGeometry.Orthogonal.O55D5RootMultigrading

/-!
# Witt-matrix realization of the split `O(5,5)` root system

Use the Witt carrier `K⁵ ⊕ K⁵` with involution exchanging the two isotropic
summands.  The split-orthogonal Lie algebra is the skew fixed space of the
Witt adjoint.  The forty `D₅` root matrices and the five Cartan matrices are
constructed explicitly.

The main theorem is the full multigraded root equation

`[H(h), E_r] = (sᵢ hᵢ + sⱼ hⱼ) E_r`.

The construction is finite matrix algebra.  It neither invokes spacetime nor
identifies the root spaces with physical particles.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Witt

open scoped Matrix
open InfoGeometry.Orthogonal.O55D5

abbrev Side := Fin 2
abbrev Index := Side × Axis
abbrev Mat10 := Matrix Index Index ℂ

/-- Exchange the two Witt sheets. -/
def flipSide : Side → Side := fun s => if s = 0 then 1 else 0

@[simp] theorem flipSide_zero : flipSide 0 = 1 := by
  rfl

@[simp] theorem flipSide_one : flipSide 1 = 0 := by
  rfl

@[simp] theorem flipSide_flipSide (s : Side) : flipSide (flipSide s) = s := by
  fin_cases s <;> rfl

/-- Exchange the two isotropic copies while retaining the axis. -/
def flipIndex : Index → Index := fun p => (flipSide p.1, p.2)

@[simp] theorem flipIndex_flipIndex (p : Index) :
    flipIndex (flipIndex p) = p := by
  rcases p with ⟨s, i⟩
  simp [flipIndex]

/-- The sheet exchange as a finite equivalence. -/
def flipIndexEquiv : Index ≃ Index where
  toFun := flipIndex
  invFun := flipIndex
  left_inv := flipIndex_flipIndex
  right_inv := flipIndex_flipIndex

@[simp] theorem flipIndex_eq_iff {p q : Index} :
    flipIndex p = q ↔ p = flipIndex q := by
  constructor
  · intro h
    calc
      p = flipIndex (flipIndex p) := (flipIndex_flipIndex p).symm
      _ = flipIndex q := congrArg flipIndex h
  · intro h
    calc
      flipIndex p = flipIndex (flipIndex q) := congrArg flipIndex h
      _ = q := flipIndex_flipIndex q

/-- Positive Witt basis index. -/
def plus (i : Axis) : Index := (0, i)

/-- Negative Witt basis index. -/
def minus (i : Axis) : Index := (1, i)

@[simp] theorem flip_plus (i : Axis) : flipIndex (plus i) = minus i := by
  rfl

@[simp] theorem flip_minus (i : Axis) : flipIndex (minus i) = plus i := by
  rfl

/-- Explicit matrix unit. -/
def matrixUnit (p q : Index) : Mat10 := fun a b =>
  if a = p ∧ b = q then 1 else 0

/-- Witt adjoint `X^♯_{pq}=X_{bar q,bar p}`.  In block notation this is
`J Xᵀ J` for the off-diagonal Witt metric. -/
def wittAdjoint (X : Mat10) : Mat10 := fun p q =>
  X (flipIndex q) (flipIndex p)

@[simp] theorem wittAdjoint_zero : wittAdjoint (0 : Mat10) = 0 := by
  rfl

@[simp] theorem wittAdjoint_add (X Y : Mat10) :
    wittAdjoint (X + Y) = wittAdjoint X + wittAdjoint Y := by
  rfl

@[simp] theorem wittAdjoint_neg (X : Mat10) :
    wittAdjoint (-X) = -wittAdjoint X := by
  rfl

@[simp] theorem wittAdjoint_sub (X Y : Mat10) :
    wittAdjoint (X - Y) = wittAdjoint X - wittAdjoint Y := by
  rfl

@[simp] theorem wittAdjoint_smul (c : ℂ) (X : Mat10) :
    wittAdjoint (c • X) = c • wittAdjoint X := by
  rfl

@[simp] theorem wittAdjoint_involutive (X : Mat10) :
    wittAdjoint (wittAdjoint X) = X := by
  ext p q
  simp [wittAdjoint]

@[simp] theorem wittAdjoint_matrixUnit (p q : Index) :
    wittAdjoint (matrixUnit p q) =
      matrixUnit (flipIndex q) (flipIndex p) := by
  ext a b
  simp [wittAdjoint, matrixUnit, and_comm]

/-- The Witt adjoint reverses multiplication. -/
theorem wittAdjoint_mul (X Y : Mat10) :
    wittAdjoint (X * Y) = wittAdjoint Y * wittAdjoint X := by
  classical
  ext p q
  simp only [wittAdjoint, Matrix.mul_apply]
  calc
    ∑ x, X (flipIndex q) x * Y x (flipIndex p) =
        ∑ x, X (flipIndex q) (flipIndex x) *
          Y (flipIndex x) (flipIndex p) := by
            simpa using
              (Equiv.sum_comp flipIndexEquiv
                (fun x => X (flipIndex q) x * Y x (flipIndex p))).symm
    _ = ∑ x, Y (flipIndex x) (flipIndex p) *
          X (flipIndex q) (flipIndex x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = _ := rfl

/-- Split-orthogonal infinitesimal condition. -/
def IsSplitOrthogonal (X : Mat10) : Prop :=
  wittAdjoint X = -X

@[simp] theorem isSplitOrthogonal_zero :
    IsSplitOrthogonal (0 : Mat10) := by
  simp [IsSplitOrthogonal]

/-- The split-orthogonal condition is closed under commutators. -/
theorem isSplitOrthogonal_commutator {X Y : Mat10}
    (hX : IsSplitOrthogonal X) (hY : IsSplitOrthogonal Y) :
    IsSplitOrthogonal (X * Y - Y * X) := by
  unfold IsSplitOrthogonal at hX hY ⊢
  rw [wittAdjoint_sub, wittAdjoint_mul, wittAdjoint_mul, hX, hY]
  noncomm_ring

/-- Native Mathlib Lie subalgebra of Witt-skew matrices. -/
def splitO55Lie : LieSubalgebra ℂ Mat10 where
  carrier := {X | IsSplitOrthogonal X}
  zero_mem' := isSplitOrthogonal_zero
  add_mem' := by
    intro X Y hX hY
    unfold IsSplitOrthogonal at hX hY ⊢
    change wittAdjoint X + wittAdjoint Y = -(X + Y)
    rw [hX, hY]
    simp only [neg_add]
  smul_mem' := by
    intro c X hX
    unfold IsSplitOrthogonal at hX ⊢
    change wittAdjoint (c • X) = -(c • X)
    rw [wittAdjoint_smul, hX]
    simp
  lie_mem' := by
    intro X Y hX hY
    change IsSplitOrthogonal (X * Y - Y * X)
    exact isSplitOrthogonal_commutator hX hY

/-- Weight read by a diagonal Witt-Cartan element. -/
def indexWeight (h : Axis → ℂ) (p : Index) : ℂ :=
  if p.1 = 0 then h p.2 else -h p.2

@[simp] theorem indexWeight_plus (h : Axis → ℂ) (i : Axis) :
    indexWeight h (plus i) = h i := by
  simp [indexWeight, plus]

@[simp] theorem indexWeight_minus (h : Axis → ℂ) (i : Axis) :
    indexWeight h (minus i) = -h i := by
  simp [indexWeight, minus]

@[simp] theorem indexWeight_flip (h : Axis → ℂ) (p : Index) :
    indexWeight h (flipIndex p) = -indexWeight h p := by
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [indexWeight, flipIndex, plus, minus]

/-- General diagonal split Cartan matrix. -/
def cartanMatrix (h : Axis → ℂ) : Mat10 := fun p q =>
  if p = q then indexWeight h p else 0

@[simp] theorem wittAdjoint_cartanMatrix (h : Axis → ℂ) :
    wittAdjoint (cartanMatrix h) = -cartanMatrix h := by
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [wittAdjoint, cartanMatrix]
  · have hflip : flipIndex q ≠ flipIndex p := by
      intro h
      apply hpq
      exact flipIndexEquiv.injective h.symm
    simp [wittAdjoint, cartanMatrix, hpq, hflip]

/-- Every diagonal Cartan matrix belongs to the split-orthogonal algebra. -/
def cartanElement (h : Axis → ℂ) : splitO55Lie :=
  ⟨cartanMatrix h, wittAdjoint_cartanMatrix h⟩

@[simp] theorem cartan_mul_matrixUnit
    (h : Axis → ℂ) (p q : Index) :
    cartanMatrix h * matrixUnit p q =
      indexWeight h p • matrixUnit p q := by
  classical
  ext a b
  by_cases hap : a = p <;> by_cases hbq : b = q <;>
    simp [Matrix.mul_apply, cartanMatrix, matrixUnit, indexWeight, hap, hbq]

@[simp] theorem matrixUnit_mul_cartan
    (h : Axis → ℂ) (p q : Index) :
    matrixUnit p q * cartanMatrix h =
      indexWeight h q • matrixUnit p q := by
  classical
  ext a b
  by_cases hap : a = p <;> by_cases hbq : b = q <;>
    simp [Matrix.mul_apply, cartanMatrix, matrixUnit, indexWeight, hap, hbq]

/-- Matrix-unit root equation for the diagonal Cartan. -/
theorem cartan_commutator_matrixUnit
    (h : Axis → ℂ) (p q : Index) :
    cartanMatrix h * matrixUnit p q -
        matrixUnit p q * cartanMatrix h =
      (indexWeight h p - indexWeight h q) • matrixUnit p q := by
  rw [cartan_mul_matrixUnit, matrixUnit_mul_cartan]
  module

/-- Root character evaluated on a diagonal Cartan coefficient. -/
def rootCharacter (h : Axis → ℂ) (r : Root) : ℂ :=
  (r.leftSign.value : ℂ) * h r.i +
    (r.rightSign.value : ℂ) * h r.j

/-- The forty standard `D₅` root matrices. -/
def rootMatrix (r : Root) : Mat10 :=
  match r.leftSign, r.rightSign with
  | .pos, .pos =>
      matrixUnit (plus r.i) (minus r.j) -
        matrixUnit (plus r.j) (minus r.i)
  | .neg, .neg =>
      matrixUnit (minus r.i) (plus r.j) -
        matrixUnit (minus r.j) (plus r.i)
  | .pos, .neg =>
      matrixUnit (plus r.i) (plus r.j) -
        matrixUnit (minus r.j) (minus r.i)
  | .neg, .pos =>
      matrixUnit (plus r.j) (plus r.i) -
        matrixUnit (minus r.i) (minus r.j)

@[simp] theorem wittAdjoint_rootMatrix (r : Root) :
    wittAdjoint (rootMatrix r) = -rootMatrix r := by
  cases hL : r.leftSign <;> cases hR : r.rightSign <;>
    simp [rootMatrix, hL, hR]

/-- Each `D₅` root matrix is a split-orthogonal Lie element. -/
def rootElement (r : Root) : splitO55Lie :=
  ⟨rootMatrix r, wittAdjoint_rootMatrix r⟩

/-- Full `ℤ⁵` root equation. -/
theorem cartan_commutator_rootMatrix
    (h : Axis → ℂ) (r : Root) :
    cartanMatrix h * rootMatrix r - rootMatrix r * cartanMatrix h =
      rootCharacter h r • rootMatrix r := by
  cases hL : r.leftSign <;> cases hR : r.rightSign
  all_goals
    simp only [rootMatrix, hL, hR]
    simp only [mul_sub, sub_mul]
    rw [cartan_mul_matrixUnit, matrixUnit_mul_cartan,
      cartan_mul_matrixUnit, matrixUnit_mul_cartan]
    simp [rootCharacter, RootSign.value, indexWeight, plus, minus, hL, hR]
    module

/-- The contact grading selects the first two isotropic axes. -/
def contactCartanCoefficient : Axis → ℂ := fun i =>
  if i = 0 ∨ i = 1 then 1 else 0

/-- Euler/grading matrix for the `|2|` collapse. -/
def contactGradingMatrix : Mat10 :=
  cartanMatrix contactCartanCoefficient

/-- The root character of the contact grading is the integral collapsed
degree. -/
theorem rootCharacter_contact (r : Root) :
    rootCharacter contactCartanCoefficient r = (r.contactDegree : ℂ) := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
    simp_all [rootCharacter, contactCartanCoefficient,
      Root.contactDegree, Root.multiDegree, Root.i, Root.j,
      RootSign.value] <;> norm_num

/-- Every root is homogeneous for the contact Euler operator. -/
theorem contactGrading_rootMatrix (r : Root) :
    contactGradingMatrix * rootMatrix r -
        rootMatrix r * contactGradingMatrix =
      (r.contactDegree : ℂ) • rootMatrix r := by
  rw [contactGradingMatrix, cartan_commutator_rootMatrix,
    rootCharacter_contact]

/-- Cartan matrices commute. -/
theorem cartanMatrix_commute (h k : Axis → ℂ) :
    cartanMatrix h * cartanMatrix k =
      cartanMatrix k * cartanMatrix h := by
  classical
  ext p q
  simp [Matrix.mul_apply, cartanMatrix]
  split_ifs with hpq <;> subst_vars <;> ring

/-- The contact grading matrix itself lies in `so(5,5)`. -/
def contactGradingElement : splitO55Lie :=
  cartanElement contactCartanCoefficient

/-- Root-level realization packet. -/
theorem o55_witt_root_packet (r : Root) :
    IsSplitOrthogonal (rootMatrix r) ∧
      contactGradingMatrix * rootMatrix r -
          rootMatrix r * contactGradingMatrix =
        (r.contactDegree : ℂ) • rootMatrix r := by
  exact ⟨wittAdjoint_rootMatrix r, contactGrading_rootMatrix r⟩

end InfoGeometry.Orthogonal.O55Witt

end noncomputable section
