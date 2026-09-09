import InfoGeometry.Orthogonal.O55WittRootRepresentation

/-!
# The real split form `so(5,5)` and its complexification

The complex Witt-skew matrices form `so(10,ℂ)`.  The matrices with real
coefficients form the split real Lie algebra `so(5,5)`.  This file constructs
that real carrier directly and proves that entrywise complexification sends
its Cartan and root matrices to the complex `D₅` owners.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Real

open scoped Matrix
open InfoGeometry.Orthogonal.O55D5
open InfoGeometry.Orthogonal.O55Witt

abbrev RealMat10 := Matrix Index Index ℝ

/-- Real Witt adjoint. -/
def realWittAdjoint (X : RealMat10) : RealMat10 := fun p q =>
  X (flipIndex q) (flipIndex p)

@[simp] theorem realWittAdjoint_add (X Y : RealMat10) :
    realWittAdjoint (X + Y) = realWittAdjoint X + realWittAdjoint Y := rfl

@[simp] theorem realWittAdjoint_smul (c : ℝ) (X : RealMat10) :
    realWittAdjoint (c • X) = c • realWittAdjoint X := rfl

@[simp] theorem realWittAdjoint_sub (X Y : RealMat10) :
    realWittAdjoint (X - Y) = realWittAdjoint X - realWittAdjoint Y := rfl

@[simp] theorem realWittAdjoint_neg (X : RealMat10) :
    realWittAdjoint (-X) = -realWittAdjoint X := rfl

@[simp] theorem realWittAdjoint_involutive (X : RealMat10) :
    realWittAdjoint (realWittAdjoint X) = X := by
  ext p q
  simp [realWittAdjoint]

/-- Real Witt adjoint reverses multiplication. -/
theorem realWittAdjoint_mul (X Y : RealMat10) :
    realWittAdjoint (X * Y) =
      realWittAdjoint Y * realWittAdjoint X := by
  classical
  ext p q
  simp only [realWittAdjoint, Matrix.mul_apply]
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

/-- Infinitesimal split-orthogonal condition over the reals. -/
def IsRealSplitOrthogonal (X : RealMat10) : Prop :=
  realWittAdjoint X = -X

/-- Native real split Lie algebra. -/
def realSplitO55Lie : LieSubalgebra ℝ RealMat10 where
  carrier := {X | IsRealSplitOrthogonal X}
  zero_mem' := by
    change realWittAdjoint 0 = -(0 : RealMat10)
    ext p q
    simp [realWittAdjoint]
  add_mem' := by
    intro X Y hX hY
    change realWittAdjoint (X + Y) = -(X + Y)
    rw [realWittAdjoint_add, hX, hY]
    abel
  smul_mem' := by
    intro c X hX
    change realWittAdjoint (c • X) = -(c • X)
    rw [realWittAdjoint_smul, hX]
    simp
  lie_mem' := by
    intro X Y hX hY
    change IsRealSplitOrthogonal (X * Y - Y * X)
    unfold IsRealSplitOrthogonal at hX hY ⊢
    rw [realWittAdjoint_sub, realWittAdjoint_mul,
      realWittAdjoint_mul, hX, hY]
    noncomm_ring

/-- Real matrix unit. -/
def realMatrixUnit (p q : Index) : RealMat10 := fun a b =>
  if a = p ∧ b = q then 1 else 0

@[simp] theorem realWittAdjoint_matrixUnit (p q : Index) :
    realWittAdjoint (realMatrixUnit p q) =
      realMatrixUnit (flipIndex q) (flipIndex p) := by
  ext a b
  simp [realWittAdjoint, realMatrixUnit, and_comm]

/-- Real Cartan weight. -/
def realIndexWeight (h : Axis → ℝ) (p : Index) : ℝ :=
  if p.1 = 0 then h p.2 else -h p.2

/-- Real diagonal Witt-Cartan matrix. -/
def realCartanMatrix (h : Axis → ℝ) : RealMat10 := fun p q =>
  if p = q then realIndexWeight h p else 0

@[simp] theorem realWittAdjoint_cartanMatrix (h : Axis → ℝ) :
    realWittAdjoint (realCartanMatrix h) = -realCartanMatrix h := by
  ext p q
  rcases p with ⟨sp, i⟩
  rcases q with ⟨sq, j⟩
  fin_cases sp <;> fin_cases sq <;>
    by_cases hij : i = j <;>
      simp [realWittAdjoint, realCartanMatrix, realIndexWeight,
        flipIndex, eq_comm, hij]

/-- Real root matrices. -/
def realRootMatrix (r : Root) : RealMat10 :=
  match r.leftSign, r.rightSign with
  | .pos, .pos =>
      realMatrixUnit (plus r.i) (minus r.j) -
        realMatrixUnit (plus r.j) (minus r.i)
  | .neg, .neg =>
      realMatrixUnit (minus r.i) (plus r.j) -
        realMatrixUnit (minus r.j) (plus r.i)
  | .pos, .neg =>
      realMatrixUnit (plus r.i) (plus r.j) -
        realMatrixUnit (minus r.j) (minus r.i)
  | .neg, .pos =>
      realMatrixUnit (plus r.j) (plus r.i) -
        realMatrixUnit (minus r.i) (minus r.j)

@[simp] theorem realWittAdjoint_rootMatrix (r : Root) :
    realWittAdjoint (realRootMatrix r) = -realRootMatrix r := by
  cases hL : r.leftSign <;> cases hR : r.rightSign <;>
    simp [realRootMatrix, hL, hR]

/-- Every root matrix is in the real split form. -/
def realRootElement (r : Root) : realSplitO55Lie :=
  ⟨realRootMatrix r, realWittAdjoint_rootMatrix r⟩

/-- Real root character. -/
def realRootCharacter (h : Axis → ℝ) (r : Root) : ℝ :=
  (r.leftSign.value : ℝ) * h r.i +
    (r.rightSign.value : ℝ) * h r.j

@[simp] theorem realCartan_mul_matrixUnit
    (h : Axis → ℝ) (p q : Index) :
    realCartanMatrix h * realMatrixUnit p q =
      realIndexWeight h p • realMatrixUnit p q := by
  classical
  ext a b
  by_cases hap : a = p <;> by_cases hbq : b = q <;>
    simp [Matrix.mul_apply, realCartanMatrix, realMatrixUnit, hap, hbq]

@[simp] theorem realMatrixUnit_mul_cartan
    (h : Axis → ℝ) (p q : Index) :
    realMatrixUnit p q * realCartanMatrix h =
      realIndexWeight h q • realMatrixUnit p q := by
  classical
  ext a b
  by_cases hap : a = p <;> by_cases hbq : b = q <;>
    simp [Matrix.mul_apply, realCartanMatrix, realMatrixUnit, hap, hbq]

/-- Full real root equation. -/
theorem realCartan_commutator_rootMatrix
    (h : Axis → ℝ) (r : Root) :
    realCartanMatrix h * realRootMatrix r -
        realRootMatrix r * realCartanMatrix h =
      realRootCharacter h r • realRootMatrix r := by
  cases hL : r.leftSign <;> cases hR : r.rightSign
  all_goals
    simp only [realRootMatrix, hL, hR]
    rw [mul_sub, sub_mul,
      realCartan_mul_matrixUnit, realMatrixUnit_mul_cartan,
      realCartan_mul_matrixUnit, realMatrixUnit_mul_cartan]
    simp [realRootCharacter, realIndexWeight, RootSign.value,
      plus, minus, hL, hR]
    module

/-- Real contact Cartan coefficient. -/
def realContactCartanCoefficient : Axis → ℝ := fun i =>
  if i = 0 ∨ i = 1 then 1 else 0

/-- Real contact Euler element. -/
def realContactGradingMatrix : RealMat10 :=
  realCartanMatrix realContactCartanCoefficient

/-- Root equation for the real contact five-grading. -/
theorem realContactGrading_rootMatrix (r : Root) :
    realContactGradingMatrix * realRootMatrix r -
        realRootMatrix r * realContactGradingMatrix =
      (r.contactDegree : ℝ) • realRootMatrix r := by
  rw [realContactGradingMatrix, realCartan_commutator_rootMatrix]
  congr 1
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
    simp_all [realRootCharacter, realContactCartanCoefficient,
      Root.contactDegree, Root.multiDegree, Root.i, Root.j,
      RootSign.value] <;> norm_num

/-- Entrywise complexification. -/
def complexifyMatrix (X : RealMat10) : Mat10 := fun p q =>
  (X p q : ℂ)

@[simp] theorem complexifyMatrix_add (X Y : RealMat10) :
    complexifyMatrix (X + Y) = complexifyMatrix X + complexifyMatrix Y := by
  ext p q
  simp [complexifyMatrix]

@[simp] theorem complexifyMatrix_mul (X Y : RealMat10) :
    complexifyMatrix (X * Y) = complexifyMatrix X * complexifyMatrix Y := by
  ext p q
  simp [complexifyMatrix, Matrix.mul_apply]

@[simp] theorem complexifyMatrix_sub (X Y : RealMat10) :
    complexifyMatrix (X - Y) = complexifyMatrix X - complexifyMatrix Y := by
  ext p q
  simp [complexifyMatrix]

@[simp] theorem complexify_realMatrixUnit (p q : Index) :
    complexifyMatrix (realMatrixUnit p q) = matrixUnit p q := by
  ext a b
  by_cases h : a = p ∧ b = q <;>
    simp [complexifyMatrix, realMatrixUnit, matrixUnit, h]

@[simp] theorem complexify_realRootMatrix (r : Root) :
    complexifyMatrix (realRootMatrix r) = rootMatrix r := by
  cases hL : r.leftSign <;> cases hR : r.rightSign <;>
    simp [realRootMatrix, rootMatrix, hL, hR]

@[simp] theorem complexify_realCartanMatrix (h : Axis → ℝ) :
    complexifyMatrix (realCartanMatrix h) =
      cartanMatrix (fun i => (h i : ℂ)) := by
  ext p q
  rcases p with ⟨sp, i⟩
  rcases q with ⟨sq, j⟩
  fin_cases sp <;> fin_cases sq <;>
    by_cases hij : i = j <;>
      simp [complexifyMatrix, realCartanMatrix, cartanMatrix,
        realIndexWeight, indexWeight, eq_comm, hij]

/-- The real contact grading complexifies to the complex contact grading. -/
@[simp] theorem complexify_realContactGradingMatrix :
    complexifyMatrix realContactGradingMatrix = contactGradingMatrix := by
  rw [realContactGradingMatrix, complexify_realCartanMatrix]
  congr 1
  funext i
  by_cases hi : i = 0 ∨ i = 1 <;>
    simp [realContactCartanCoefficient, contactCartanCoefficient, hi]

/-- Real split form and complex root realization in one theorem packet. -/
theorem real_o55_complexification_packet (r : Root) :
    IsRealSplitOrthogonal (realRootMatrix r) ∧
    realContactGradingMatrix * realRootMatrix r -
        realRootMatrix r * realContactGradingMatrix =
      (r.contactDegree : ℝ) • realRootMatrix r ∧
    complexifyMatrix (realRootMatrix r) = rootMatrix r ∧
    complexifyMatrix realContactGradingMatrix = contactGradingMatrix := by
  exact ⟨realWittAdjoint_rootMatrix r,
    realContactGrading_rootMatrix r,
    complexify_realRootMatrix r,
    complexify_realContactGradingMatrix⟩

end InfoGeometry.Orthogonal.O55Real

end noncomputable section
