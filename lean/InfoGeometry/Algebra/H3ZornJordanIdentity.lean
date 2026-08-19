import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.H3ZornCubicOperators
import InfoGeometry.Algebra.H3ZornQuadraticCommutation
import InfoGeometry.Exceptional.Freudenthal
import Mathlib.Algebra.Jordan.Basic

/-!
# Verified `H3Zorn` Jordan-law surface

This file defines the product induced by the cubic-data `T`-operator and proves
its Jordan identity from the McCrimmon quadratic-representation chain.  The
corresponding Mathlib `IsCommJordan` instance is installed separately in
`H3ZornJordanInstance`, which keeps the carrier and the installed instance in
distinct owner files.
-/

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Exceptional.Freudenthal

/-- Linearity of the trace pairing on `H3Zorn ℝ` represented as a linear map. -/
noncomputable def h3zornTraceBilin : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => traceBilin x y
      map_add' := fun y z => traceBilin_add_right x y z
      map_smul' := fun r y => traceBilin_smul_right r x y }
  map_add' := fun x y => by
    ext z
    exact traceBilin_add_left x y z
  map_smul' := fun r x => by
    ext z
    exact traceBilin_smul_left r x z

/-- Symmetric trilinear form associated to the cubic norm on H3Zorn. -/
noncomputable def h3zornNormTrilin : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => (1 / 6 : ℝ) * traceBilin x (crossProduct y z)
          map_add' := fun z₁ z₂ => by
            simp only [crossProduct_add_right, traceBilin_add_right, mul_add]
          map_smul' := fun c z => by
            dsimp
            simp only [crossProduct_smul_right, traceBilin_smul_right]
            ring }
      map_add' := fun y₁ y₂ => by
        ext z
        dsimp
        simp only [crossProduct_add_left, traceBilin_add_right, mul_add]
      map_smul' := fun c y => by
        ext z
        dsimp
        simp only [crossProduct_smul_left, traceBilin_smul_right]
        ring }
  map_add' := fun x₁ x₂ => by
    ext y z
    dsimp
    simp only [traceBilin_add_left, mul_add]
  map_smul' := fun c x => by
    ext y z
    dsimp
    simp only [traceBilin_smul_left]
    ring

/-- The H3Zorn cubic Jordan datum. -/
noncomputable def h3zornCubicJordanDatum : CubicJordanDatum (H3Zorn ℝ) where
  traceBilin := h3zornTraceBilin
  trace_comm x y := traceBilin_symm x y
  normCubic := normCubic
  adjointQuad := adjointQuad
  normTrilin := h3zornNormTrilin
  normTrilin_swap₁₂ x y z := by
    dsimp [h3zornNormTrilin]
    rw [traceBilin_symm x (crossProduct y z)]
    rw [traceBilin_crossProduct_assoc y z x]
    rw [crossProduct_symm z x]
  normTrilin_swap₂₃ x y z := by
    dsimp [h3zornNormTrilin]
    rw [crossProduct_symm y z]
  normTrilin_self x := by
    dsimp [h3zornNormTrilin]
    rw [crossProduct_self, traceBilin_smul_right, traceBilin_symm x (adjointQuad x), mccrimmon_identity_13 x]
    ring

/-- The installed product induced by the current trilinear `T` data. -/
noncomputable def candidateJordanMul (X Y : H3Zorn ℝ) : H3Zorn ℝ :=
  (1 / 2 : ℝ) • T X 1 Y

/-- The installed product is commutative because the cubic `T`-operator is
symmetric in the outer variables. -/
theorem candidateJordanMul_comm (X Y : H3Zorn ℝ) :
    candidateJordanMul X Y = candidateJordanMul Y X := by
  simpa [candidateJordanMul] using H3Zorn.T_symm_outer X 1 Y

/-- The diagonal cubic basepoint is a right unit for the induced product. -/
@[simp] theorem candidateJordanMul_one_right (X : H3Zorn ℝ) :
    candidateJordanMul X 1 = X := by
  simp [candidateJordanMul, H3Zorn.T_one_one, smul_smul]

/-- The diagonal cubic basepoint is a left unit for the induced product. -/
@[simp] theorem candidateJordanMul_one_left (X : H3Zorn ℝ) :
    candidateJordanMul 1 X = X := by
  rw [candidateJordanMul_comm, candidateJordanMul_one_right]

/-- The installed product is additive in its left variable. -/
theorem candidateJordanMul_add_left (X₁ X₂ Y : H3Zorn ℝ) :
    candidateJordanMul (X₁ + X₂) Y =
      candidateJordanMul X₁ Y + candidateJordanMul X₂ Y := by
  simp [candidateJordanMul, H3Zorn.T_add_left]

/-- The installed product is additive in its right variable. -/
theorem candidateJordanMul_add_right (X Y₁ Y₂ : H3Zorn ℝ) :
    candidateJordanMul X (Y₁ + Y₂) =
      candidateJordanMul X Y₁ + candidateJordanMul X Y₂ := by
  calc
    candidateJordanMul X (Y₁ + Y₂) =
        candidateJordanMul (Y₁ + Y₂) X := by
          rw [candidateJordanMul_comm]
    _ = candidateJordanMul Y₁ X + candidateJordanMul Y₂ X := by
          rw [candidateJordanMul_add_left]
    _ = candidateJordanMul X Y₁ + candidateJordanMul X Y₂ := by
          rw [candidateJordanMul_comm X Y₁, candidateJordanMul_comm X Y₂]

/-- The installed product is homogeneous in its left variable. -/
theorem candidateJordanMul_smul_left (r : ℝ) (X Y : H3Zorn ℝ) :
    candidateJordanMul (r • X) Y = r • candidateJordanMul X Y := by
  simp [candidateJordanMul, H3Zorn.T_smul_left, smul_smul, mul_comm]

/-- The installed product is homogeneous in its right variable. -/
theorem candidateJordanMul_smul_right (r : ℝ) (X Y : H3Zorn ℝ) :
    candidateJordanMul X (r • Y) = r • candidateJordanMul X Y := by
  calc
    candidateJordanMul X (r • Y) =
        candidateJordanMul (r • Y) X := by
          rw [candidateJordanMul_comm]
    _ = r • candidateJordanMul Y X := by
          rw [candidateJordanMul_smul_left]
    _ = r • candidateJordanMul X Y := by
          rw [candidateJordanMul_comm]

/-- The Jordan product equation at one concrete pair. -/
def H3ZornJordanProductLawAt (x y : H3Zorn ℝ) : Prop :=
  candidateJordanMul (candidateJordanMul x y) (candidateJordanMul x x) =
    candidateJordanMul x (candidateJordanMul y (candidateJordanMul x x))

/-- The pointwise Jordan product law is exactly the scalar-free `T`-commutation
equation after expanding the installed product. -/
theorem H3ZornJordanProductLawAt_iff_TJordanCommutation (x y : H3Zorn ℝ) :
    H3ZornJordanProductLawAt x y ↔
      T (T x 1 y) 1 (T x 1 x) = T x 1 (T y 1 (T x 1 x)) := by
  constructor
  · intro h
    have h1 : ((1 / 2 : ℝ) ^ 3) • (T (T x 1 y) 1 (T x 1 x)) =
        ((1 / 2 : ℝ) ^ 3) • (T x 1 (T y 1 (T x 1 x))) := by
      simpa [H3ZornJordanProductLawAt, candidateJordanMul,
        H3Zorn.T_smul_left, H3Zorn.T_smul_right, smul_smul,
        mul_comm, mul_left_comm, mul_assoc] using h
    have h2 := congrArg (fun z => (8 : ℝ) • z) h1
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using h2
  · intro h
    have h1 : ((1 / 2 : ℝ) ^ 3) • (T (T x 1 y) 1 (T x 1 x)) =
        ((1 / 2 : ℝ) ^ 3) • (T x 1 (T y 1 (T x 1 x))) := by
      simp [h]
    simpa [H3ZornJordanProductLawAt, candidateJordanMul,
      H3Zorn.T_smul_left, H3Zorn.T_smul_right, smul_smul,
      mul_comm, mul_left_comm, mul_assoc] using h1

/-- The global Jordan product law is the pointwise law at every pair. -/
def H3ZornJordanProductLaw : Prop :=
  ∀ x y : H3Zorn ℝ, H3ZornJordanProductLawAt x y

/-- Coordinate-free quadratic-Jordan commutation identity for the `T`-operator. -/
def TJordanCommutation : Prop :=
  ∀ a b : H3Zorn ℝ,
    T (T a 1 b) 1 (T a 1 a) =
      T a 1 (T b 1 (T a 1 a))

/-- The global Jordan product law is equivalent to the pointwise `T`
commutation law. -/
theorem H3ZornJordanProductLaw_iff_TJordanCommutation :
    H3ZornJordanProductLaw ↔ TJordanCommutation := by
  constructor
  · intro h a b
    simpa [TJordanCommutation] using
      (H3ZornJordanProductLawAt_iff_TJordanCommutation a b).1 (h a b)
  · intro h x y
    exact (H3ZornJordanProductLawAt_iff_TJordanCommutation x y).2 (h x y)

/-- McCrimmon's quadratic-representation identities close the scalar-free
`T`-commutation law. -/
theorem TJordanCommutation_holds : TJordanCommutation := by
  intro a b
  rw [T_symm_outer (T a 1 b) 1 (T a 1 a)]
  rw [T_symm_outer b 1 (T a 1 a)]
  have h₁ := four_U a (T a 1 b)
  have h₂ := congrArg (fun W : H3Zorn ℝ => T a 1 W) (four_U a b)
  simp only [sub_eq_add_neg, T_add_right, T_smul_right] at h₂
  have hc := P_comm_U a b
  rw [← hc] at h₁
  have htneg (W : H3Zorn ℝ) : T a 1 (-W) = -T a 1 W := by
    rw [show -W = (-1 : ℝ) • W by module, T_smul_right]
    module
  rw [htneg] at h₂
  have h := h₁.symm.trans h₂
  have h' := congrArg
    (fun W : H3Zorn ℝ =>
      (2 : ℝ) • T a 1 (T a 1 (T a 1 b)) - W)
    h
  convert h' using 1 <;> module

/-- Scalar normal form for the quadratic representation identity extracted
from `four_U`.  This is the clean coefficient-level theorem underlying the
installed-product reconstruction. -/
theorem H3ZornJordanQuadraticReconstruction (X Y : H3Zorn ℝ) :
    U X Y = (1 / 2 : ℝ) • T X 1 (T X 1 Y) - (1 / 4 : ℝ) • T (T X 1 X) 1 Y := by
  have h := congrArg (fun Z : H3Zorn ℝ => (1 / 4 : ℝ) • Z) (four_U X Y)
  simp only [smul_sub, smul_smul] at h
  norm_num at h
  simpa [smul_add, smul_sub, smul_smul, T_smul_left, T_smul_right] using h

/-- The installed product satisfies the Jordan identity. -/
theorem H3ZornJordanProductLaw_holds : H3ZornJordanProductLaw :=
  H3ZornJordanProductLaw_iff_TJordanCommutation.mpr TJordanCommutation_holds

/--
A theorem that the cubic norm axioms of a `CubicJordanDatum` imply that the
induced multiplication satisfies the commutative Jordan ring axioms (`IsCommJordan`).
This records the cubic-to-Jordan algebra translation as an explicit theorem
surface.
-/
theorem isCommJordan_of_cubicJordanDatum [CommMagma (H3Zorn ℝ)]
    (_D : CubicJordanDatum (H3Zorn ℝ))
    (h_mul : ∀ x y : H3Zorn ℝ, x * y = candidateJordanMul x y := by intros; rfl) :
    IsCommJordan (H3Zorn ℝ) where
  lmul_comm_rmul_rmul x y := by
    simp_rw [h_mul]
    exact H3ZornJordanProductLaw_holds x y

end InfoGeometry.Algebra
