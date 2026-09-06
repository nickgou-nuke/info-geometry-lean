import InfoGeometry.Core.PeirceDecomposition
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Jordan Peirce decomposition induced by an associative algebra

Let `A` be an associative real algebra and let `f : A` be idempotent.  The
special Jordan product is

`x ∘ y = (1 / 2) • (x * y + y * x)`.

The associative four-block Peirce decomposition relative to `f`

* `A₁₁ = f A f`,
* `A₁₀ = f A (1-f)`,
* `A₀₁ = (1-f) A f`,
* `A₀₀ = (1-f) A (1-f)`

collapses under left Jordan multiplication by `f` to the three eigenvalues
`1`, `1/2`, and `0`:

* `A₁₁ ⊆ J₁(f)`,
* `A₁₀, A₀₁ ⊆ J_{1/2}(f)`,
* `A₀₀ ⊆ J₀(f)`.

This file keeps the eigenspace interface elementwise.  It does not yet package
these predicates as `Submodule`s or assert a `DirectSum`; those are downstream
structural upgrades.
-/

namespace InfoGeometry.Core.JordanPeirceDecomposition

open InfoGeometry.Core.PeirceDecomposition

section SpecialJordan

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The special Jordan product induced by the associative multiplication. -/
def jordanMul (x y : A) : A :=
  (1 / 2 : ℝ) • (x * y + y * x)

@[simp]
theorem jordanMul_comm (x y : A) :
    jordanMul x y = jordanMul y x := by
  simp [jordanMul, add_comm]

@[simp]
theorem jordanMul_add_right (x y z : A) :
    jordanMul x (y + z) = jordanMul x y + jordanMul x z := by
  simp only [jordanMul, mul_add, add_mul, smul_add]
  module

@[simp]
theorem jordanMul_add_left (x y z : A) :
    jordanMul (x + y) z = jordanMul x z + jordanMul y z := by
  rw [jordanMul_comm, jordanMul_add_right]
  simp [jordanMul_comm]

@[simp]
theorem jordanMul_smul_right (r : ℝ) (x y : A) :
    jordanMul x (r • y) = r • jordanMul x y := by
  simp only [jordanMul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    smul_add, smul_smul]
  module

@[simp]
theorem jordanMul_smul_left (r : ℝ) (x y : A) :
    jordanMul (r • x) y = r • jordanMul x y := by
  rw [jordanMul_comm, jordanMul_smul_right]
  simp [jordanMul_comm]

/-- Left Jordan multiplication by `f`, as a native real-linear endomorphism. -/
def jordanLeft (f : A) : Module.End ℝ A where
  toFun x := jordanMul f x
  map_add' x y := jordanMul_add_right f x y
  map_smul' r x := jordanMul_smul_right r f x

@[simp]
theorem jordanLeft_apply (f x : A) :
    jordanLeft f x = jordanMul f x :=
  rfl

/-- Jordan Peirce eigenvalue `1`. -/
def IsJordanPeirceOne (f x : A) : Prop :=
  jordanMul f x = x

/-- Jordan Peirce eigenvalue `1/2`. -/
def IsJordanPeirceHalf (f x : A) : Prop :=
  jordanMul f x = (1 / 2 : ℝ) • x

/-- Jordan Peirce eigenvalue `0`. -/
def IsJordanPeirceZero (f x : A) : Prop :=
  jordanMul f x = 0

/-! ## Generic associative-to-Jordan transfer lemmas -/

/-- If `f` acts as the identity on both sides of `x`, then `x` is in the
Jordan Peirce eigenvalue-`1` sector. -/
theorem jordan_one_of_assoc
    {f x : A}
    (hleft : f * x = x)
    (hright : x * f = x) :
    IsJordanPeirceOne f x := by
  simp only [IsJordanPeirceOne, jordanMul, hleft, hright]
  module

/-- If `f` acts as the identity on the left and annihilates on the right,
then `x` is in the Jordan Peirce eigenvalue-`1/2` sector. -/
theorem jordan_half_of_assoc_left
    {f x : A}
    (hleft : f * x = x)
    (hright : x * f = 0) :
    IsJordanPeirceHalf f x := by
  simp [IsJordanPeirceHalf, jordanMul, hleft, hright]

/-- If `f` annihilates on the left and acts as the identity on the right,
then `x` is in the Jordan Peirce eigenvalue-`1/2` sector. -/
theorem jordan_half_of_assoc_right
    {f x : A}
    (hleft : f * x = 0)
    (hright : x * f = x) :
    IsJordanPeirceHalf f x := by
  simp [IsJordanPeirceHalf, jordanMul, hleft, hright]

/-- If `f` annihilates `x` on both sides, then `x` is in the Jordan Peirce
eigenvalue-`0` sector. -/
theorem jordan_zero_of_assoc
    {f x : A}
    (hleft : f * x = 0)
    (hright : x * f = 0) :
    IsJordanPeirceZero f x := by
  simp [IsJordanPeirceZero, jordanMul, hleft, hright]

/-! ## Associative block readouts against the idempotent -/

/-- `f` acts as the identity on the left of `A₁₀`. -/
theorem peirce10_absorb_left
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce10 f) :
    f * x = x := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, hf]

/-- `f` annihilates `A₁₀` on the right. -/
theorem peirce10_mul_idempotent_eq_zero
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce10 f) :
    x * f = 0 := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, complement_mul_idempotent f hf]

/-- `f` annihilates `A₀₁` on the left. -/
theorem idempotent_mul_peirce01_eq_zero
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce01 f) :
    f * x = 0 := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, idempotent_mul_complement f hf]

/-- `f` acts as the identity on the right of `A₀₁`. -/
theorem peirce01_absorb_right
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce01 f) :
    x * f = x := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, hf]

/-- `f` annihilates `A₀₀` on the left. -/
theorem idempotent_mul_peirce00_eq_zero
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce00 f) :
    f * x = 0 := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, idempotent_mul_complement f hf]

/-- `f` annihilates `A₀₀` on the right. -/
theorem peirce00_mul_idempotent_eq_zero
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce00 f) :
    x * f = 0 := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, complement_mul_idempotent f hf]

/-! ## Associative Peirce sectors as Jordan eigenspaces -/

/-- `A₁₁ ⊆ J₁(f)`. -/
theorem peirce11_is_jordan_one
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce11 f) :
    IsJordanPeirceOne f x := by
  exact jordan_one_of_assoc
    (peirce11_absorb_left f hf hx)
    (peirce11_absorb_right f hf hx)

/-- `A₁₀ ⊆ J_{1/2}(f)`. -/
theorem peirce10_is_jordan_half
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce10 f) :
    IsJordanPeirceHalf f x := by
  exact jordan_half_of_assoc_left
    (peirce10_absorb_left f hf hx)
    (peirce10_mul_idempotent_eq_zero f hf hx)

/-- `A₀₁ ⊆ J_{1/2}(f)`. -/
theorem peirce01_is_jordan_half
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce01 f) :
    IsJordanPeirceHalf f x := by
  exact jordan_half_of_assoc_right
    (idempotent_mul_peirce01_eq_zero f hf hx)
    (peirce01_absorb_right f hf hx)

/-- `A₀₀ ⊆ J₀(f)`. -/
theorem peirce00_is_jordan_zero
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce00 f) :
    IsJordanPeirceZero f x := by
  exact jordan_zero_of_assoc
    (idempotent_mul_peirce00_eq_zero f hf hx)
    (peirce00_mul_idempotent_eq_zero f hf hx)

/-! ## Canonical three-piece Jordan decomposition -/

/-- Canonical eigenvalue-`1` component. -/
def jordanOneComponent (f x : A) : A :=
  component11 f x

/-- Canonical eigenvalue-`1/2` component. -/
def jordanHalfComponent (f x : A) : A :=
  component10 f x + component01 f x

/-- Canonical eigenvalue-`0` component. -/
def jordanZeroComponent (f x : A) : A :=
  component00 f x

@[simp]
theorem jordanOneComponent_is_jordan_one
    (f : A) (hf : f * f = f) (x : A) :
    IsJordanPeirceOne f (jordanOneComponent f x) := by
  apply peirce11_is_jordan_one f hf
  exact component11_mem f x

@[simp]
theorem jordanHalfComponent_is_jordan_half
    (f : A) (hf : f * f = f) (x : A) :
    IsJordanPeirceHalf f (jordanHalfComponent f x) := by
  have h10 := peirce10_is_jordan_half f hf (component10_mem f x)
  have h01 := peirce01_is_jordan_half f hf (component01_mem f x)
  rw [IsJordanPeirceHalf] at h10 h01 ⊢
  simp only [jordanHalfComponent, jordanMul_add_right, h10, h01, smul_add]

@[simp]
theorem jordanZeroComponent_is_jordan_zero
    (f : A) (hf : f * f = f) (x : A) :
    IsJordanPeirceZero f (jordanZeroComponent f x) := by
  apply peirce00_is_jordan_zero f hf
  exact component00_mem f x

/-- Every element is the sum of its canonical Jordan Peirce `1`, `1/2`, and
`0` components. -/
theorem jordan_peirce_decomposition
    (f x : A) :
    x =
      jordanOneComponent f x +
      jordanHalfComponent f x +
      jordanZeroComponent f x := by
  rw [peirce_decomposition f x]
  simp only [jordanOneComponent, jordanHalfComponent, jordanZeroComponent]
  abel

/-- The canonical `1/2` component is explicitly the sum of the two off-diagonal
associative blocks. -/
theorem jordanHalfComponent_eq
    (f x : A) :
    jordanHalfComponent f x =
      f * x * complementIdempotent f +
      complementIdempotent f * x * f :=
  rfl

end SpecialJordan

end InfoGeometry.Core.JordanPeirceDecomposition
