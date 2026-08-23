/-
InfoGeometry/Exceptional/Freudenthal.lean

Freudenthal phase-space and TKK closure signatures.

This file is intentionally property-gated. It does not construct `E₇(7)`.
It defines the algebraic operations needed to form the Freudenthal charge
space over an abstract cubic Jordan datum, and proves only consequences of
those stored operations.
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

/-! ### 1. Cubic Jordan algebra signature -/

/--
Signature for a cubic Jordan datum.

This is not a full bundled construction of the split Albert algebra. It stores
the operations required by the Freudenthal quartic invariant. Concrete models,
such as the diagonal STU model or a split Albert model, must provide this datum.
-/
structure CubicJordanDatum (J : Type*) [AddCommGroup J] [Module ℝ J] where
  /-- Symmetric bilinear trace pairing `⟨X,Y⟩`. -/
  traceBilin : J →ₗ[ℝ] J →ₗ[ℝ] ℝ

  /-- Symmetry of the trace pairing. -/
  trace_comm : ∀ x y : J, traceBilin x y = traceBilin y x

  /-- Cubic norm `N(X)`. -/
  normCubic : J → ℝ

  /-- Quadratic adjoint/cofactor map `X ↦ X#`. -/
  adjointQuad : J → J

  /-- Symmetric trilinear form associated to the cubic datum. -/
  normTrilin : J →ₗ[ℝ] J →ₗ[ℝ] J →ₗ[ℝ] ℝ

  /-- Symmetry of the first two arguments. -/
  normTrilin_swap₁₂ :
    ∀ x y z : J, normTrilin x y z = normTrilin y x z

  /-- Symmetry of the last two arguments. -/
  normTrilin_swap₂₃ :
    ∀ x y z : J, normTrilin x y z = normTrilin x z y

  /--
  Diagonal normalization.

  For the usual polarization convention, `N(X,X,X) = N(X)`.
  -/
  normTrilin_self : ∀ x : J, normTrilin x x x = normCubic x

namespace CubicJordanDatum

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- Derived symmetry between the first and third trilinear arguments. -/
theorem normTrilin_swap₁₃ (x y z : J) :
    D.normTrilin x y z = D.normTrilin z y x := by
  calc
    D.normTrilin x y z = D.normTrilin y x z :=
      D.normTrilin_swap₁₂ x y z
    _ = D.normTrilin y z x :=
      D.normTrilin_swap₂₃ y x z
    _ = D.normTrilin z y x :=
      D.normTrilin_swap₁₂ y z x

end CubicJordanDatum

/-! ### 2. The Freudenthal phase space `𝔉(J)` -/

/--
The Freudenthal charge space `𝔉(J) ≅ ℝ ⊕ ℝ ⊕ J ⊕ J`.

An element is written as `Q = (α, β, X, Y)`.
-/
@[ext]
structure FreudenthalCharge (J : Type*) [AddCommGroup J] [Module ℝ J] where
  alpha : ℝ
  beta : ℝ
  x : J
  y : J

namespace FreudenthalCharge

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

instance : AddCommGroup (FreudenthalCharge J) where
  add P Q := ⟨P.alpha + Q.alpha, P.beta + Q.beta, P.x + Q.x, P.y + Q.y⟩
  add_assoc P Q S := by ext <;> simp [add_assoc]
  zero := ⟨0, 0, 0, 0⟩
  zero_add P := by ext <;> simp
  add_zero P := by ext <;> simp
  neg P := ⟨-P.alpha, -P.beta, -P.x, -P.y⟩
  neg_add_cancel P := by ext <;> simp
  add_comm P Q := by ext <;> simp [add_comm]
  nsmul := fun n P => Nat.rec 0 (fun _ acc => acc + P) n
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul := fun z P =>
    match z with
    | Int.ofNat n => Nat.rec 0 (fun _ acc => acc + P) n
    | Int.negSucc n => -(Nat.rec 0 (fun _ acc => acc + P) (n + 1))
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

instance : Module ℝ (FreudenthalCharge J) where
  smul r P := ⟨r * P.alpha, r * P.beta, r • P.x, r • P.y⟩
  one_smul P := by ext <;> simp
  mul_smul r s P := by ext <;> simp [mul_assoc]
  smul_add r P Q := by ext <;> simp [mul_add]
  smul_zero r := by ext <;> simp
  add_smul r s P := by ext <;> simp [add_mul]
  zero_smul P := by ext <;> simp

@[simp] theorem zero_alpha : (0 : FreudenthalCharge J).alpha = 0 := rfl
@[simp] theorem zero_beta : (0 : FreudenthalCharge J).beta = 0 := rfl
@[simp] theorem zero_x : (0 : FreudenthalCharge J).x = 0 := rfl
@[simp] theorem zero_y : (0 : FreudenthalCharge J).y = 0 := rfl

@[simp] theorem add_alpha (P Q : FreudenthalCharge J) : (P + Q).alpha = P.alpha + Q.alpha := rfl
@[simp] theorem add_beta (P Q : FreudenthalCharge J) : (P + Q).beta = P.beta + Q.beta := rfl
@[simp] theorem add_x (P Q : FreudenthalCharge J) : (P + Q).x = P.x + Q.x := rfl
@[simp] theorem add_y (P Q : FreudenthalCharge J) : (P + Q).y = P.y + Q.y := rfl

@[simp] theorem smul_alpha (r : ℝ) (P : FreudenthalCharge J) : (r • P).alpha = r * P.alpha := rfl
@[simp] theorem smul_beta (r : ℝ) (P : FreudenthalCharge J) : (r • P).beta = r * P.beta := rfl
@[simp] theorem smul_x (r : ℝ) (P : FreudenthalCharge J) : (r • P).x = r • P.x := rfl
@[simp] theorem smul_y (r : ℝ) (P : FreudenthalCharge J) : (r • P).y = r • P.y := rfl

/--
The Freudenthal quartic polynomial

`I₄(Q) = (αβ - ⟨X,Y⟩)² - 4(αN(X) + βN(Y) - ⟨X#,Y#⟩)`.
-/
def quarticInvariant
    (D : CubicJordanDatum J) (Q : FreudenthalCharge J) : ℝ :=
  let term1 := Q.alpha * Q.beta - D.traceBilin Q.x Q.y
  let term2 :=
    Q.alpha * D.normCubic Q.x
      + Q.beta * D.normCubic Q.y
      - D.traceBilin (D.adjointQuad Q.x) (D.adjointQuad Q.y)
  term1 ^ 2 - 4 * term2

/--
The scalar formula for the canonical Freudenthal symplectic pairing

`ω(Q₁,Q₂) = α₁β₂ - β₁α₂ + ⟨X₁,Y₂⟩ - ⟨Y₁,X₂⟩`.
-/
def symplecticForm
    (D : CubicJordanDatum J)
    (Q₁ Q₂ : FreudenthalCharge J) : ℝ :=
  Q₁.alpha * Q₂.beta - Q₁.beta * Q₂.alpha
    + D.traceBilin Q₁.x Q₂.y
    - D.traceBilin Q₁.y Q₂.x

/-- The Freudenthal symplectic pairing bundled as a bilinear map. -/
def symplecticFormLinear
    (D : CubicJordanDatum J) :
    FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J →ₗ[ℝ] ℝ where
  toFun Q₁ :=
    { toFun := fun Q₂ => symplecticForm D Q₁ Q₂
      map_add' := by
        intro Q₂ Q₃
        simp [symplecticForm, mul_add, D.traceBilin.map_add]
        ring
      map_smul' := by
        intro r Q₂
        simp [symplecticForm, mul_assoc, D.traceBilin.map_smul]
        ring }
  map_add' := by
    intro Q₁ Q₂
    ext Q₃
    simp [symplecticForm, add_mul, D.traceBilin.map_add]
    ring
  map_smul' := by
    intro r Q₁
    ext Q₂
    simp [symplecticForm, mul_assoc, D.traceBilin.map_smul]
    ring

@[simp] theorem symplecticFormLinear_apply
    (D : CubicJordanDatum J) (Q₁ Q₂ : FreudenthalCharge J) :
    symplecticFormLinear D Q₁ Q₂ = symplecticForm D Q₁ Q₂ := rfl

/--
The Freudenthal symplectic form is alternating.

This follows only from symmetry of the stored trace pairing and ring arithmetic.
-/
@[simp]
theorem symplectic_form_alternating
    (D : CubicJordanDatum J) (Q : FreudenthalCharge J) :
    symplecticForm D Q Q = 0 := by
  dsimp [symplecticForm]
  rw [D.trace_comm Q.x Q.y]
  ring

/-- The Freudenthal symplectic form is skew-symmetric. -/
theorem symplectic_form_skew
    (D : CubicJordanDatum J) (Q₁ Q₂ : FreudenthalCharge J) :
    symplecticForm D Q₂ Q₁ = - symplecticForm D Q₁ Q₂ := by
  dsimp [symplecticForm]
  rw [D.trace_comm Q₂.x Q₁.y]
  rw [D.trace_comm Q₂.y Q₁.x]
  ring

end FreudenthalCharge

/-! ### 3. Tits-Kantor-Koecher closure signature -/

/--
Tits-Kantor-Koecher 3-grading signature.

This stores bilinear operations for a 3-graded closure interface

`𝔤 = 𝔤₋₁ ⊕ 𝔤₀ ⊕ 𝔤₊₁`

with `𝔤₋₁ ≃ J` and `𝔤₊₁ ≃ J`.

This is only a signature. It does not assert skew-symmetry, Jacobi, simplicity,
representation laws, or an identification with `𝔢₇(7)`.
-/
structure TKKClosureDatum
    (J : Type*) [AddCommGroup J] [Module ℝ J]
    (G_zero : Type*) [AddCommGroup G_zero] [Module ℝ G_zero] where

  /-- Bilinear operation on the grade-zero sector. -/
  op_0_0 : G_zero →ₗ[ℝ] G_zero →ₗ[ℝ] G_zero

  /-- Bilinear operation from grade zero and grade `-1` to grade `-1`. -/
  op_0_minus1 : G_zero →ₗ[ℝ] J →ₗ[ℝ] J

  /-- Bilinear operation from grade zero and grade `+1` to grade `+1`. -/
  op_0_plus1 : G_zero →ₗ[ℝ] J →ₗ[ℝ] J

  /-- Bilinear operation from grade `-1` and grade `+1` into grade zero. -/
  op_minus1_plus1 : J →ₗ[ℝ] J →ₗ[ℝ] G_zero

end InfoGeometry.Exceptional.Freudenthal
