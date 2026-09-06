/-
InfoGeometry/Exceptional/Freudenthal.lean

Freudenthal phase-space and TKK closure signatures.

This file is intentionally witness-gated. It does not construct `E₇(7)`.
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

This file proves alternating and skew-symmetry. A later file can bundle this as
a bilinear form after adding the vector-space instance on `FreudenthalCharge J`.
-/
def symplecticForm
    (D : CubicJordanDatum J)
    (Q₁ Q₂ : FreudenthalCharge J) : ℝ :=
  Q₁.alpha * Q₂.beta - Q₁.beta * Q₂.alpha
    + D.traceBilin Q₁.x Q₂.y
    - D.traceBilin Q₁.y Q₂.x

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

/-! ### 2a. The symplectic Heisenberg sector -/

@[ext]
structure HeisenbergElement (J : Type*) [AddCommGroup J] [Module ℝ J] where
  charge : FreudenthalCharge J
  center : ℝ

namespace HeisenbergElement

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

def zeroCharge : FreudenthalCharge J where
  alpha := 0
  beta := 0
  x := 0
  y := 0

theorem zeroCharge_eq_iff (Q : FreudenthalCharge J) :
    Q = (zeroCharge : FreudenthalCharge J) ↔
      Q.alpha = 0 ∧ Q.beta = 0 ∧ Q.x = 0 ∧ Q.y = 0 := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨ha, hb, hx, hy⟩
    cases Q with
    | mk alpha beta x y =>
      simp_all [zeroCharge]

def zero : HeisenbergElement J where
  charge := zeroCharge
  center := 0

def bracket
    (D : CubicJordanDatum J)
    (X Y : HeisenbergElement J) : HeisenbergElement J where
  charge := zeroCharge
  center := FreudenthalCharge.symplecticForm D X.charge Y.charge

@[simp] theorem bracket_charge
    (D : CubicJordanDatum J) (X Y : HeisenbergElement J) :
    (bracket D X Y).charge = zeroCharge := rfl

@[simp] theorem bracket_center
    (D : CubicJordanDatum J) (X Y : HeisenbergElement J) :
    (bracket D X Y).center = FreudenthalCharge.symplecticForm D X.charge Y.charge := rfl

theorem bracket_skew
    (D : CubicJordanDatum J) (X Y : HeisenbergElement J) :
    bracket D Y X =
      { charge := (bracket D X Y).charge
        center := -(bracket D X Y).center } := by
  apply HeisenbergElement.ext
  · rfl
  · exact FreudenthalCharge.symplectic_form_skew D X.charge Y.charge

@[simp] theorem bracket_self
    (D : CubicJordanDatum J) (X : HeisenbergElement J) :
    bracket D X X = zero := by
  apply HeisenbergElement.ext
  · rfl
  · simpa only [bracket, zero] using
      (FreudenthalCharge.symplectic_form_alternating D X.charge)

@[simp] theorem bracket_bracket_left
    (D : CubicJordanDatum J) (X Y Z : HeisenbergElement J) :
    bracket D (bracket D X Y) Z = zero := by
  apply HeisenbergElement.ext
  · rfl
  · simp [bracket, zero, zeroCharge, FreudenthalCharge.symplecticForm]

theorem bracket_bracket_right
    (D : CubicJordanDatum J) (X Y Z : HeisenbergElement J) :
    bracket D X (bracket D Y Z) = zero := by
  apply HeisenbergElement.ext
  · rfl
  · simp [bracket, zero, zeroCharge, FreudenthalCharge.symplecticForm]

theorem bracket_jacobi_terms_vanish
    (D : CubicJordanDatum J) (X Y Z : HeisenbergElement J) :
    bracket D X (bracket D Y Z) = zero ∧
      bracket D Y (bracket D Z X) = zero ∧
      bracket D Z (bracket D X Y) = zero := by
  exact ⟨bracket_bracket_right D X Y Z,
    bracket_bracket_right D Y Z X,
    bracket_bracket_right D Z X Y⟩

end HeisenbergElement

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
