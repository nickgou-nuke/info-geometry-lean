import proofs.SplitOctonionBraidSU3

/-!
# Zorn Matrix Layer for OP³ = OP and Null Paravectors

We use the Zorn vector-matrix model

`[[a, u], [v, b]]`

with `u v : Fin 3 → ℂ`.  This is the standard split-octonion style container:
diagonal idempotents model the cubic/trifactor projector `OP³ = OP`, while
pure off-diagonal paravectors model null square-zero directions.

Only the finite algebraic core is asserted here:

* `E₊² = E₊`, hence `E₊³ = E₊`;
* `E₋² = E₋`, hence `E₋³ = E₋`;
* upper and lower pure paravectors square to zero;
* all these projector/null lanes have Zorn determinant zero.
-/

noncomputable section

namespace ZornOPParavector

attribute [local simp]
  SplitOctonionBraidSU3.zornMul
  SplitOctonionBraidSU3.zornNorm
  SplitOctonionBraidSU3.dot3
  SplitOctonionBraidSU3.cross3

/-- Compatibility name for the repository's canonical complex Zorn carrier. -/
abbrev Zorn := SplitOctonionBraidSU3.Zorn

/-- Compatibility name for the canonical three-coordinate dot product. -/
def dot3 (u v : Fin 3 → ℂ) : ℂ :=
  SplitOctonionBraidSU3.dot3 u v

/-- Compatibility name for the canonical three-coordinate cross product. -/
def cross3 (u v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  SplitOctonionBraidSU3.cross3 u v

/-- Compatibility name for canonical Zorn multiplication. -/
def zornMul (X Y : Zorn) : Zorn :=
  SplitOctonionBraidSU3.zornMul X Y

/-- Keep legacy proofs reducible through their historical multiplication name. -/
local instance : Mul Zorn := ⟨zornMul⟩

/-!
The canonical `Mul` instance unfolds to `SplitOctonionBraidSU3.zornMul` in
downstream legacy modules.  These projection lemmas keep their coordinate
proofs stable without reintroducing a second carrier or product.
-/
@[simp] theorem canonical_zornMul_a (X Y : Zorn) :
    (SplitOctonionBraidSU3.zornMul X Y).a =
      X.a * Y.a + SplitOctonionBraidSU3.dot3 X.u Y.v := rfl

@[simp] theorem canonical_zornMul_u (X Y : Zorn) (i : Fin 3) :
    (SplitOctonionBraidSU3.zornMul X Y).u i =
      X.a * Y.u i + Y.b * X.u i -
        SplitOctonionBraidSU3.cross3 X.v Y.v i := rfl

@[simp] theorem canonical_zornMul_v (X Y : Zorn) (i : Fin 3) :
    (SplitOctonionBraidSU3.zornMul X Y).v i =
      Y.a * X.v i + X.b * Y.v i +
        SplitOctonionBraidSU3.cross3 X.u Y.u i := rfl

@[simp] theorem canonical_zornMul_b (X Y : Zorn) :
    (SplitOctonionBraidSU3.zornMul X Y).b =
      SplitOctonionBraidSU3.dot3 X.v Y.u + X.b * Y.b := rfl

@[simp] theorem canonical_dot3_zero_left (u : Fin 3 → ℂ) :
    SplitOctonionBraidSU3.dot3 0 u = 0 := by
  simp [SplitOctonionBraidSU3.dot3]

@[simp] theorem canonical_dot3_zero_right (u : Fin 3 → ℂ) :
    SplitOctonionBraidSU3.dot3 u 0 = 0 := by
  simp [SplitOctonionBraidSU3.dot3]

@[simp] theorem canonical_cross3_zero_left (u : Fin 3 → ℂ) :
    SplitOctonionBraidSU3.cross3 0 u = 0 := by
  funext i
  fin_cases i <;> simp [SplitOctonionBraidSU3.cross3]

@[simp] theorem canonical_cross3_zero_right (u : Fin 3 → ℂ) :
    SplitOctonionBraidSU3.cross3 u 0 = 0 := by
  funext i
  fin_cases i <;> simp [SplitOctonionBraidSU3.cross3]

/-- Zorn determinant/norm form. -/
def zornDet (X : Zorn) : ℂ :=
  SplitOctonionBraidSU3.zornNorm X

/-- Cubic/trifactor condition. -/
def CubicProjector (X : Zorn) : Prop :=
  X * X * X = X

/-- Null/parabolic square-zero condition. -/
def SquareZero (X : Zorn) : Prop :=
  X * X = 0

/-- Upper diagonal primitive projector. -/
def Eplus : Zorn :=
  ⟨1, 0, 0, 0⟩

/-- Lower diagonal primitive projector. -/
def Eminus : Zorn :=
  ⟨0, 0, 0, 1⟩

/-- Pure upper paravector lane. -/
def Nup (u : Fin 3 → ℂ) : Zorn :=
  ⟨0, u, 0, 0⟩

/-- Pure lower paravector lane. -/
def Ndown (v : Fin 3 → ℂ) : Zorn :=
  ⟨0, 0, v, 0⟩

namespace Zorn

theorem ext' {X Y : Zorn}
    (ha : X.a = Y.a) (hu : X.u = Y.u) (hv : X.v = Y.v) (hb : X.b = Y.b) :
    X = Y := by
  exact SplitOctonionBraidSU3.zorn_ext ha hu hv hb

end Zorn

theorem Eplus_sq :
    Eplus * Eplus = Eplus := by
  change zornMul Eplus Eplus = Eplus
  apply Zorn.ext'
  · simp [Eplus, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Eplus, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [Eplus, zornMul, cross3]
  · simp [Eplus, zornMul, dot3]

theorem Eminus_sq :
    Eminus * Eminus = Eminus := by
  change zornMul Eminus Eminus = Eminus
  apply Zorn.ext'
  · simp [Eminus, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Eminus, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [Eminus, zornMul, cross3]
  · simp [Eminus, zornMul, dot3]

theorem Eplus_cubic :
    CubicProjector Eplus := by
  unfold CubicProjector
  rw [Eplus_sq, Eplus_sq]

theorem Eminus_cubic :
    CubicProjector Eminus := by
  unfold CubicProjector
  rw [Eminus_sq, Eminus_sq]

theorem Eplus_det_zero :
    zornDet Eplus = 0 := by
  simp [zornDet, Eplus, dot3]

theorem Eminus_det_zero :
    zornDet Eminus = 0 := by
  simp [zornDet, Eminus, dot3]

theorem Nup_sq (u : Fin 3 → ℂ) :
    SquareZero (Nup u) := by
  unfold SquareZero
  change zornMul (Nup u) (Nup u) = ⟨0, 0, 0, 0⟩
  apply Zorn.ext'
  · simp [Nup, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Nup, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [Nup, zornMul, cross3] <;> ring_nf
  · simp [Nup, zornMul, dot3]

theorem Ndown_sq (v : Fin 3 → ℂ) :
    SquareZero (Ndown v) := by
  unfold SquareZero
  change zornMul (Ndown v) (Ndown v) = ⟨0, 0, 0, 0⟩
  apply Zorn.ext'
  · simp [Ndown, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Ndown, zornMul, cross3] <;> ring_nf
  · funext i
    fin_cases i <;> simp [Ndown, zornMul, cross3]
  · simp [Ndown, zornMul, dot3]

theorem Nup_det_zero (u : Fin 3 → ℂ) :
    zornDet (Nup u) = 0 := by
  simp [zornDet, Nup, dot3]

theorem Ndown_det_zero (v : Fin 3 → ℂ) :
    zornDet (Ndown v) = 0 := by
  simp [zornDet, Ndown, dot3]

/-- Upper-lower paravector product puts the dot product in the upper scalar slot. -/
theorem Nup_mul_Ndown (u v : Fin 3 → ℂ) :
    Nup u * Ndown v = ⟨dot3 u v, 0, 0, 0⟩ := by
  change zornMul (Nup u) (Ndown v) = ⟨dot3 u v, 0, 0, 0⟩
  apply Zorn.ext'
  · simp [Nup, Ndown, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Nup, Ndown, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [Nup, Ndown, zornMul, cross3]
  · simp [Nup, Ndown, zornMul, dot3]

/-- Lower-upper paravector product puts the dot product in the lower scalar slot. -/
theorem Ndown_mul_Nup (u v : Fin 3 → ℂ) :
    Ndown v * Nup u = ⟨0, 0, 0, dot3 v u⟩ := by
  change zornMul (Ndown v) (Nup u) = ⟨0, 0, 0, dot3 v u⟩
  apply Zorn.ext'
  · simp [Nup, Ndown, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Nup, Ndown, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [Nup, Ndown, zornMul, cross3]
  · simp [Nup, Ndown, zornMul, dot3]

/--
Consolidated Zorn layer: cubic OP projectors and square-zero null paravectors
live in the same vector-matrix package, and both are determinant-null.
-/
theorem zorn_op_paravector_synthesis :
    Eplus * Eplus = Eplus ∧
    Eminus * Eminus = Eminus ∧
    CubicProjector Eplus ∧
    CubicProjector Eminus ∧
    zornDet Eplus = 0 ∧
    zornDet Eminus = 0 ∧
    (∀ u : Fin 3 → ℂ, SquareZero (Nup u)) ∧
    (∀ v : Fin 3 → ℂ, SquareZero (Ndown v)) ∧
    (∀ u : Fin 3 → ℂ, zornDet (Nup u) = 0) ∧
    (∀ v : Fin 3 → ℂ, zornDet (Ndown v) = 0) ∧
    (∀ u v : Fin 3 → ℂ, Nup u * Ndown v = ⟨dot3 u v, 0, 0, 0⟩) ∧
    (∀ u v : Fin 3 → ℂ, Ndown v * Nup u = ⟨0, 0, 0, dot3 v u⟩) := by
  exact ⟨Eplus_sq,
    Eminus_sq,
    Eplus_cubic,
    Eminus_cubic,
    Eplus_det_zero,
    Eminus_det_zero,
    Nup_sq,
    Ndown_sq,
    Nup_det_zero,
    Ndown_det_zero,
    Nup_mul_Ndown,
    Ndown_mul_Nup⟩

end ZornOPParavector

end noncomputable section
