import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Zorn Associator and Split-Octonion Witness

The determinant/null bridge gives the vector-matrix container.  This layer
records the key split-octonion feature: Zorn multiplication is generally
non-associative because the cross product enters the off-diagonal lanes.

We prove a concrete associator witness using basis vectors:

`A = [[0,e₁],[0,0]]`

`B = [[0,0],[e₁,0]]`

`C = [[0,e₂],[0,0]]`

Then `(AB)C - A(BC)` has upper vector component `e₂`, so associativity fails.
-/

noncomputable section

namespace ZornAssociatorSplitOctonion

/-- Three-vector dot product. -/
def dot3 (u v : Fin 3 → ℂ) : ℂ :=
  ∑ i : Fin 3, u i * v i

/-- Three-vector cross product. -/
def cross3 (u v : Fin 3 → ℂ) : Fin 3 → ℂ
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

/-- Zorn vector matrix. -/
structure Zorn where
  a : ℂ
  u : Fin 3 → ℂ
  v : Fin 3 → ℂ
  b : ℂ

instance : Zero Zorn :=
  ⟨⟨0, 0, 0, 0⟩⟩

instance : One Zorn :=
  ⟨⟨1, 0, 0, 1⟩⟩

/-- Componentwise negation. -/
def zornNeg (X : Zorn) : Zorn :=
  ⟨-X.a, -X.u, -X.v, -X.b⟩

/-- Componentwise addition. -/
def zornAdd (X Y : Zorn) : Zorn :=
  ⟨X.a + Y.a, X.u + Y.u, X.v + Y.v, X.b + Y.b⟩

/-- Componentwise subtraction. -/
def zornSub (X Y : Zorn) : Zorn :=
  zornAdd X (zornNeg Y)

instance : Neg Zorn :=
  ⟨zornNeg⟩

instance : Add Zorn :=
  ⟨zornAdd⟩

instance : Sub Zorn :=
  ⟨zornSub⟩

/-- Zorn product. -/
def zornMul (X Y : Zorn) : Zorn where
  a := X.a * Y.a + dot3 X.u Y.v
  u := fun i => X.a * Y.u i + Y.b * X.u i - cross3 X.v Y.v i
  v := fun i => Y.a * X.v i + X.b * Y.v i + cross3 X.u Y.u i
  b := dot3 X.v Y.u + X.b * Y.b

instance : Mul Zorn :=
  ⟨zornMul⟩

/-- Zorn determinant/norm form. -/
def zornDet (X : Zorn) : ℂ :=
  X.a * X.b - dot3 X.u X.v

@[ext]
theorem Zorn.ext' {X Y : Zorn}
    (ha : X.a = Y.a) (hu : X.u = Y.u) (hv : X.v = Y.v) (hb : X.b = Y.b) :
    X = Y := by
  cases X
  cases Y
  simp_all

/-- Standard basis of `ℂ^3`. -/
def basis3 (k : Fin 3) : Fin 3 → ℂ :=
  fun i => if i = k then 1 else 0

def e₁ : Fin 3 → ℂ := basis3 0
def e₂ : Fin 3 → ℂ := basis3 1
def e₃ : Fin 3 → ℂ := basis3 2

/-- Pure upper lane. -/
def U (u : Fin 3 → ℂ) : Zorn :=
  ⟨0, u, 0, 0⟩

/-- Pure lower lane. -/
def L (v : Fin 3 → ℂ) : Zorn :=
  ⟨0, 0, v, 0⟩

/-- Associator `(XY)Z - X(YZ)`. -/
def associator (X Y Z : Zorn) : Zorn :=
  zornSub ((X * Y) * Z) (X * (Y * Z))

theorem cross_e₁_e₂ :
    cross3 e₁ e₂ = e₃ := by
  funext i
  fin_cases i <;> simp [cross3, e₁, e₂, e₃, basis3]

theorem cross_e₂_e₃ :
    cross3 e₂ e₃ = e₁ := by
  funext i
  fin_cases i <;> simp [cross3, e₁, e₂, e₃, basis3]

theorem dot_e₁_e₃ :
    dot3 e₁ e₃ = 0 := by
  simp [dot3, e₁, e₃, basis3]

theorem dot_e₂_e₃ :
    dot3 e₂ e₃ = 0 := by
  simp [dot3, e₂, e₃, basis3]

theorem dot_e₃_e₃ :
    dot3 e₃ e₃ = 1 := by
  simp [dot3, e₃, basis3]

/-- Pure upper square is zero. -/
theorem U_sq (u : Fin 3 → ℂ) :
    U u * U u = 0 := by
  change zornMul (U u) (U u) = ⟨0, 0, 0, 0⟩
  apply Zorn.ext'
  · simp [U, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [U, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [U, zornMul, cross3] <;> ring
  · simp [U, zornMul, dot3]

/-- Pure lower square is zero. -/
theorem L_sq (v : Fin 3 → ℂ) :
    L v * L v = 0 := by
  change zornMul (L v) (L v) = ⟨0, 0, 0, 0⟩
  apply Zorn.ext'
  · simp [L, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [L, zornMul, cross3] <;> ring
  · funext i
    fin_cases i <;> simp [L, zornMul, cross3]
  · simp [L, zornMul, dot3]

/--
Concrete non-associativity witness.  The upper vector component is `e₂`.
-/
theorem associator_U₁_L₁_U₂ :
    associator (U e₁) (L e₁) (U e₂) = ⟨0, e₂, 0, 0⟩ := by
  unfold associator
  change
    zornSub
      (zornMul (zornMul (U e₁) (L e₁)) (U e₂))
      (zornMul (U e₁) (zornMul (L e₁) (U e₂))) =
        ⟨0, e₂, 0, 0⟩
  apply Zorn.ext'
  · norm_num [zornSub, zornAdd, zornNeg, zornMul, U, L, dot3, cross3, e₁, e₂, basis3]
  · funext i
    fin_cases i <;> simp [zornSub, zornAdd, zornNeg, zornMul, U, L, cross3, dot3, e₁, e₂, basis3]
  · funext i
    fin_cases i <;> simp [zornSub, zornAdd, zornNeg, zornMul, U, L, cross3, dot3, e₁, e₂, basis3]
  · norm_num [zornSub, zornAdd, zornNeg, zornMul, U, L, dot3, cross3, e₁, e₂, basis3]

theorem associator_U₁_L₁_U₂_nonzero :
    associator (U e₁) (L e₁) (U e₂) ≠ 0 := by
  intro h
  have hu := congrArg (fun X : Zorn => X.u 1) h
  rw [associator_U₁_L₁_U₂] at hu
  change (1 : ℂ) = 0 at hu
  exact one_ne_zero hu

/-- Diagonal split idempotent lanes. -/
def Eplus : Zorn := ⟨1, 0, 0, 0⟩
def Eminus : Zorn := ⟨0, 0, 0, 1⟩

theorem zornDet_Eplus :
    zornDet Eplus = 0 := by
  simp [zornDet, Eplus, dot3]

theorem zornDet_Eminus :
    zornDet Eminus = 0 := by
  simp [zornDet, Eminus, dot3]

/--
Consolidated split-octonion witness: square-zero paravector lanes coexist with
an explicit nonzero associator.
-/
theorem zorn_associator_split_octonion_synthesis :
    (∀ u : Fin 3 → ℂ, U u * U u = 0) ∧
    (∀ v : Fin 3 → ℂ, L v * L v = 0) ∧
    associator (U e₁) (L e₁) (U e₂) = ⟨0, e₂, 0, 0⟩ ∧
    associator (U e₁) (L e₁) (U e₂) ≠ 0 ∧
    zornDet Eplus = 0 ∧
    zornDet Eminus = 0 := by
  exact ⟨U_sq,
    L_sq,
    associator_U₁_L₁_U₂,
    associator_U₁_L₁_U₂_nonzero,
    zornDet_Eplus,
    zornDet_Eminus⟩

end ZornAssociatorSplitOctonion

end noncomputable section
