import Mathlib.Tactic

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

/-- Three-vector dot product. -/
def dot3 (u v : Fin 3 → ℂ) : ℂ :=
  ∑ i : Fin 3, u i * v i

/-- Three-vector cross product. -/
def cross3 (u v : Fin 3 → ℂ) : Fin 3 → ℂ
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

/-- Zorn vector matrix `[[a,u],[v,b]]`. -/
abbrev Zorn := ℂ × (Fin 3 → ℂ) × (Fin 3 → ℂ) × ℂ

namespace Zorn

def a (X : Zorn) : ℂ := X.1
def u (X : Zorn) : Fin 3 → ℂ := X.2.1
def v (X : Zorn) : Fin 3 → ℂ := X.2.2.1
def b (X : Zorn) : ℂ := X.2.2.2

end Zorn

instance : Zero Zorn :=
  ⟨(0, 0, 0, 0)⟩

instance : One Zorn :=
  ⟨(1, 0, 0, 1)⟩

/-- Zorn product for split-octonion vector matrices. -/
def zornMul (X Y : Zorn) : Zorn :=
  (X.a * Y.a + dot3 X.u Y.v,
    fun i => X.a * Y.u i + Y.b * X.u i - cross3 X.v Y.v i,
    fun i => Y.a * X.v i + X.b * Y.v i + cross3 X.u Y.u i,
    dot3 X.v Y.u + X.b * Y.b)

instance : Mul Zorn :=
  ⟨zornMul⟩

/-- Zorn determinant/norm form. -/
def zornDet (X : Zorn) : ℂ :=
  X.a * X.b - dot3 X.u X.v

/-- Cubic/trifactor condition. -/
def CubicProjector (X : Zorn) : Prop :=
  X * X * X = X

/-- Null/parabolic square-zero condition. -/
def SquareZero (X : Zorn) : Prop :=
  X * X = 0

/-- Upper diagonal primitive projector. -/
def Eplus : Zorn :=
  (1, 0, 0, 0)

/-- Lower diagonal primitive projector. -/
def Eminus : Zorn :=
  (0, 0, 0, 1)

/-- Pure upper paravector lane. -/
def Nup (u : Fin 3 → ℂ) : Zorn :=
  (0, u, 0, 0)

/-- Pure lower paravector lane. -/
def Ndown (v : Fin 3 → ℂ) : Zorn :=
  (0, 0, v, 0)

@[ext]
theorem Zorn.ext' {X Y : Zorn}
    (ha : X.a = Y.a) (hu : X.u = Y.u) (hv : X.v = Y.v) (hb : X.b = Y.b) :
    X = Y := by
  rcases X with ⟨aX, uX, vX, bX⟩
  rcases Y with ⟨aY, uY, vY, bY⟩
  simp only [Zorn.a, Zorn.u, Zorn.v, Zorn.b] at ha hu hv hb
  simp_all

theorem Eplus_sq :
    Eplus * Eplus = Eplus := by
  change zornMul Eplus Eplus = Eplus
  apply Zorn.ext'
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Eplus, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Eplus, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Eplus, zornMul, cross3]
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Eplus, zornMul, dot3]

theorem Eminus_sq :
    Eminus * Eminus = Eminus := by
  change zornMul Eminus Eminus = Eminus
  apply Zorn.ext'
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Eminus, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Eminus, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Eminus, zornMul, cross3]
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Eminus, zornMul, dot3]

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
  simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, zornDet, Eplus, dot3]

theorem Eminus_det_zero :
    zornDet Eminus = 0 := by
  simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, zornDet, Eminus, dot3]

theorem Nup_sq (u : Fin 3 → ℂ) :
    SquareZero (Nup u) := by
  unfold SquareZero
  change zornMul (Nup u) (Nup u) = ⟨0, 0, 0, 0⟩
  apply Zorn.ext'
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, zornMul, cross3] <;> ring_nf
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, zornMul, dot3]

theorem Ndown_sq (v : Fin 3 → ℂ) :
    SquareZero (Ndown v) := by
  unfold SquareZero
  change zornMul (Ndown v) (Ndown v) = ⟨0, 0, 0, 0⟩
  apply Zorn.ext'
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Ndown, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Ndown, zornMul, cross3] <;> ring_nf
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Ndown, zornMul, cross3]
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Ndown, zornMul, dot3]

theorem Nup_det_zero (u : Fin 3 → ℂ) :
    zornDet (Nup u) = 0 := by
  simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, zornDet, Nup, dot3]

theorem Ndown_det_zero (v : Fin 3 → ℂ) :
    zornDet (Ndown v) = 0 := by
  simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, zornDet, Ndown, dot3]

/-- Upper-lower paravector product puts the dot product in the upper scalar slot. -/
theorem Nup_mul_Ndown (u v : Fin 3 → ℂ) :
    Nup u * Ndown v = ⟨dot3 u v, 0, 0, 0⟩ := by
  change zornMul (Nup u) (Ndown v) = ⟨dot3 u v, 0, 0, 0⟩
  apply Zorn.ext'
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, Ndown, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, Ndown, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, Ndown, zornMul, cross3]
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, Ndown, zornMul, dot3]

/-- Lower-upper paravector product puts the dot product in the lower scalar slot. -/
theorem Ndown_mul_Nup (u v : Fin 3 → ℂ) :
    Ndown v * Nup u = ⟨0, 0, 0, dot3 v u⟩ := by
  change zornMul (Ndown v) (Nup u) = ⟨0, 0, 0, dot3 v u⟩
  apply Zorn.ext'
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, Ndown, zornMul, dot3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, Ndown, zornMul, cross3]
  · funext i
    fin_cases i <;> simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, Ndown, zornMul, cross3]
  · simp [Zorn.a, Zorn.u, Zorn.v, Zorn.b, Nup, Ndown, zornMul, dot3]

end ZornOPParavector

end noncomputable section
