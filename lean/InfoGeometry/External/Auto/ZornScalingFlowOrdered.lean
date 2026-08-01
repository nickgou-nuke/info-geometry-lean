import Mathlib.Tactic

/-!
# Zorn scaling flow in tuple order `(a,b,u,v)`

This module matches the user's SymPy tuple convention:
`X=(a,b,u,v)` represents the Zorn matrix `[[a,u],[v,b]]`.
For `E=(p,p⁻¹,0,0)` and `E⁻¹=(p⁻¹,p,0,0)`, Zorn conjugation gives

`E * X * E⁻¹ = (a,b,p²u,p⁻²v)`.
-/

noncomputable section

namespace ZornScalingFlowOrdered

abbrev Vec3 := Fin 3 → ℂ

/-- Dot product on `ℂ³`. -/
def dot3 (u v : Vec3) : ℂ := ∑ i : Fin 3, u i * v i

/-- Cross product on `ℂ³`. -/
def cross3 (u v : Vec3) : Vec3
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

/-- Zorn coordinates in order `(a,b,u,v)`. -/
abbrev Zorn := ℂ × ℂ × Vec3 × Vec3

namespace Zorn

def a (X : Zorn) : ℂ := X.1
def b (X : Zorn) : ℂ := X.2.1
def u (X : Zorn) : Vec3 := X.2.2.1
def v (X : Zorn) : Vec3 := X.2.2.2

end Zorn

/-- Extensionality for Zorn coordinates. -/
theorem zorn_ext {X Y : Zorn}
    (ha : X.a = Y.a) (hb : X.b = Y.b) (hu : X.u = Y.u) (hv : X.v = Y.v) : X = Y := by
  rcases X with ⟨aX, bX, uX, vX⟩
  rcases Y with ⟨aY, bY, uY, vY⟩
  simp only [Zorn.a, Zorn.b, Zorn.u, Zorn.v] at ha hb hu hv
  simp_all

/-- Zorn multiplication in `(a,b,u,v)` order. -/
def zornMul (X Y : Zorn) : Zorn :=
  (X.a * Y.a + dot3 X.u Y.v,
    X.b * Y.b + dot3 X.v Y.u,
    fun i => X.a * Y.u i + Y.b * X.u i - cross3 X.v Y.v i,
    fun i => Y.a * X.v i + X.b * Y.v i + cross3 X.u Y.u i)

/-- Diagonal boost element `(p,p⁻¹,0,0)`. -/
def E (p : ℂ) : Zorn := (p, p⁻¹, fun _ => 0, fun _ => 0)

/-- Inverse diagonal boost `(p⁻¹,p,0,0)`. -/
def Einv (p : ℂ) : Zorn := (p⁻¹, p, fun _ => 0, fun _ => 0)

/-- Zorn conjugation by the diagonal boost. -/
def flow (p : ℂ) (X : Zorn) : Zorn := zornMul (zornMul (E p) X) (Einv p)

/-- The user's scaling formula: `a,b` fixed, `u ↦ p²u`, `v ↦ p⁻²v`. -/
theorem flow_formula {p : ℂ} (hp : p ≠ 0) (X : Zorn) :
    flow p X =
      (X.a, X.b,
        fun i => p^2 * X.u i,
        fun i => (p⁻¹)^2 * X.v i) := by
  apply zorn_ext
  · simp [flow, zornMul, E, Einv, dot3]
    field_simp [hp]
  · simp [flow, zornMul, E, Einv, dot3]
    field_simp [hp]
  · funext i
    fin_cases i <;> simp [flow, zornMul, E, Einv, cross3] <;> field_simp [hp]
  · funext i
    fin_cases i <;> simp [flow, zornMul, E, Einv, cross3] <;> field_simp [hp]

/-- Pure upper nilpotent. -/
def upperNil (u : Vec3) : Zorn := (0, 0, u, fun _ => 0)

/-- Pure lower nilpotent. -/
def lowerNil (v : Vec3) : Zorn := (0, 0, fun _ => 0, v)

/-- Zero element. -/
def zero : Zorn := (0, 0, fun _ => 0, fun _ => 0)

/-- Upper nilpotents square to zero. -/
theorem upperNil_sq_zero (u : Vec3) : zornMul (upperNil u) (upperNil u) = zero := by
  apply zorn_ext
  · simp [zornMul, upperNil, zero, dot3]
  · simp [zornMul, upperNil, zero, dot3]
  · funext i; fin_cases i <;> simp [zornMul, upperNil, zero, cross3]
  · funext i; fin_cases i <;> simp [zornMul, upperNil, zero, cross3] <;> ring

/-- Lower nilpotents square to zero. -/
theorem lowerNil_sq_zero (v : Vec3) : zornMul (lowerNil v) (lowerNil v) = zero := by
  apply zorn_ext
  · simp [zornMul, lowerNil, zero, dot3]
  · simp [zornMul, lowerNil, zero, dot3]
  · funext i; fin_cases i <;> simp [zornMul, lowerNil, zero, cross3] <;> ring
  · funext i; fin_cases i <;> simp [zornMul, lowerNil, zero, cross3]

end ZornScalingFlowOrdered
