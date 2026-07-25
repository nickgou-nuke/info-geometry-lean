import Mathlib

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
structure Zorn where
  a : ℂ
  b : ℂ
  u : Vec3
  v : Vec3

/-- Extensionality for Zorn coordinates. -/
theorem zorn_ext {X Y : Zorn}
    (ha : X.a = Y.a) (hb : X.b = Y.b) (hu : X.u = Y.u) (hv : X.v = Y.v) : X = Y := by
  cases X
  cases Y
  simp_all

/-- Zorn multiplication in `(a,b,u,v)` order. -/
def zornMul (X Y : Zorn) : Zorn where
  a := X.a * Y.a + dot3 X.u Y.v
  b := X.b * Y.b + dot3 X.v Y.u
  u := fun i => X.a * Y.u i + Y.b * X.u i - cross3 X.v Y.v i
  v := fun i => Y.a * X.v i + X.b * Y.v i + cross3 X.u Y.u i

/-- Diagonal boost element `(p,p⁻¹,0,0)`. -/
def E (p : ℂ) : Zorn where
  a := p
  b := p⁻¹
  u := fun _ => 0
  v := fun _ => 0

/-- Inverse diagonal boost `(p⁻¹,p,0,0)`. -/
def Einv (p : ℂ) : Zorn where
  a := p⁻¹
  b := p
  u := fun _ => 0
  v := fun _ => 0

/-- Zorn conjugation by the diagonal boost. -/
def flow (p : ℂ) (X : Zorn) : Zorn := zornMul (zornMul (E p) X) (Einv p)

/-- The user's scaling formula: `a,b` fixed, `u ↦ p²u`, `v ↦ p⁻²v`. -/
theorem flow_formula {p : ℂ} (hp : p ≠ 0) (X : Zorn) :
    flow p X =
      { a := X.a,
        b := X.b,
        u := fun i => p^2 * X.u i,
        v := fun i => (p⁻¹)^2 * X.v i } := by
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
def upperNil (u : Vec3) : Zorn where
  a := 0; b := 0; u := u; v := fun _ => 0

/-- Pure lower nilpotent. -/
def lowerNil (v : Vec3) : Zorn where
  a := 0; b := 0; u := fun _ => 0; v := v

/-- Zero element. -/
def zero : Zorn where
  a := 0; b := 0; u := fun _ => 0; v := fun _ => 0

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

/-- Synthesis theorem for the ordered tuple convention. -/
theorem zorn_scaling_flow_ordered_synthesis :
    (∀ {p : ℂ}, p ≠ 0 → ∀ X : Zorn,
      flow p X = { a := X.a, b := X.b, u := fun i => p^2 * X.u i, v := fun i => (p⁻¹)^2 * X.v i }) ∧
    (∀ u : Vec3, zornMul (upperNil u) (upperNil u) = zero) ∧
    (∀ v : Vec3, zornMul (lowerNil v) (lowerNil v) = zero) := by
  exact ⟨flow_formula, upperNil_sq_zero, lowerNil_sq_zero⟩

#check flow_formula
#check upperNil_sq_zero
#check lowerNil_sq_zero
#check zorn_scaling_flow_ordered_synthesis

end ZornScalingFlowOrdered
