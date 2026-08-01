import Mathlib.Tactic

/-!
# Zorn paravectors and lower nilpotent coordinates

This file works only with finite Zorn coordinates over `ℂ`.  The diagonal
coordinate form

`P=(E,E,p,p)`, i.e. `[[E,p],[p,E]]`,

has split norm `E²-p·p`.  The lower off-diagonal coordinate
`Z=(0,0,0,p)` has zero norm and squares to zero under Zorn multiplication.
-/

noncomputable section

namespace ZornParavectorNullspace

abbrev Vec3 := Fin 3 → ℂ

/-- Dot product on `ℂ³`. -/
def dot3 (u v : Vec3) : ℂ := ∑ i : Fin 3, u i * v i

/-- Cross product on `ℂ³`. -/
def cross3 (u v : Vec3) : Vec3
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

/-- Zorn coordinates in order `(a,b,u,v)` for `[[a,u],[v,b]]`. -/
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

/-- Zorn multiplication. -/
def zornMul (X Y : Zorn) : Zorn where
  a := X.a * Y.a + dot3 X.u Y.v
  b := X.b * Y.b + dot3 X.v Y.u
  u := fun i => X.a * Y.u i + Y.b * X.u i - cross3 X.v Y.v i
  v := fun i => Y.a * X.v i + X.b * Y.v i + cross3 X.u Y.u i

/-- Split/Zorn norm. -/
def zornNorm (X : Zorn) : ℂ := X.a * X.b - dot3 X.u X.v

/-- Zero Zorn element. -/
def zero : Zorn where
  a := 0; b := 0; u := fun _ => 0; v := fun _ => 0

/-- Diagonal Zorn coordinate `[[E,p],[p,E]]`. -/
def paravector (E : ℂ) (p : Vec3) : Zorn where
  a := E
  b := E
  u := p
  v := p

/-- Lower off-diagonal Zorn coordinate `[[0,0],[p,0]]`. -/
def collapsedLower (p : Vec3) : Zorn where
  a := 0
  b := 0
  u := fun _ => 0
  v := p

/-- The diagonal-coordinate norm is exactly the quadratic `E²-p·p`. -/
theorem paravector_norm_mass_shell (E : ℂ) (p : Vec3) :
    zornNorm (paravector E p) = E^2 - dot3 p p := by
  simp [zornNorm, paravector, dot3]
  ring

/-- The lower off-diagonal coordinate has zero norm. -/
theorem collapsed_state_norm_zero (p : Vec3) :
    zornNorm (collapsedLower p) = 0 := by
  simp [zornNorm, collapsedLower, dot3]

/-- Cross product of a vector with itself vanishes. -/
theorem cross_self_zero (p : Vec3) : cross3 p p = fun _ => 0 := by
  funext i
  fin_cases i <;> simp [cross3] <;> ring

/-- The lower off-diagonal coordinate is nilpotent: `Z²=0`. -/
theorem collapsed_state_nilpotent (p : Vec3) :
    zornMul (collapsedLower p) (collapsedLower p) = zero := by
  apply zorn_ext
  · simp [zornMul, collapsedLower, zero, dot3]
  · simp [zornMul, collapsedLower, zero, dot3]
  · funext i
    fin_cases i <;> simp [zornMul, collapsedLower, zero, cross3] <;> ring
  · funext i
    fin_cases i <;> simp [zornMul, collapsedLower, zero, cross3]

end ZornParavectorNullspace
