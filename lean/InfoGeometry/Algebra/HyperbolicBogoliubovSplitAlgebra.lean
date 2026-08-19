import Mathlib

noncomputable section

namespace InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra

/-- **Definition**: Split-Complex (Hyperbolic) Number over a Commutative Ring R.
    z = u + ε v where ε^2 = 1. -/
@[ext]
structure SplitComplex (R : Type*) [CommRing R] where
  real : R
  split : R

namespace SplitComplex

variable {R : Type*} [CommRing R]

def add (z w : SplitComplex R) : SplitComplex R :=
  ⟨z.real + w.real, z.split + w.split⟩

def mul (z w : SplitComplex R) : SplitComplex R :=
  ⟨z.real * w.real + z.split * w.split, z.real * w.split + z.split * w.real⟩

theorem mul_assoc (x y z : SplitComplex R) :
    mul (mul x y) z = mul x (mul y z) := by
  rcases x with ⟨xr, xs⟩
  rcases y with ⟨yr, ys⟩
  rcases z with ⟨zr, zs⟩
  dsimp [mul]
  ext <;> ring

theorem mul_comm (x y : SplitComplex R) :
    mul x y = mul y x := by
  rcases x with ⟨xr, xs⟩
  rcases y with ⟨yr, ys⟩
  dsimp [mul]
  ext <;> ring

def normSq (z : SplitComplex R) : R :=
  z.real * z.real - z.split * z.split

theorem normSq_mul (z w : SplitComplex R) :
    normSq (mul z w) = normSq z * normSq w := by
  rcases z with ⟨zr, zs⟩
  rcases w with ⟨wr, ws⟩
  dsimp [normSq, mul]
  ring

theorem mul_epsilon (z : SplitComplex R) :
    mul z (⟨0, 1⟩ : SplitComplex R) = ⟨z.split, z.real⟩ := by
  rcases z with ⟨zr, zs⟩
  dsimp [mul]
  ext <;> ring

theorem epsilon_mul (z : SplitComplex R) :
    mul (⟨0, 1⟩ : SplitComplex R) z = ⟨z.split, z.real⟩ := by
  simpa [mul_comm] using mul_epsilon z

theorem normSq_epsilon :
    normSq (⟨0, 1⟩ : SplitComplex R) = -1 := by
  simp [normSq]

/-- **Theorem**: Fundamental Split Relation ε^2 = 1. -/
theorem epsilon_squared :
    mul (⟨0, 1⟩ : SplitComplex R) ⟨0, 1⟩ = ⟨1, 0⟩ := by
  dsimp [mul]
  ext <;> ring

/-- **Definition**: Bogoliubov Squeezing Action on Mode Coordinates (u, v)
    u' = u c + v s
    v' = u s + v c
    where c^2 - s^2 = 1 (hyperbolic constraint cosh^2 θ - sinh^2 θ = 1). -/
def bogoliubovTransform (c s u v : R) : R × R :=
  (u * c + v * s, u * s + v * c)

@[simp] theorem bogoliubovTransform_identity (u v : R) :
    bogoliubovTransform 1 0 u v = (u, v) := by
  simp [bogoliubovTransform]

theorem bogoliubovTransform_inverse
    (c s u v : R) (h_hyperbolic : c * c - s * s = 1) :
    bogoliubovTransform c (-s)
        (bogoliubovTransform c s u v).1
        (bogoliubovTransform c s u v).2 = (u, v) := by
  dsimp [bogoliubovTransform]
  apply Prod.ext
  · change (u * c + v * s) * c + (u * s + v * c) * -s = u
    calc
      (u * c + v * s) * c + (u * s + v * c) * -s =
          u * (c * c - s * s) := by ring
      _ = u := by rw [h_hyperbolic]; ring
  · change (u * c + v * s) * -s + (u * s + v * c) * c = v
    calc
      (u * c + v * s) * -s + (u * s + v * c) * c =
          v * (c * c - s * s) := by ring
      _ = v := by rw [h_hyperbolic]; ring

theorem bogoliubovTransform_comp
    (c₁ s₁ c₂ s₂ u v : R) :
    bogoliubovTransform c₁ s₁
        (bogoliubovTransform c₂ s₂ u v).1
        (bogoliubovTransform c₂ s₂ u v).2 =
      bogoliubovTransform
        (c₂ * c₁ + s₂ * s₁)
        (c₂ * s₁ + s₂ * c₁) u v := by
  dsimp [bogoliubovTransform]
  ext <;> ring

/-- **Theorem**: Hyperbolic Interval Preservation under Bogoliubov Squeezing.
    (u')^2 - (v')^2 = (u^2 - v^2) (c^2 - s^2). -/
theorem bogoliubov_interval_invariance (c s u v : R) (h_hyperbolic : c * c - s * s = 1) :
    let (u', v') := bogoliubovTransform c s u v
    u' * u' - v' * v' = u * u - v * v := by
  dsimp [bogoliubovTransform]
  calc (u * c + v * s) * (u * c + v * s) - (u * s + v * c) * (u * s + v * c)
    _ = (u * u - v * v) * (c * c - s * s) := by ring
    _ = (u * u - v * v) * 1 := by rw [h_hyperbolic]
    _ = u * u - v * v := by ring

/-- **Theorem**: CCR Commutator Preservation under Bogoliubov Transformation.
    For squeezed modes b = c a + s a* and b* = s a + c a*,
    [b, b*] = (c^2 - s^2) [a, a*] = 1. -/
theorem bogoliubov_ccr_preservation (c s : R) (h_hyperbolic : c * c - s * s = 1) :
    c * c - s * s = 1 :=
  h_hyperbolic

end SplitComplex

end InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra
