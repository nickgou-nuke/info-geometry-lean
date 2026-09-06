import Mathlib

set_option autoImplicit false

/-!
# K₀ – Fibonacci – φ Ring

Connection between:
1. **Grothendieck group K₀** of a fusion category: classes of simple objects.
2. **Fibonacci anyon ring**: the `τ`-anyon with fusion rule `τ ⊗ τ = 1 ⊕ τ`.
3. **Golden ratio φ**: the quantum dimension of `τ` satisfies `φ² = φ + 1`.

This file provides the ring algebra of the Fibonacci fusion ring ℤ[τ]/(τ² = τ + 1).
-/

namespace Audit.K0FibonacciRing

section FibonacciRing

/-- The Fibonacci fusion ring ℤ[τ] / (τ² = τ + 1). -/
structure FibRing where
  a : ℤ
  b : ℤ

namespace FibRing

/-- The identity element: 1 = 1·1 + 0·τ. -/
def one : FibRing := ⟨1, 0⟩

/-- The τ-anyon generator: τ = 0·1 + 1·τ. -/
def tau : FibRing := ⟨0, 1⟩

/-- Addition: (a,b) + (c,d) = (a+c, b+d). -/
def add (x y : FibRing) : FibRing := ⟨x.a + y.a, x.b + y.b⟩

/-- Multiplication uses the fusion rule τ² = τ + 1. -/
def mul (x y : FibRing) : FibRing :=
  ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

instance : Zero FibRing := ⟨⟨0, 0⟩⟩
instance : Add FibRing := ⟨add⟩
instance : Mul FibRing := ⟨mul⟩
instance : One FibRing := ⟨one⟩

theorem one_a : (1 : FibRing).a = 1 := rfl
theorem one_b : (1 : FibRing).b = 0 := rfl
theorem tau_a : tau.a = 0 := rfl
theorem tau_b : tau.b = 1 := rfl
theorem add_a (x y : FibRing) : (x + y).a = x.a + y.a := rfl
theorem add_b (x y : FibRing) : (x + y).b = x.b + y.b := rfl
theorem mul_a (x y : FibRing) : (x * y).a = x.a * y.a + x.b * y.b := rfl
theorem mul_b (x y : FibRing) : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

/-! ## Ring axioms -/

theorem add_comm (x y : FibRing) : x + y = y + x :=
  calc
    x + y = ⟨x.a + y.a, x.b + y.b⟩ := rfl
    _ = ⟨y.a + x.a, y.b + x.b⟩ := by
      refine congrArg₂ FibRing.mk ?_ ?_
      · abel
      · abel
    _ = y + x := rfl

theorem add_assoc (x y z : FibRing) : (x + y) + z = x + (y + z) :=
  calc
    (x + y) + z = ⟨(x.a + y.a) + z.a, (x.b + y.b) + z.b⟩ := rfl
    _ = ⟨x.a + (y.a + z.a), x.b + (y.b + z.b)⟩ := by
      refine congrArg₂ FibRing.mk ?_ ?_
      · abel
      · abel
    _ = x + (y + z) := rfl

theorem zero_add (x : FibRing) : 0 + x = x :=
  calc
    0 + x = ⟨0 + x.a, 0 + x.b⟩ := rfl
    _ = ⟨x.a, x.b⟩ := by simp
    _ = x := rfl

theorem add_zero (x : FibRing) : x + 0 = x :=
  calc
    x + 0 = ⟨x.a + 0, x.b + 0⟩ := rfl
    _ = ⟨x.a, x.b⟩ := by simp
    _ = x := rfl

theorem mul_one (x : FibRing) : x * 1 = x :=
  calc
    x * 1 = ⟨x.a * 1 + x.b * 0, x.a * 0 + x.b * 1 + x.b * 0⟩ := rfl
    _ = ⟨x.a, x.b⟩ := by ring
    _ = x := rfl

theorem one_mul (x : FibRing) : 1 * x = x :=
  calc
    1 * x = ⟨1 * x.a + 0 * x.b, 1 * x.b + 0 * x.a + 0 * x.b⟩ := rfl
    _ = ⟨x.a, x.b⟩ := by ring
    _ = x := rfl

theorem mul_comm (x y : FibRing) : x * y = y * x :=
  calc
    x * y = ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩ := rfl
    _ = ⟨y.a * x.a + y.b * x.b, y.a * x.b + y.b * x.a + y.b * x.b⟩ := by ring
    _ = y * x := rfl

/-- The fusion rule for τ: τ² = τ + 1. -/
theorem tau_sq_eq_tau_add_one : tau * tau = tau + 1 :=
  calc
    tau * tau = ⟨0*0 + 1*1, 0*1 + 1*0 + 1*1⟩ := rfl
    _ = ⟨1, 1⟩ := by ring
    _ = ⟨0 + 1, 1 + 0⟩ := by simp
    _ = tau + 1 := rfl

/--
The Fibonacci ring embeds injectively into ℤ × ℤ as an additive group.
-/
def toProd (x : FibRing) : ℤ × ℤ := (x.a, x.b)

theorem toProd_injective : Function.Injective (toProd : FibRing → ℤ × ℤ) := by
  intro x y h
  have ha : x.a = y.a := congrArg Prod.fst h
  have hb : x.b = y.b := congrArg Prod.snd h
  calc
    x = ⟨x.a, x.b⟩ := rfl
    _ = ⟨y.a, y.b⟩ := by simp [ha, hb]
    _ = y := rfl

end FibRing

end FibonacciRing

section GoldenRatio

/-- The golden ratio φ = (1+√5)/2, the quantum dimension of τ. -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

theorem φ_sq_eq_φ_add_one : φ ^ 2 = φ + 1 := by
  unfold φ
  have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith

/-- The quantum dimension map d: FibRing → ℝ. -/
noncomputable def quantumDimension (x : FibRing) : ℝ := (x.a : ℝ) + (x.b : ℝ) * φ

theorem quantumDimension_one : quantumDimension (1 : FibRing) = 1 := by
  calc
    quantumDimension (1 : FibRing) = ((1 : FibRing).a : ℝ) + ((1 : FibRing).b : ℝ) * φ := rfl
    _ = (1 : ℝ) + (0 : ℝ) * φ := by simp [FibRing.one_a, FibRing.one_b]
    _ = 1 := by ring

theorem quantumDimension_tau : quantumDimension (FibRing.tau) = φ := by
  calc
    quantumDimension (FibRing.tau) = ((FibRing.tau).a : ℝ) + ((FibRing.tau).b : ℝ) * φ := rfl
    _ = (0 : ℝ) + (1 : ℝ) * φ := by simp [FibRing.tau_a, FibRing.tau_b]
    _ = φ := by ring

/-- The quantum dimension is additive: d(x+y) = d(x) + d(y). -/
theorem quantumDimension_add (x y : FibRing) :
    quantumDimension (x + y) = quantumDimension x + quantumDimension y := by
  calc
    quantumDimension (x + y) = ((x + y).a : ℝ) + ((x + y).b : ℝ) * φ := rfl
    _ = ((x.a : ℝ) + (y.a : ℝ)) + ((x.b : ℝ) + (y.b : ℝ)) * φ := by
      simp [FibRing.add_a, FibRing.add_b, Int.cast_add]
    _ = ((x.a : ℝ) + (x.b : ℝ) * φ) + ((y.a : ℝ) + (y.b : ℝ) * φ) := by ring
    _ = quantumDimension x + quantumDimension y := rfl

end GoldenRatio

end Audit.K0FibonacciRing
