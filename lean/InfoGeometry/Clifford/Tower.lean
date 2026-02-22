import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import InfoGeometry.Clifford.SplitQ11

/-!
# Split Clifford Tower

Mathlib-native split `(1,1)` quadratic form and recursive product tower, together
with the one-step Clifford-algebra factorization.
-/

namespace InfoGeometry.CliffordTower

open scoped TensorProduct

/-- Backward-compatible alias to the canonical split form. -/
noncomputable abbrev Q11 : QuadraticForm ℝ (ℝ × ℝ) := InfoGeometry.Clifford.splitQ11

@[simp] lemma Q11_apply (x : ℝ × ℝ) :
    Q11 x = x.1 * x.1 - x.2 * x.2 := by
  exact InfoGeometry.Clifford.splitQ11_apply x

/-- Recursive split space `(ℝ × ℝ)^n` as an iterated product. -/
abbrev SplitSpace : ℕ → Type _
  | 0 => Fin 0 → (ℝ × ℝ)
  | n + 1 => (ℝ × ℝ) × SplitSpace n

instance splitSpaceAddCommGroup : ∀ n : ℕ, AddCommGroup (SplitSpace n)
  | 0 => by
      change AddCommGroup (Fin 0 → (ℝ × ℝ))
      infer_instance
  | n + 1 => by
      letI : AddCommGroup (SplitSpace n) := splitSpaceAddCommGroup n
      change AddCommGroup ((ℝ × ℝ) × SplitSpace n)
      infer_instance

instance splitSpaceModule : ∀ n : ℕ, Module ℝ (SplitSpace n)
  | 0 => by
      change Module ℝ (Fin 0 → (ℝ × ℝ))
      infer_instance
  | n + 1 => by
      letI : AddCommGroup (SplitSpace n) := splitSpaceAddCommGroup n
      letI : Module ℝ (SplitSpace n) := splitSpaceModule n
      change Module ℝ ((ℝ × ℝ) × SplitSpace n)
      infer_instance

/-- Recursive split quadratic form: `Q(n+1) = Q11.prod Q(n)`. -/
noncomputable def Qsplit : (n : ℕ) → QuadraticForm ℝ (SplitSpace n)
  | 0 => 0
  | n + 1 => Q11.prod (Qsplit n)

@[simp] lemma Qsplit_zero_apply (x : SplitSpace 0) :
    Qsplit 0 x = 0 := by
  simp [Qsplit]

@[simp] lemma Qsplit_succ_apply (n : ℕ) (x : ℝ × ℝ) (xs : SplitSpace n) :
    Qsplit (n + 1) (x, xs) = Q11 x + Qsplit n xs := by
  simp [Qsplit, QuadraticMap.prod, LinearMap.fst, LinearMap.snd]

/-- The `n`-th Clifford algebra in the split tower. -/
abbrev Clsplit (n : ℕ) := CliffordAlgebra (Qsplit n)

/-- One-step factorization:
`Cl(Q11 ⊕ Qn) ≃ CliffordAlgebra.evenOdd Q11 ᵍ⊗ CliffordAlgebra.evenOdd (Qsplit n)`. -/
noncomputable def clsplit_succ_equiv (n : ℕ) :
    CliffordAlgebra (Qsplit (n + 1))
      ≃ₐ[ℝ] (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) := by
  simpa [Qsplit] using
    (CliffordAlgebra.prodEquiv (Q₁ := Q11) (Q₂ := Qsplit n))

end InfoGeometry.CliffordTower
