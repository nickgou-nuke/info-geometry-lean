import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.Data.Real.Basic

/-!
# Split Clifford Tower

Mathlib-native split `(1,1)` quadratic form and recursive product tower, together
with the one-step Clifford-algebra factorization.
-/

namespace InfoGeometry.CliffordTower

open scoped TensorProduct

/-- Split quadratic form of signature `(1,1)` on `ℝ × ℝ`: `x₁² - x₂²`. -/
noncomputable def Q11 : QuadraticForm ℝ (ℝ × ℝ) :=
  QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ)
    - QuadraticMap.linMulLin (LinearMap.snd ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)

@[simp] lemma Q11_apply (x : ℝ × ℝ) :
    Q11 x = x.1 * x.1 - x.2 * x.2 := by
  simp [Q11]

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
  | 0 => by
      change QuadraticForm ℝ (Fin 0 → (ℝ × ℝ))
      exact 0
  | n + 1 => by
      letI : AddCommGroup (SplitSpace n) := splitSpaceAddCommGroup n
      letI : Module ℝ (SplitSpace n) := splitSpaceModule n
      change QuadraticForm ℝ ((ℝ × ℝ) × SplitSpace n)
      exact Q11.prod (Qsplit n)

/-- The `n`-th Clifford algebra in the split tower. -/
abbrev Clsplit (n : ℕ) := CliffordAlgebra (Qsplit n)

/-- One-step factorization `Cl(Q11 ⊕ Qn) ≃ graded_tensor(Cl(Q11), Cl(Qn))`. -/
noncomputable def clsplit_succ_equiv (n : ℕ) :
    CliffordAlgebra (Qsplit (n + 1))
      ≃ₐ[ℝ] (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) := by
  letI : AddCommGroup (SplitSpace n) := splitSpaceAddCommGroup n
  letI : Module ℝ (SplitSpace n) := splitSpaceModule n
  change CliffordAlgebra (Q11.prod (Qsplit n))
      ≃ₐ[ℝ] (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n))
  exact CliffordAlgebra.prodEquiv (Q₁ := Q11) (Q₂ := Qsplit n)

end InfoGeometry.CliffordTower
