import InfoGeometry.Canonical.ChiralLightConeTensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# One-step decomposition of the finite causal-word tower

The finite word carrier is split into its first chiral arrow and the
remaining tail.  This is a carrier-level equivalence; no topology or infinite
boundary identification is asserted here.
-/

namespace InfoGeometry.Canonical.CantorWordTowerDecomposition

open InfoGeometry.Canonical.ChiralLightConeTensorTower

noncomputable def causalWordSuccEquiv (n : ℕ) :
    CausalWord (n + 1) ≃ ChiralArrow × CausalWord n where
  toFun w := (w 0, fun i => w i.succ)
  invFun p := Fin.cases p.1 (fun i => p.2 i)
  left_inv w := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  right_inv p := by
    cases p with
    | mk a t =>
      rfl

@[simp] theorem causalWordSuccEquiv_apply_head (n : ℕ)
    (w : CausalWord (n + 1)) :
    (causalWordSuccEquiv n w).1 = w 0 := rfl

@[simp] theorem causalWordSuccEquiv_apply_tail (n : ℕ)
    (w : CausalWord (n + 1)) (i : Fin n) :
    (causalWordSuccEquiv n w).2 i = w i.succ := rfl

@[simp] theorem causalWordSuccEquiv_symm_apply_zero (n : ℕ)
    (a : ChiralArrow) (w : CausalWord n) :
    (causalWordSuccEquiv n).symm (a, w) 0 = a := rfl

@[simp] theorem causalWordSuccEquiv_symm_apply_succ (n : ℕ)
    (a : ChiralArrow) (w : CausalWord n) (i : Fin n) :
    (causalWordSuccEquiv n).symm (a, w) i.succ = w i := rfl

noncomputable def cylinderFunctionSuccEquiv (n : ℕ) :
    (CausalWord (n + 1) → ℝ) ≃
      (CausalWord n → ℝ) × (CausalWord n → ℝ) where
  toFun F :=
    (fun w => F ((causalWordSuccEquiv n).symm (ChiralArrow.plus, w)),
      fun w => F ((causalWordSuccEquiv n).symm (ChiralArrow.minus, w)))
  invFun p w :=
    match (causalWordSuccEquiv n w).1 with
    | ChiralArrow.plus => p.1 (causalWordSuccEquiv n w).2
    | ChiralArrow.minus => p.2 (causalWordSuccEquiv n w).2
  left_inv F := by
    funext w
    dsimp
    split <;> rename_i hhead
    · apply congrArg F
      funext i
      exact Fin.cases
        ((causalWordSuccEquiv_symm_apply_zero n ChiralArrow.plus
          (causalWordSuccEquiv n w).2).trans hhead.symm)
        (fun j => causalWordSuccEquiv_symm_apply_succ n ChiralArrow.plus
          (causalWordSuccEquiv n w).2 j) i
    · apply congrArg F
      funext i
      exact Fin.cases
        ((causalWordSuccEquiv_symm_apply_zero n ChiralArrow.minus
          (causalWordSuccEquiv n w).2).trans hhead.symm)
        (fun j => causalWordSuccEquiv_symm_apply_succ n ChiralArrow.minus
          (causalWordSuccEquiv n w).2 j) i
  right_inv p := by
    rcases p with ⟨pPlus, pMinus⟩
    apply Prod.ext <;> funext w <;> rfl

end InfoGeometry.Canonical.CantorWordTowerDecomposition
