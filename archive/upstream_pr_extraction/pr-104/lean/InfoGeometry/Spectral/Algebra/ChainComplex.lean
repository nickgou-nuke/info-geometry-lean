import Mathlib

/-!
# Chain complexes for the Spectral port

The Lean2 reference uses a bespoke `module_chain_complex` carrier.  This file
exposes the corresponding Mathlib `ChainComplex (ModuleCat R) ℕ` boundary and
keeps the square-zero law available under Spectral names.
-/

namespace InfoGeometry.Spectral.Algebra

open CategoryTheory

universe u

namespace ModuleChainComplex

variable (R : Type u) [Ring R]

abbrev Carrier := ChainComplex (ModuleCat R) ℕ

/-- Construct a module chain complex from objects and differentials. -/
def of (X : ℕ → ModuleCat R)
    (d : ∀ n, X (n + 1) ⟶ X n)
    (sq : ∀ n, d (n + 1) ≫ d n = 0) : Carrier R :=
  ChainComplex.of X d sq

@[simp] theorem of_X (X : ℕ → ModuleCat R)
    (d : ∀ n, X (n + 1) ⟶ X n)
    (sq : ∀ n, d (n + 1) ≫ d n = 0) (n : ℕ) :
    (of R X d sq).X n = X n := rfl

theorem differential_squared (C : Carrier R) (n : ℕ) :
    C.d (n + 2) (n + 1) ≫ C.d (n + 1) n = 0 := by
  exact C.d_comp_d (n + 2) (n + 1) n

end ModuleChainComplex
end InfoGeometry.Spectral.Algebra
