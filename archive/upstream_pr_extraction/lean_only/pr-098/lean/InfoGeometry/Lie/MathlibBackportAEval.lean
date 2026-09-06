module

public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Algebra.Polynomial.Eval.Defs

public section

namespace Module.End

open Polynomial

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {f : End R M} {μ : R} {p : Polynomial R} {x : M}

lemma aeval_apply_of_mem_apply_eq_smul (hx : f x = μ • x) :
    aeval f p x = p.eval μ • x := by
  rcases eq_or_ne x 0 with rfl | hne
  · simp
  · exact aeval_apply_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hx, hne⟩

end Module.End
