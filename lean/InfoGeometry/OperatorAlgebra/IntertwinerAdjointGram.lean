/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Adjoint intertwiners and cross-Gram operators

Bounded intertwiners between two Hilbert-space star representations have
adjoints intertwining in the reverse direction. Consequently, `S† ∘ T`
centralizes the source representation when `S` and `T` intertwine the same
pair of representations. No commutativity or normality of the represented
operators is assumed.

This is a typed source-space operator construction. It does not identify the
commutant with a local algebra or construct a relative tensor product.
In particular, a cross-Gram operator with distinct `S` and `T` is not asserted
positive.
-/

namespace InfoGeometry.OperatorAlgebra.IntertwinerAdjointGram

variable {A E F : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {π : A →⋆ₐ[ℂ] (E →L[ℂ] E)} {ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)}

/-- Taking the Hilbert adjoint reverses an intertwiner of star representations.
The proof uses intertwining at `star a`, rather than assuming `π a` normal. -/
theorem adjoint_intertwines {T : E →L[ℂ] F}
    (hT : ∀ a, T.comp (π a) = (ρ a).comp T) (a : A) :
    T.adjoint.comp (ρ a) = (π a).comp T.adjoint := by
  have h := congrArg (fun L : E →L[ℂ] F => L.adjoint) (hT (star a))
  simpa only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h.symm

/-- The cross-Gram operator of two intertwiners commutes with the entire
source representation. The order `S† ∘ T` is essential. -/
theorem adjoint_comp_commute {S T : E →L[ℂ] F}
    (hS : ∀ a, S.comp (π a) = (ρ a).comp S)
    (hT : ∀ a, T.comp (π a) = (ρ a).comp T) (a : A) :
    Commute (S.adjoint.comp T) (π a) := by
  change (S.adjoint.comp T).comp (π a) = (π a).comp (S.adjoint.comp T)
  calc
    (S.adjoint.comp T).comp (π a) = S.adjoint.comp (T.comp (π a)) :=
      ContinuousLinearMap.comp_assoc _ _ _
    _ = S.adjoint.comp ((ρ a).comp T) := by rw [hT a]
    _ = (S.adjoint.comp (ρ a)).comp T := (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = ((π a).comp S.adjoint).comp T := by rw [adjoint_intertwines hS a]
    _ = (π a).comp (S.adjoint.comp T) := ContinuousLinearMap.comp_assoc _ _ _

end InfoGeometry.OperatorAlgebra.IntertwinerAdjointGram
