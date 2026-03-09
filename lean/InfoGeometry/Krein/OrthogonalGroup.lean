import InfoGeometry.Krein.Metric

/-!
# Krein Orthogonal Group

Group structure for automorphisms preserving the neutral Hessian pairing.
Provides the model for the indefinite orthogonal group `O(n,n)`.
Uses the hardened `NeutralSpace` newtype and a performance-optimized structure.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace
open KreinSpace NeutralSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Orthogonal isometries of the doubled neutral form (Hessian pairing).
Defined as a structure to avoid Subtype unification timeouts. -/
structure HessianOrthogonalGroup (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- The underlying continuous linear equivalence. -/
  equiv : NeutralSpace E ≃L[ℝ] NeutralSpace E
  /-- Proof that the equivalence preserves the Krein metric. -/
  is_isometry : IsKreinIsometry (equiv : NeutralSpace E →L[ℝ] NeutralSpace E)

namespace HessianOrthogonalGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[ext]
lemma ext {U V : HessianOrthogonalGroup E} (h : ∀ x, U.equiv x = V.equiv x) : U = V := by
  cases U; cases V
  congr
  exact ContinuousLinearEquiv.ext (funext h)

noncomputable instance : Group (HessianOrthogonalGroup E) where
  mul U V :=
    { equiv := U.equiv.trans V.equiv
      is_isometry := by
        intro u v
        exact (V.is_isometry (U.equiv u) (U.equiv v)).trans (U.is_isometry u v) }
  one := ⟨ContinuousLinearEquiv.refl ℝ (NeutralSpace E), IsKreinIsometry.id⟩
  inv U := ⟨U.equiv.symm, IsKreinIsometry.inv U.is_isometry⟩
  mul_assoc U V W := by ext; rfl
  one_mul U := by ext; rfl
  mul_one U := by ext; rfl
  inv_mul_cancel U := by
    apply HessianOrthogonalGroup.ext
    intro x
    exact U.equiv.apply_symm_apply x

instance : Coe (HessianOrthogonalGroup E) (NeutralSpace E ≃L[ℝ] NeutralSpace E) := ⟨equiv⟩

end HessianOrthogonalGroup

/-- Swap involution as an element of the Hessian orthogonal group. -/
noncomputable def modularJHessianOrthogonal : HessianOrthogonalGroup E :=
  ⟨(NeutralSpace.neutralJ (E := E)).toContinuousLinearEquiv, IsKreinIsometry.J⟩

end InfoGeometry.Krein
