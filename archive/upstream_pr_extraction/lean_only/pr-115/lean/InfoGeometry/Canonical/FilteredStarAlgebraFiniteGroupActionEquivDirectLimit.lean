import InfoGeometry.Canonical.FilteredStarAlgebraFiniteGroupActionDirectLimit

/-!
# Star-algebra equivalences from compatible finite-group actions on the native direct limit

This file packages the already-descended finite-group action as a genuine
`StarAlgEquiv`.  It does not introduce a new colimit carrier, crossed-product
completion, or quotient algebra.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionEquivDirectLimit

open CStarStateColimit.Native
open FilteredStarAlgebraDirectLimit
open FilteredStarAlgebraFiniteGroupActionDirectLimit

universe u

variable {I G : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [Group G] [Fintype G] [DecidableEq G]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (A : CompatibleStarGroupAction I G Stage sys)

theorem algebraicColimitGroupAction_bijective (g : G) :
    Function.Bijective (algebraicColimitGroupAction I G Stage sys A g) := by
  constructor
  · intro x y hxy
    have hcomp := congrArg
      (fun z => algebraicColimitGroupAction I G Stage sys A g⁻¹ z) hxy
    have hx :
        algebraicColimitGroupAction I G Stage sys A g⁻¹
            (algebraicColimitGroupAction I G Stage sys A g x) = x := by
      change
        ((algebraicColimitGroupAction I G Stage sys A g⁻¹).comp
          (algebraicColimitGroupAction I G Stage sys A g)) x = x
      rw [algebraicColimitGroupAction_inv_comp I G Stage sys A g]
      rfl
    have hy :
        algebraicColimitGroupAction I G Stage sys A g⁻¹
            (algebraicColimitGroupAction I G Stage sys A g y) = y := by
      change
        ((algebraicColimitGroupAction I G Stage sys A g⁻¹).comp
          (algebraicColimitGroupAction I G Stage sys A g)) y = y
      rw [algebraicColimitGroupAction_inv_comp I G Stage sys A g]
      rfl
    calc
      x = algebraicColimitGroupAction I G Stage sys A g⁻¹
          (algebraicColimitGroupAction I G Stage sys A g x) := hx.symm
      _ = algebraicColimitGroupAction I G Stage sys A g⁻¹
          (algebraicColimitGroupAction I G Stage sys A g y) := hcomp
      _ = y := hy
  · intro y
    refine ⟨algebraicColimitGroupAction I G Stage sys A g⁻¹ y, ?_⟩
    change
      ((algebraicColimitGroupAction I G Stage sys A g).comp
        (algebraicColimitGroupAction I G Stage sys A g⁻¹)) y = y
    rw [algebraicColimitGroupAction_comp_inv I G Stage sys A g]
    rfl

noncomputable def algebraicColimitGroupActionEquiv (g : G) :
    FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys ≃⋆ₐ[ℂ]
      FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys :=
  StarAlgEquiv.ofBijective
    (algebraicColimitGroupAction I G Stage sys A g)
    (algebraicColimitGroupAction_bijective (Stage := Stage) (sys := sys) (A := A) g)

@[simp] theorem algebraicColimitGroupActionEquiv_apply
    (g : G) (x) :
    algebraicColimitGroupActionEquiv Stage sys A g x =
      algebraicColimitGroupAction I G Stage sys A g x :=
  rfl

@[simp] theorem algebraicColimitGroupActionEquiv_one :
    algebraicColimitGroupActionEquiv Stage sys A 1 =
      (StarAlgEquiv.refl :
        FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys ≃⋆ₐ[ℂ]
          FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys) := by
  ext x
  simp [algebraicColimitGroupActionEquiv,
    algebraicColimitGroupAction_one]

theorem algebraicColimitGroupActionEquiv_mul
    (g h : G) :
    algebraicColimitGroupActionEquiv Stage sys A (g * h) =
      (algebraicColimitGroupActionEquiv Stage sys A h).trans
        (algebraicColimitGroupActionEquiv Stage sys A g) := by
  ext x
  change
    algebraicColimitGroupAction I G Stage sys A (g * h) x =
      algebraicColimitGroupAction I G Stage sys A g
        (algebraicColimitGroupAction I G Stage sys A h x)
  rw [algebraicColimitGroupAction_mul I G Stage sys A g h]
  rfl

end CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionEquivDirectLimit
