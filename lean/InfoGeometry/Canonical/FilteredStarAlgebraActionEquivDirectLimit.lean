import InfoGeometry.Canonical.FilteredStarAlgebraActionDirectLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Automorphism readout for the native noncommutative direct-limit action

The action owner descends stagewise `StarAlgHom`s.  This file records the
stronger fact that every time slice is bijective, using the already proved
`t`/`-t` composition laws, and packages the slice as a `StarAlgEquiv`.
No commutativity, diagonalization, norm completion, or quotient carrier is
introduced here.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredStarAlgebraActionEquivDirectLimit

open CStarStateColimit.Native
open FilteredStarAlgebraDirectLimit
open FilteredStarAlgebraActionDirectLimit

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (A : CompatibleStarAction Stage sys)

theorem algebraicColimitAction_bijective (t : ℤ) :
    Function.Bijective (algebraicColimitAction Stage sys A t) := by
  constructor
  · intro x y hxy
    have hcomp := congrArg
      (fun z => algebraicColimitAction Stage sys A (-t) z) hxy
    change
      algebraicColimitAction Stage sys A (-t)
          (algebraicColimitAction Stage sys A t x) =
        algebraicColimitAction Stage sys A (-t)
          (algebraicColimitAction Stage sys A t y) at hcomp
    have hx :
        algebraicColimitAction Stage sys A (-t)
            (algebraicColimitAction Stage sys A t x) = x := by
      change
        ((algebraicColimitAction Stage sys A (-t)).comp
          (algebraicColimitAction Stage sys A t)) x = x
      rw [algebraicColimitAction_comp_neg Stage sys A t]
      rfl
    have hy :
        algebraicColimitAction Stage sys A (-t)
            (algebraicColimitAction Stage sys A t y) = y := by
      change
        ((algebraicColimitAction Stage sys A (-t)).comp
          (algebraicColimitAction Stage sys A t)) y = y
      rw [algebraicColimitAction_comp_neg Stage sys A t]
      rfl
    exact hx.symm.trans (hcomp.trans hy)
  · intro y
    refine ⟨algebraicColimitAction Stage sys A (-t) y, ?_⟩
    change
      ((algebraicColimitAction Stage sys A t).comp
        (algebraicColimitAction Stage sys A (-t))) y = y
    rw [algebraicColimitAction_neg_comp Stage sys A t]
    rfl

noncomputable def algebraicColimitActionEquiv (t : ℤ) :
    FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys ≃⋆ₐ[ℂ]
      FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys :=
  StarAlgEquiv.ofBijective
    (algebraicColimitAction Stage sys A t)
    (algebraicColimitAction_bijective Stage sys A t)

@[simp] theorem algebraicColimitActionEquiv_apply (t : ℤ) (x) :
    algebraicColimitActionEquiv Stage sys A t x =
      algebraicColimitAction Stage sys A t x :=
  rfl

@[simp] theorem algebraicColimitActionEquiv_zero :
    algebraicColimitActionEquiv Stage sys A 0 =
      (StarAlgEquiv.refl :
        FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys ≃⋆ₐ[ℂ]
          FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys) := by
  ext x
  simp [algebraicColimitActionEquiv,
    algebraicColimitAction_zero Stage sys A]

theorem algebraicColimitActionEquiv_add (s t : ℤ) :
    algebraicColimitActionEquiv Stage sys A (s + t) =
      (algebraicColimitActionEquiv Stage sys A s).trans
        (algebraicColimitActionEquiv Stage sys A t) := by
  ext x
  change
    algebraicColimitAction Stage sys A (s + t) x =
      algebraicColimitAction Stage sys A t
        (algebraicColimitAction Stage sys A s x)
  rw [algebraicColimitAction_add Stage sys A s t]
  rfl

@[simp] theorem algebraicColimitActionEquiv_neg_trans (t : ℤ) :
    (algebraicColimitActionEquiv Stage sys A (-t)).trans
        (algebraicColimitActionEquiv Stage sys A t) =
      (StarAlgEquiv.refl :
        FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys ≃⋆ₐ[ℂ]
          FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys) := by
  ext x
  change
    algebraicColimitAction Stage sys A t
        (algebraicColimitAction Stage sys A (-t) x) = x
  change
    ((algebraicColimitAction Stage sys A t).comp
      (algebraicColimitAction Stage sys A (-t))) x = x
  rw [algebraicColimitAction_neg_comp Stage sys A t]
  rfl

@[simp] theorem algebraicColimitActionEquiv_trans_neg (t : ℤ) :
    (algebraicColimitActionEquiv Stage sys A t).trans
        (algebraicColimitActionEquiv Stage sys A (-t)) =
      (StarAlgEquiv.refl :
        FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys ≃⋆ₐ[ℂ]
          FilteredStarAlgebraDirectLimit.AlgebraicStarDirectLimit Stage sys) := by
  ext x
  change
    algebraicColimitAction Stage sys A (-t)
        (algebraicColimitAction Stage sys A t x) = x
  change
    ((algebraicColimitAction Stage sys A (-t)).comp
      (algebraicColimitAction Stage sys A t)) x = x
  rw [algebraicColimitAction_comp_neg Stage sys A t]
  rfl

end CStarStateColimit.Native.FilteredStarAlgebraActionEquivDirectLimit
