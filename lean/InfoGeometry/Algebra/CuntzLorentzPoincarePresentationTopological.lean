import InfoGeometry.Algebra.CuntzLorentzPoincarePresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# Topological realization of a finite Cuntz Lorentz/Poincare presentation

The finite quotient presentation remains algebraic.  A concrete topological
target is supplied explicitly, together with continuous target automorphisms
and the intertwining law.  Each group element then gives a native `TopCat`
endomorphism, and invariant supercharge-generated momentum is transported
without introducing a topology on the quotient source.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzLorentzPoincarePresentation.Topological

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzSuperalgebra
open InfoGeometry.Algebra.SupergradedSUSY
open InfoGeometry.Algebra.CuntzLorentzPoincarePresentation

universe u

variable {n : ℕ} {D : CuntzGradingDeformation n}
variable {G : Type u} [Group G]
variable {B : Type u} [CStarAlgebra B]

/-- Explicit continuous target realization of an algebraic Cuntz presentation.
The pointwise action laws are stated on elements so that no category-level
action structure is assumed beyond the finite algebraic presentation. -/
structure Realization (T : CuntzPresentationOperator n D G) where
  representation : CuntzAlg n →⋆ₐ[ℂ] B
  action : G → B ≃ₐ[ℂ] B

def actionTopCatMap
    (R : Realization (n := n) (D := D) (G := G) (B := B) T) (g : G)
    (h_cont : Continuous (R.action g)) :
    TopCat.of B ⟶ TopCat.of B :=
  TopCat.ofHom
    { toFun := R.action g
      continuous_toFun := h_cont }

@[simp] theorem actionTopCatMap_apply
    (R : Realization (n := n) (D := D) (G := G) (B := B) T) (g : G)
    (h_cont : Continuous (R.action g)) (x : B) :
    actionTopCatMap R g h_cont x = R.action g x :=
  rfl

theorem actionTopCatMap_one
    (R : Realization (n := n) (D := D) (G := G) (B := B) T)
    (h_cont : Continuous (R.action 1))
    (h_one : ∀ x, R.action 1 x = x) :
    actionTopCatMap R 1 h_cont = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact h_one x

theorem actionTopCatMap_mul
    (R : Realization (n := n) (D := D) (G := G) (B := B) T) (g h : G)
    (h_cont_gh : Continuous (R.action (g * h)))
    (h_cont_h : Continuous (R.action h))
    (h_cont_g : Continuous (R.action g))
    (h_mul : ∀ x : B, R.action (g * h) x = R.action g (R.action h x)) :
    actionTopCatMap R (g * h) h_cont_gh =
      actionTopCatMap R h h_cont_h ≫ actionTopCatMap R g h_cont_g := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  simpa [actionTopCatMap] using h_mul x

theorem action_representation_apply
    (R : Realization (n := n) (D := D) (G := G) (B := B) T) (g : G) (x : CuntzAlg n)
    (h_intertwines : ∀ (g : G) (x : CuntzAlg n),
      R.representation (T.op g x) = R.action g (R.representation x)) :
    R.action g (R.representation x) = R.representation (T.op g x) := by
  exact (h_intertwines g x).symm

theorem action_representation_momentum
    (R : Realization (n := n) (D := D) (G := G) (B := B) T) (g : G) (Q : CuntzAlg n)
    (h_intertwines : ∀ (g : G) (x : CuntzAlg n),
      R.representation (T.op g x) = R.action g (R.representation x))
    (hQ : T.op g Q = Q) :
    R.action g (R.representation (superMomentum Q)) =
      R.representation (superMomentum Q) := by
  rw [action_representation_apply R g (superMomentum Q) h_intertwines,
    T.map_superMomentum, hQ]

theorem action_representation_supercharge
    (R : Realization (n := n) (D := D) (G := G) (B := B) T) (g : G) (Q : CuntzAlg n)
    (h_intertwines : ∀ (g : G) (x : CuntzAlg n),
      R.representation (T.op g x) = R.action g (R.representation x))
    (hQ : T.op g Q = Q) :
    R.action g (R.representation
      (algebraicAnticommutator Q Q)) =
      R.representation (algebraicAnticommutator Q Q) := by
  rw [action_representation_apply R g (algebraicAnticommutator Q Q) h_intertwines,
    T.map_anticommutator, hQ]

end InfoGeometry.Algebra.CuntzLorentzPoincarePresentation.Topological
