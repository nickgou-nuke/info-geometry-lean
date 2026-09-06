import InfoGeometry.Algebra.CuntzSupergradedSUSY
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# Topological realization of the Cuntz supergraded parity

`CuntzAlg n` is intentionally algebraic.  A realization into a concrete
topological C*-algebra is therefore supplied explicitly.  This owner records
the continuous parity endomorphism in `TopCat` and transports the verified
odd/even formulas for the Majorana supercharge and its square.
-/

noncomputable section

namespace InfoGeometry.Algebra.SupergradedSUSY.Topological

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzSuperalgebra
open InfoGeometry.Algebra.SupergradedSUSY

universe u

variable {B : Type u} [CStarAlgebra B]

/-- An explicit topological realization of the finite Cuntz quotient together
with a continuous parity automorphism of its target.  No topology is inferred
for the source quotient. -/
structure Realization (n : ℕ) where
  representation : CuntzAlg n →⋆ₐ[ℂ] B
  parity : B ≃ₐ[ℂ] B

def parityTopCatEndomorphism (R : Realization (B := B) n)
    (h_cont : Continuous R.parity) :
    TopCat.of B ⟶ TopCat.of B :=
  TopCat.ofHom
    { toFun := R.parity
      continuous_toFun := h_cont }

@[simp] theorem parityTopCatEndomorphism_apply
    (R : Realization (B := B) n) (h_cont : Continuous R.parity) (x : B) :
    parityTopCatEndomorphism R h_cont x = R.parity x :=
  rfl

theorem parityTopCatEndomorphism_comp_self
    (R : Realization (B := B) n) (h_cont : Continuous R.parity)
    (h_involutive : ∀ x : B, R.parity (R.parity x) = x) :
    parityTopCatEndomorphism R h_cont ≫ parityTopCatEndomorphism R h_cont =
      𝟙 (TopCat.of B) := by
  apply TopCat.hom_ext
  ext x
  rw [TopCat.comp_app, TopCat.id_app]
  exact h_involutive x

theorem parity_representation_cuntzMajoranaSupercharge
    (R : Realization (B := B) n)
    (h_intertwines : ∀ x : CuntzAlg n,
      R.representation (InfoGeometry.Algebra.CuntzSuperalgebra.parity n x) =
        R.parity (R.representation x))
    (i : Fin n) :
    R.parity
        (R.representation (cuntzMajoranaSupercharge n i)) =
      -R.representation (cuntzMajoranaSupercharge n i) := by
  calc
    R.parity
        (R.representation (cuntzMajoranaSupercharge n i)) =
        R.representation
          (InfoGeometry.Algebra.CuntzSuperalgebra.parity n
            (cuntzMajoranaSupercharge n i)) := by
      exact (h_intertwines _).symm
    _ = R.representation (-cuntzMajoranaSupercharge n i) := by
      rw [parity_cuntzMajoranaSupercharge]
    _ = -R.representation (cuntzMajoranaSupercharge n i) := by
      exact map_neg R.representation _

theorem parity_representation_cuntzSuperMomentum
    (R : Realization (B := B) n)
    (h_intertwines : ∀ x : CuntzAlg n,
      R.representation (InfoGeometry.Algebra.CuntzSuperalgebra.parity n x) =
        R.parity (R.representation x))
    (i : Fin n) :
    R.parity (R.representation (cuntzSuperMomentum n i)) =
      R.representation (cuntzSuperMomentum n i) := by
  calc
    R.parity (R.representation (cuntzSuperMomentum n i)) =
        R.representation
          (InfoGeometry.Algebra.CuntzSuperalgebra.parity n
            (cuntzSuperMomentum n i)) := by
      exact (h_intertwines _).symm
    _ = R.representation (cuntzSuperMomentum n i) := by
      rw [parity_cuntzSuperMomentum]

theorem parity_representation_cuntzCentralCharge
    (R : Realization (B := B) n)
    (h_intertwines : ∀ x : CuntzAlg n,
      R.representation (InfoGeometry.Algebra.CuntzSuperalgebra.parity n x) =
        R.parity (R.representation x)) :
    R.parity (R.representation (cuntzCentralCharge n)) =
      R.representation (cuntzCentralCharge n) := by
  calc
    R.parity (R.representation (cuntzCentralCharge n)) =
        R.representation
          (InfoGeometry.Algebra.CuntzSuperalgebra.parity n
            (cuntzCentralCharge n)) := by
      exact (h_intertwines _).symm
    _ = R.representation (cuntzCentralCharge n) := by
      rw [parity_cuntzCentralCharge]

end InfoGeometry.Algebra.SupergradedSUSY.Topological
