import InfoGeometry.Canonical.RealDoubledKreinMirrorTopologicalDirectSumTopCatIso
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Transported mirror action on the even/odd direct sum

The real mirror conjugation becomes the diagonal action `(u, v) ↦ (u, -v)`
under the continuous direct-sum equivalence.  This is the equivariant bridge
needed before any later colimit transport.
-/

namespace InfoGeometry.Canonical.DoubledHestenesKreinData

open CategoryTheory

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable (K : DoubledHestenesKreinData V)

noncomputable def mirrorProductActionLinear :
    (mirrorEvenSubmodule K × mirrorOddSubmodule K) →L[ℝ]
      (mirrorEvenSubmodule K × mirrorOddSubmodule K) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.fst ℝ (mirrorEvenSubmodule K)
      (mirrorOddSubmodule K))
    (-(ContinuousLinearMap.snd ℝ (mirrorEvenSubmodule K)
      (mirrorOddSubmodule K)))

@[simp] theorem mirrorProductActionLinear_apply
    (p : mirrorEvenSubmodule K × mirrorOddSubmodule K) :
    mirrorProductActionLinear K p = (p.1, -p.2) := rfl

noncomputable def mirrorProductActionTopCatHom :
    TopCat.of (mirrorEvenSubmodule K × mirrorOddSubmodule K) ⟶
      TopCat.of (mirrorEvenSubmodule K × mirrorOddSubmodule K) :=
  TopCat.ofHom
    { toFun := mirrorProductActionLinear K
      continuous_toFun := (mirrorProductActionLinear K).continuous }

@[simp] theorem mirrorProductActionTopCatHom_apply
    (p : mirrorEvenSubmodule K × mirrorOddSubmodule K) :
    mirrorProductActionTopCatHom K p = (p.1, -p.2) := rfl

theorem mirrorProductActionLinear_equivariant
    (T : ContinuousOperator V) :
    mirrorProductActionLinear K (mirrorProjectionToProduct K T) =
      mirrorProjectionToProduct K (mirrorConjugateContinuous K T) := by
  apply Prod.ext
  · apply Subtype.ext
    change mirrorEvenPart K T =
      mirrorEvenPart K (mirrorConjugateContinuous K T)
    unfold mirrorEvenPart
    change (1 / 2 : ℝ) •
        (T + mirrorConjugateContinuous K T) =
      (1 / 2 : ℝ) •
        (mirrorConjugateContinuous K T +
          mirrorConjugateContinuousLinear K
            (mirrorConjugateContinuous K T))
    rw [mirrorConjugateContinuousLinear_apply,
      mirrorConjugateContinuous_involutive]
    module
  · apply Subtype.ext
    change -(mirrorOddPart K T) =
      mirrorOddPart K (mirrorConjugateContinuous K T)
    unfold mirrorOddPart
    change -((1 / 2 : ℝ) •
        (T - mirrorConjugateContinuous K T)) =
      (1 / 2 : ℝ) •
        (mirrorConjugateContinuous K T -
          mirrorConjugateContinuousLinear K
            (mirrorConjugateContinuous K T))
    rw [mirrorConjugateContinuousLinear_apply,
      mirrorConjugateContinuous_involutive]
    module

theorem mirrorProjectionTopCatIso_mirror_square :
    mirrorConjugateTopCatHom K ≫
        (mirrorProjectionTopCatIso K).hom =
      (mirrorProjectionTopCatIso K).hom ≫
        mirrorProductActionTopCatHom K := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro T
  change mirrorProjectionToProduct K
      (mirrorConjugateContinuous K T) =
    mirrorProductActionLinear K (mirrorProjectionToProduct K T)
  exact (mirrorProductActionLinear_equivariant K T).symm

end
end InfoGeometry.Canonical.DoubledHestenesKreinData
