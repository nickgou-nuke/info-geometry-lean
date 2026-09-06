import InfoGeometry.Canonical.RealDoubledKreinMirrorTopologicalDirectSumEquiv

/-!
# TopCat isomorphism for the real mirror direct sum

This is the categorical image of the finite-dimensional continuous linear
equivalence constructed by the preceding owner.
-/

namespace InfoGeometry.Canonical.DoubledHestenesKreinData

open CategoryTheory

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable (K : DoubledHestenesKreinData V)

noncomputable def mirrorProjectionTopCatIso :
    TopCat.of (ContinuousOperator V) ≅
  TopCat.of (mirrorEvenSubmodule K × mirrorOddSubmodule K) :=
  TopCat.isoOfHomeo
    (mirrorProjectionContinuousLinearEquiv K).toHomeomorph

@[simp] theorem mirrorProjectionTopCatIso_hom_apply
    (T : ContinuousOperator V) :
    (mirrorProjectionTopCatIso K).hom T =
      mirrorProjectionToProduct K T := rfl

@[simp] theorem mirrorProjectionTopCatIso_inv_apply
    (p : mirrorEvenSubmodule K × mirrorOddSubmodule K) :
    (mirrorProjectionTopCatIso K).inv p =
      mirrorProjectionFromProduct K p := rfl

end
end InfoGeometry.Canonical.DoubledHestenesKreinData
