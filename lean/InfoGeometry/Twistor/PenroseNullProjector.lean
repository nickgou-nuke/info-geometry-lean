/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LinearAlgebra.IsotropicSelfAdjoint
import InfoGeometry.Twistor.PerjesConventions

/-!
# The isotropic Penrose incidence plane and its oblique projector

The existing incidence graph is transported from the Witt frame to the
existing diagonal signature-`(2,2)` Hermitian carrier. For Hermitian spacetime
matrices its image is totally isotropic. A self-adjoint idempotent whose
image lies in that plane therefore vanishes.

The same graph has an explicit nonzero oblique projector, obtained by
retaining the lower spinor and reconstructing the upper spinor. This
projector is idempotent but is not self-adjoint for the Penrose pairing.
The assertions concern native linear maps and submodules, not a manifold
or a positive-definite inner product.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseNullProjector

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PerjesConventions
open scoped BigOperators Matrix

/-- The diagonal Penrose pairing separates its second argument, expressed
in the linear-first convention used by the native adjunction predicate. -/
theorem twistorHermitian_flip_separatingLeft :
    twistorHermitian.flip.SeparatingLeft := by
  intro z hz
  funext i
  have hi : twistorHermitian (Pi.single i (1 : ℂ)) z = 0 :=
    hz (Pi.single i (1 : ℂ))
  fin_cases i <;>
    simpa [twistorHermitian_apply, Fin.sum_univ_four, Pi.single_apply] using hi

/-- The existing signed incidence graph in the diagonal Penrose frame. -/
def incidenceEmbedding (X : ComplexSpacetime) : Spinor2 →ₗ[ℂ] TwistorCarrier :=
  wittToDiagonal.toLinearMap.comp (paperIncidence X)

@[simp] theorem incidenceEmbedding_apply (X : ComplexSpacetime) (pi : Spinor2) :
    incidenceEmbedding X pi = wittToDiagonal (paperIncidence X pi) := rfl

/-- The transported incidence graph retains the two-component spinor exactly. -/
theorem incidenceEmbedding_injective (X : ComplexSpacetime) :
    Function.Injective (incidenceEmbedding X) :=
  wittToDiagonal.injective.comp
    (incidenceSign.injective.comp (incidenceLinearMap_injective X))

/-- Hermitian spacetime incidence is totally isotropic after the actual
change of frame, including the owner's factor of two. -/
theorem incidenceEmbedding_isotropic (X : ComplexSpacetime) (hX : Xᴴ = X)
    (pi rho : Spinor2) :
    twistorHermitian (incidenceEmbedding X pi) (incidenceEmbedding X rho) = 0 := by
  change twistorHermitian (wittToDiagonal (paperIncidence X pi))
    (wittToDiagonal (paperIncidence X rho)) = 0
  rw [diagonal_pairing, paperIncidence_witt_isotropic X hX, mul_zero]

/-- A self-adjoint idempotent supported in the isotropic incidence plane
must be zero. Self-adjointness refers to the Penrose form itself. -/
theorem eq_zero_of_selfAdjoint_of_range_le_incidence
    (X : ComplexSpacetime) (hX : Xᴴ = X) (P : Module.End ℂ TwistorCarrier)
    (hP : IsIdempotentElem P) (hself : twistorHermitian.flip.IsSelfAdjoint P)
    (hrange : P.range ≤ (incidenceEmbedding X).range) : P = 0 := by
  apply InfoGeometry.LinearAlgebra.IsotropicSelfAdjoint.eq_zero_of_idempotent_of_image_isotropic
    twistorHermitian.flip twistorHermitian_flip_separatingLeft hP hself
  intro z w
  obtain ⟨pi, hpi⟩ := hrange (LinearMap.mem_range_self P z)
  obtain ⟨rho, hrho⟩ := hrange (LinearMap.mem_range_self P w)
  change twistorHermitian (P w) (P z) = 0
  rw [← hpi, ← hrho]
  exact incidenceEmbedding_isotropic X hX rho pi

/-- An oblique projector onto the incidence graph, using the actual lower
spinor projection in the Witt frame and then returning to the diagonal frame. -/
def incidenceProjection (X : ComplexSpacetime) : Module.End ℂ TwistorCarrier :=
  (incidenceEmbedding X).comp
    ((LinearMap.snd ℂ Spinor2 Spinor2).comp wittToDiagonal.symm.toLinearMap)

@[simp] theorem incidenceProjection_apply (X : ComplexSpacetime) (z : TwistorCarrier) :
    incidenceProjection X z =
      incidenceEmbedding X (wittToDiagonal.symm z).2 := rfl

/-- The graph projector fixes every incident twistor. -/
@[simp] theorem incidenceProjection_on_incidence (X : ComplexSpacetime) (pi : Spinor2) :
    incidenceProjection X (incidenceEmbedding X pi) = incidenceEmbedding X pi := by
  simp only [incidenceProjection_apply, incidenceEmbedding_apply,
    LinearEquiv.symm_apply_apply, paperIncidence_apply]

/-- The graph construction gives a genuine idempotent endomorphism. -/
theorem incidenceProjection_idempotent (X : ComplexSpacetime) :
    IsIdempotentElem (incidenceProjection X) := by
  change incidenceProjection X * incidenceProjection X = incidenceProjection X
  apply LinearMap.ext
  intro z
  change incidenceProjection X (incidenceProjection X z) = incidenceProjection X z
  rw [incidenceProjection_apply X z]
  exact incidenceProjection_on_incidence X _

/-- The range is exactly the transported incidence graph. -/
theorem incidenceProjection_range (X : ComplexSpacetime) :
    (incidenceProjection X).range = (incidenceEmbedding X).range := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(wittToDiagonal.symm w).2, rfl⟩
  · rintro ⟨pi, rfl⟩
    exact ⟨incidenceEmbedding X pi, incidenceProjection_on_incidence X pi⟩

/-- The oblique projector has complex rank two, inherited from the native
two-component spinor through the injective incidence embedding. -/
theorem incidenceProjection_finrank_range (X : ComplexSpacetime) :
    Module.finrank ℂ (incidenceProjection X).range = 2 := by
  rw [incidenceProjection_range,
    LinearMap.finrank_range_of_inj (incidenceEmbedding_injective X)]
  simpa [Spinor2, InfoGeometry.Algebra.FiniteSpin.Vec2C] using
    (Module.finrank_pi (R := ℂ) (ι := Fin 2))

/-- A nonzero lower spinor supplies a nonzero fixed vector of the projector. -/
theorem incidenceProjection_ne_zero (X : ComplexSpacetime) :
    incidenceProjection X ≠ 0 := by
  intro hzero
  let pi : Spinor2 := fun _ => 1
  have hemb : incidenceEmbedding X pi = 0 := by
    have hfix := incidenceProjection_on_incidence X pi
    rw [hzero, LinearMap.zero_apply] at hfix
    exact hfix.symm
  have hp : paperIncidence X pi = 0 := by
    apply wittToDiagonal.injective
    simpa only [incidenceEmbedding_apply, map_zero] using hemb
  have hlast := congrArg (fun Z : Twistor4 => Z.2 0) hp
  simp [paperIncidence_apply, pi] at hlast

/-- The nonzero projector onto a Hermitian spacetime incidence plane is
necessarily oblique for the Penrose Hermitian form. -/
theorem incidenceProjection_not_selfAdjoint (X : ComplexSpacetime) (hX : Xᴴ = X) :
    ¬ twistorHermitian.flip.IsSelfAdjoint (incidenceProjection X) := by
  intro hself
  apply incidenceProjection_ne_zero X
  exact eq_zero_of_selfAdjoint_of_range_le_incidence X hX (incidenceProjection X)
    (incidenceProjection_idempotent X) hself (incidenceProjection_range X).le

end InfoGeometry.Twistor.PenroseNullProjector
