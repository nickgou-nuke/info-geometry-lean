import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import InfoGeometry.Canonical.CanonicalZornTrialitySpinEquivariance

/-!
# The related-triples group and outer Cartan triality

The genuine home of Cartan triality is a group of three simultaneous
transformations, one on each typed eight-dimensional carrier.  This file
constructs the subgroup of

`GL(8v) × GL(8s) × GL(8c)`

which preserves all three quadratic forms and the cyclic composition-algebra
trilinear form.  This avoids identifying Cartan outer triality with the
internal cyclic permutation of the three Zorn coordinate axes.
-/

noncomputable section

namespace CanonicalZornOuterTrialityGroup

open InfoGeometry.Physics.SplitOctonionBraidSU3
open CanonicalZornProjectiveTKKBridge
open CanonicalZornCompositionTriality
open CanonicalZornCompositionFiveGradeBridge
open CanonicalZornCliffordRepresentation
open CanonicalZornRealSpin44
open CanonicalZornFiveGradedClosure
open InfoGeometry.Canonical.CanonicalZornTrialitySpinEquivariance
open ProjectiveAffineConformalClosure55

abbrev VectorGL := LinearMap.GeneralLinearGroup ℂ Vector8
abbrev SpinorPlusGL := LinearMap.GeneralLinearGroup ℂ SpinorPlus8
abbrev SpinorMinusGL := LinearMap.GeneralLinearGroup ℂ SpinorMinus8

/-- Ambient group of independently invertible maps on the three triality
carriers. -/
abbrev TrialityGL := VectorGL × SpinorPlusGL × SpinorMinusGL

def vectorAct (g : VectorGL) (V : Vector8) : Vector8 :=
  (g : Module.End ℂ Vector8) V

def spinorPlusAct (g : SpinorPlusGL) (S : SpinorPlus8) : SpinorPlus8 :=
  (g : Module.End ℂ SpinorPlus8) S

def spinorMinusAct (g : SpinorMinusGL) (C : SpinorMinus8) : SpinorMinus8 :=
  (g : Module.End ℂ SpinorMinus8) C

@[simp] theorem vectorAct_one (V : Vector8) : vectorAct 1 V = V := rfl
@[simp] theorem spinorPlusAct_one (S : SpinorPlus8) : spinorPlusAct 1 S = S := rfl
@[simp] theorem spinorMinusAct_one (C : SpinorMinus8) : spinorMinusAct 1 C = C := rfl

theorem vectorAct_mul (g h : VectorGL) (V : Vector8) :
    vectorAct (g * h) V = vectorAct g (vectorAct h V) := rfl

theorem spinorPlusAct_mul (g h : SpinorPlusGL) (S : SpinorPlus8) :
    spinorPlusAct (g * h) S = spinorPlusAct g (spinorPlusAct h S) := rfl

theorem spinorMinusAct_mul (g h : SpinorMinusGL) (C : SpinorMinus8) :
    spinorMinusAct (g * h) C = spinorMinusAct g (spinorMinusAct h C) := rfl

theorem vectorAct_inv_cancel (g : VectorGL) (V : Vector8) :
    vectorAct g (vectorAct g⁻¹ V) = V := by
  rw [← vectorAct_mul, mul_inv_cancel, vectorAct_one]

theorem spinorPlusAct_inv_cancel (g : SpinorPlusGL) (S : SpinorPlus8) :
    spinorPlusAct g (spinorPlusAct g⁻¹ S) = S := by
  rw [← spinorPlusAct_mul, mul_inv_cancel, spinorPlusAct_one]

theorem spinorMinusAct_inv_cancel (g : SpinorMinusGL) (C : SpinorMinus8) :
    spinorMinusAct g (spinorMinusAct g⁻¹ C) = C := by
  rw [← spinorMinusAct_mul, mul_inv_cancel, spinorMinusAct_one]

/-- A related triple preserves the three quadratic forms and Cartan's
trilinear composition form. -/
def IsRelatedTriple (g : TrialityGL) : Prop :=
  (∀ V, vectorNorm (vectorAct g.1 V) = vectorNorm V) ∧
  (∀ S, spinorPlusNorm (spinorPlusAct g.2.1 S) = spinorPlusNorm S) ∧
  (∀ C, spinorMinusNorm (spinorMinusAct g.2.2 C) = spinorMinusNorm C) ∧
  (∀ V S C,
    trialityForm (vectorAct g.1 V)
      (spinorPlusAct g.2.1 S) (spinorMinusAct g.2.2 C) =
        trialityForm V S C)

/-- The canonical related-triples subgroup. -/
def relatedTriples : Subgroup TrialityGL where
  carrier := {g | IsRelatedTriple g}
  one_mem' := by
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun _ _ _ => rfl⟩
  mul_mem' := by
    intro g h hg hh
    rcases hg with ⟨hgv, hgs, hgc, hgf⟩
    rcases hh with ⟨hhv, hhs, hhc, hhf⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro V
      change vectorNorm (vectorAct (g.1 * h.1) V) = vectorNorm V
      rw [vectorAct_mul, hgv, hhv]
    · intro S
      change spinorPlusNorm (spinorPlusAct (g.2.1 * h.2.1) S) =
        spinorPlusNorm S
      rw [spinorPlusAct_mul, hgs, hhs]
    · intro C
      change spinorMinusNorm (spinorMinusAct (g.2.2 * h.2.2) C) =
        spinorMinusNorm C
      rw [spinorMinusAct_mul, hgc, hhc]
    · intro V S C
      change trialityForm (vectorAct (g.1 * h.1) V)
        (spinorPlusAct (g.2.1 * h.2.1) S)
        (spinorMinusAct (g.2.2 * h.2.2) C) = trialityForm V S C
      rw [vectorAct_mul, spinorPlusAct_mul, spinorMinusAct_mul,
        hgf, hhf]
  inv_mem' := by
    intro g hg
    rcases hg with ⟨hgv, hgs, hgc, hgf⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro V
      change vectorNorm (vectorAct g.1⁻¹ V) = vectorNorm V
      calc
        vectorNorm (vectorAct g.1⁻¹ V) =
            vectorNorm (vectorAct g.1 (vectorAct g.1⁻¹ V)) :=
              (hgv (vectorAct g.1⁻¹ V)).symm
        _ = vectorNorm V := by rw [vectorAct_inv_cancel]
    · intro S
      calc
        spinorPlusNorm (spinorPlusAct g.2.1⁻¹ S) =
            spinorPlusNorm (spinorPlusAct g.2.1
              (spinorPlusAct g.2.1⁻¹ S)) :=
                (hgs (spinorPlusAct g.2.1⁻¹ S)).symm
        _ = spinorPlusNorm S := by rw [spinorPlusAct_inv_cancel]
    · intro C
      calc
        spinorMinusNorm (spinorMinusAct g.2.2⁻¹ C) =
            spinorMinusNorm (spinorMinusAct g.2.2
              (spinorMinusAct g.2.2⁻¹ C)) :=
                (hgc (spinorMinusAct g.2.2⁻¹ C)).symm
        _ = spinorMinusNorm C := by rw [spinorMinusAct_inv_cancel]
    · intro V S C
      calc
        trialityForm (vectorAct g.1⁻¹ V)
            (spinorPlusAct g.2.1⁻¹ S) (spinorMinusAct g.2.2⁻¹ C) =
          trialityForm
            (vectorAct g.1 (vectorAct g.1⁻¹ V))
            (spinorPlusAct g.2.1 (spinorPlusAct g.2.1⁻¹ S))
            (spinorMinusAct g.2.2 (spinorMinusAct g.2.2⁻¹ C)) :=
              (hgf (vectorAct g.1⁻¹ V) (spinorPlusAct g.2.1⁻¹ S)
                (spinorMinusAct g.2.2⁻¹ C)).symm
        _ = trialityForm V S C := by
          rw [vectorAct_inv_cancel, spinorPlusAct_inv_cancel,
            spinorMinusAct_inv_cancel]

/-- The group of related triples associated with the canonical Zorn
composition triality. -/
abbrev CartanTrialityGroup := relatedTriples

/-! ## The outer order-three permutation -/

/-- Transport an invertible endomorphism across a linear equivalence. -/
def transportGL {A B : Type*} [AddCommMonoid A] [Module ℂ A]
    [AddCommMonoid B] [Module ℂ B] (e : A ≃ₗ[ℂ] B) :
    LinearMap.GeneralLinearGroup ℂ A →*
      LinearMap.GeneralLinearGroup ℂ B :=
  Units.map (e.conjAlgEquiv ℂ).toRingHom.toMonoidHom

theorem transportGL_apply {A B : Type*} [AddCommMonoid A] [Module ℂ A]
    [AddCommMonoid B] [Module ℂ B] (e : A ≃ₗ[ℂ] B)
    (g : LinearMap.GeneralLinearGroup ℂ A) (x : A) :
    ((transportGL e g : LinearMap.GeneralLinearGroup ℂ B) :
      Module.End ℂ B) (e x) = e ((g : Module.End ℂ A) x) := by
  simp [transportGL, LinearEquiv.conjAlgEquiv_apply]

/-- Cyclically transport the three components
`(8v,8s,8c) ↦ (8c,8v,8s)` using the canonical typed coordinate
equivalences. -/
def trialityCycleAmbient : TrialityGL →* TrialityGL where
  toFun g :=
    (transportGL spinorMinusToVector g.2.2,
      transportGL vectorToSpinorPlus g.1,
      transportGL spinorPlusToSpinorMinus g.2.1)
  map_one' := by
    apply Prod.ext
    · exact map_one (transportGL spinorMinusToVector)
    · apply Prod.ext
      · exact map_one (transportGL vectorToSpinorPlus)
      · exact map_one (transportGL spinorPlusToSpinorMinus)
  map_mul' g h := by
    apply Prod.ext
    · exact map_mul (transportGL spinorMinusToVector) g.2.2 h.2.2
    · apply Prod.ext
      · exact map_mul (transportGL vectorToSpinorPlus) g.1 h.1
      · exact map_mul (transportGL spinorPlusToSpinorMinus) g.2.1 h.2.1

theorem trialityCycleAmbient_vector_apply (g : TrialityGL) (C : SpinorMinus8) :
    vectorAct (trialityCycleAmbient g).1 (spinorMinusToVector C) =
      spinorMinusToVector (spinorMinusAct g.2.2 C) := by
  exact transportGL_apply spinorMinusToVector g.2.2 C

theorem trialityCycleAmbient_spinorPlus_apply (g : TrialityGL) (V : Vector8) :
    spinorPlusAct (trialityCycleAmbient g).2.1 (vectorToSpinorPlus V) =
      vectorToSpinorPlus (vectorAct g.1 V) := by
  exact transportGL_apply vectorToSpinorPlus g.1 V

theorem trialityCycleAmbient_spinorMinus_apply (g : TrialityGL)
    (S : SpinorPlus8) :
    spinorMinusAct (trialityCycleAmbient g).2.2 (spinorPlusToSpinorMinus S) =
      spinorPlusToSpinorMinus (spinorPlusAct g.2.1 S) := by
  exact transportGL_apply spinorPlusToSpinorMinus g.2.1 S

theorem vectorNorm_spinorMinusToVector_symm (V : Vector8) :
    spinorMinusNorm (spinorMinusToVector.symm V) = vectorNorm V := by
  have h := spinorMinusToVector_norm (spinorMinusToVector.symm V)
  simpa using h.symm

theorem spinorPlusNorm_vectorToSpinorPlus_symm (S : SpinorPlus8) :
    vectorNorm (vectorToSpinorPlus.symm S) = spinorPlusNorm S := by
  have h := vectorToSpinorPlus_norm (vectorToSpinorPlus.symm S)
  simpa using h.symm

theorem spinorMinusNorm_spinorPlusToSpinorMinus_symm (C : SpinorMinus8) :
    spinorPlusNorm (spinorPlusToSpinorMinus.symm C) = spinorMinusNorm C := by
  have h := spinorPlusToSpinorMinus_norm (spinorPlusToSpinorMinus.symm C)
  simpa using h.symm

/-- The ambient cyclic transport preserves the related-triple predicate. -/
theorem trialityCycleAmbient_related {g : TrialityGL}
    (hg : IsRelatedTriple g) : IsRelatedTriple (trialityCycleAmbient g) := by
  rcases hg with ⟨hgv, hgs, hgc, hgf⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V
    calc
      vectorNorm (vectorAct (trialityCycleAmbient g).1 V) =
          vectorNorm (vectorAct (trialityCycleAmbient g).1
            (spinorMinusToVector (spinorMinusToVector.symm V))) := by
              rw [spinorMinusToVector.apply_symm_apply]
      _ = vectorNorm (spinorMinusToVector
            (spinorMinusAct g.2.2 (spinorMinusToVector.symm V))) := by
              rw [trialityCycleAmbient_vector_apply]
      _ = spinorMinusNorm
            (spinorMinusAct g.2.2 (spinorMinusToVector.symm V)) :=
              spinorMinusToVector_norm _
      _ = spinorMinusNorm (spinorMinusToVector.symm V) := hgc _
      _ = vectorNorm V := vectorNorm_spinorMinusToVector_symm V
  · intro S
    calc
      spinorPlusNorm (spinorPlusAct (trialityCycleAmbient g).2.1 S) =
          spinorPlusNorm (spinorPlusAct (trialityCycleAmbient g).2.1
            (vectorToSpinorPlus (vectorToSpinorPlus.symm S))) := by
              rw [vectorToSpinorPlus.apply_symm_apply]
      _ = spinorPlusNorm (vectorToSpinorPlus
            (vectorAct g.1 (vectorToSpinorPlus.symm S))) := by
              rw [trialityCycleAmbient_spinorPlus_apply]
      _ = vectorNorm (vectorAct g.1 (vectorToSpinorPlus.symm S)) :=
              vectorToSpinorPlus_norm _
      _ = vectorNorm (vectorToSpinorPlus.symm S) := hgv _
      _ = spinorPlusNorm S := spinorPlusNorm_vectorToSpinorPlus_symm S
  · intro C
    calc
      spinorMinusNorm (spinorMinusAct (trialityCycleAmbient g).2.2 C) =
          spinorMinusNorm (spinorMinusAct (trialityCycleAmbient g).2.2
            (spinorPlusToSpinorMinus (spinorPlusToSpinorMinus.symm C))) := by
              rw [spinorPlusToSpinorMinus.apply_symm_apply]
      _ = spinorMinusNorm (spinorPlusToSpinorMinus
            (spinorPlusAct g.2.1 (spinorPlusToSpinorMinus.symm C))) := by
              rw [trialityCycleAmbient_spinorMinus_apply]
      _ = spinorPlusNorm
            (spinorPlusAct g.2.1 (spinorPlusToSpinorMinus.symm C)) :=
              spinorPlusToSpinorMinus_norm _
      _ = spinorPlusNorm (spinorPlusToSpinorMinus.symm C) := hgs _
      _ = spinorMinusNorm C :=
              spinorMinusNorm_spinorPlusToSpinorMinus_symm C
  · intro V S C
    let V₀ := vectorToSpinorPlus.symm S
    let S₀ := spinorPlusToSpinorMinus.symm C
    let C₀ := spinorMinusToVector.symm V
    have hV : V = spinorMinusToVector C₀ := by
      exact (spinorMinusToVector.apply_symm_apply V).symm
    have hS : S = vectorToSpinorPlus V₀ := by
      exact (vectorToSpinorPlus.apply_symm_apply S).symm
    have hC : C = spinorPlusToSpinorMinus S₀ := by
      exact (spinorPlusToSpinorMinus.apply_symm_apply C).symm
    rw [hV, hS, hC,
      trialityCycleAmbient_vector_apply,
      trialityCycleAmbient_spinorPlus_apply,
      trialityCycleAmbient_spinorMinus_apply]
    calc
      trialityForm (spinorMinusToVector (spinorMinusAct g.2.2 C₀))
          (vectorToSpinorPlus (vectorAct g.1 V₀))
          (spinorPlusToSpinorMinus (spinorPlusAct g.2.1 S₀)) =
        trialityForm (vectorAct g.1 V₀) (spinorPlusAct g.2.1 S₀)
          (spinorMinusAct g.2.2 C₀) :=
            (trialityForm_cyclic _ _ _).symm
      _ = trialityForm V₀ S₀ C₀ := hgf V₀ S₀ C₀
      _ = trialityForm (spinorMinusToVector C₀)
          (vectorToSpinorPlus V₀) (spinorPlusToSpinorMinus S₀) :=
            trialityForm_cyclic V₀ S₀ C₀

/-- Outer cyclic transport as an endomorphism of the related-triples group. -/
def cartanTrialityCycle : CartanTrialityGroup →* CartanTrialityGroup where
  toFun g := ⟨trialityCycleAmbient g.1, trialityCycleAmbient_related g.2⟩
  map_one' := Subtype.ext (map_one trialityCycleAmbient)
  map_mul' g h := Subtype.ext (map_mul trialityCycleAmbient g.1 h.1)

theorem typed_triality_order_three_spinorPlus (S : SpinorPlus8) :
    vectorToSpinorPlus
      (spinorMinusToVector (spinorPlusToSpinorMinus S)) = S := by
  apply ZornCopy.ext
  exact coordinatesToZorn_zornCoordinates S.val

theorem typed_triality_order_three_spinorMinus (C : SpinorMinus8) :
    spinorPlusToSpinorMinus
      (vectorToSpinorPlus (spinorMinusToVector C)) = C := by
  apply ZornCopy.ext
  exact coordinatesToZorn_zornCoordinates C.val

theorem trialityCycleAmbient_order_three (g : TrialityGL) :
    trialityCycleAmbient
      (trialityCycleAmbient (trialityCycleAmbient g)) = g := by
  apply Prod.ext
  · apply Units.ext
    apply LinearMap.ext
    intro V
    change vectorAct
      (trialityCycleAmbient
        (trialityCycleAmbient (trialityCycleAmbient g))).1 V =
          vectorAct g.1 V
    conv_lhs => rw [← typed_triality_order_three V]
    rw [trialityCycleAmbient_vector_apply,
      trialityCycleAmbient_spinorMinus_apply,
      trialityCycleAmbient_spinorPlus_apply,
      typed_triality_order_three]
  · apply Prod.ext
    · apply Units.ext
      apply LinearMap.ext
      intro S
      change spinorPlusAct
        (trialityCycleAmbient
          (trialityCycleAmbient (trialityCycleAmbient g))).2.1 S =
            spinorPlusAct g.2.1 S
      conv_lhs => rw [← typed_triality_order_three_spinorPlus S]
      rw [trialityCycleAmbient_spinorPlus_apply,
        trialityCycleAmbient_vector_apply,
        trialityCycleAmbient_spinorMinus_apply,
        typed_triality_order_three_spinorPlus]
    · apply Units.ext
      apply LinearMap.ext
      intro C
      change spinorMinusAct
        (trialityCycleAmbient
          (trialityCycleAmbient (trialityCycleAmbient g))).2.2 C =
            spinorMinusAct g.2.2 C
      conv_lhs => rw [← typed_triality_order_three_spinorMinus C]
      rw [trialityCycleAmbient_spinorMinus_apply,
        trialityCycleAmbient_spinorPlus_apply,
        trialityCycleAmbient_vector_apply,
        typed_triality_order_three_spinorMinus]

theorem cartanTrialityCycle_order_three (g : CartanTrialityGroup) :
    cartanTrialityCycle
      (cartanTrialityCycle (cartanTrialityCycle g)) = g := by
  apply Subtype.ext
  exact trialityCycleAmbient_order_three g.1

/-- The outer Cartan triality automorphism of the related-triples group. -/
def cartanTrialityOuterEquiv :
    CartanTrialityGroup ≃* CartanTrialityGroup where
  toFun := cartanTrialityCycle
  invFun g := cartanTrialityCycle (cartanTrialityCycle g)
  left_inv := cartanTrialityCycle_order_three
  right_inv := cartanTrialityCycle_order_three
  map_mul' := map_mul cartanTrialityCycle

theorem cartanTrialityOuterEquiv_order_three (g : CartanTrialityGroup) :
    cartanTrialityOuterEquiv
      (cartanTrialityOuterEquiv (cartanTrialityOuterEquiv g)) = g :=
  cartanTrialityCycle_order_three g

/-! ## The internal Zorn-axis symmetry as a related triple -/

def axisRelatedTripleAmbient : TrialityGL :=
  (LinearMap.GeneralLinearGroup.ofLinearEquiv vectorAxisCycle,
    LinearMap.GeneralLinearGroup.ofLinearEquiv spinorPlusAxisCycle,
    LinearMap.GeneralLinearGroup.ofLinearEquiv spinorMinusAxisCycle)

theorem axisRelatedTriple_vector_apply (V : Vector8) :
    vectorAct axisRelatedTripleAmbient.1 V = vectorAxisCycle V := rfl

theorem axisRelatedTriple_spinorPlus_apply (S : SpinorPlus8) :
    spinorPlusAct axisRelatedTripleAmbient.2.1 S = spinorPlusAxisCycle S := rfl

theorem axisRelatedTriple_spinorMinus_apply (C : SpinorMinus8) :
    spinorMinusAct axisRelatedTripleAmbient.2.2 C = spinorMinusAxisCycle C := rfl

theorem spinorPlusAxisCycle_norm (S : SpinorPlus8) :
    spinorPlusNorm (spinorPlusAxisCycle S) = spinorPlusNorm S := by
  change zornNorm (spinorPlusAxisCycle S).val = zornNorm S.val
  rw [axisCycleCopy_val, canonicalTriality_norm]

theorem spinorMinusAxisCycle_norm (C : SpinorMinus8) :
    spinorMinusNorm (spinorMinusAxisCycle C) = spinorMinusNorm C := by
  change zornNorm (spinorMinusAxisCycle C).val = zornNorm C.val
  rw [axisCycleCopy_val, canonicalTriality_norm]

theorem zornTrace_canonicalTriality
    (X : InfoGeometry.Physics.SplitOctonionBraidSU3.Zorn) :
    zornTrace (canonicalTriality X) = zornTrace X := by
  rfl

theorem trialityForm_axisCycle (V : Vector8) (S : SpinorPlus8)
    (C : SpinorMinus8) :
    trialityForm (vectorAxisCycle V) (spinorPlusAxisCycle S)
      (spinorMinusAxisCycle C) = trialityForm V S C := by
  change zornTrace
      (zornMul
        (zornMul (canonicalTriality V.val) (canonicalTriality S.val))
        (canonicalTriality C.val)) =
    zornTrace (zornMul (zornMul V.val S.val) C.val)
  rw [← canonicalTriality_mul, ← canonicalTriality_mul,
    zornTrace_canonicalTriality]

theorem axisRelatedTriple_isRelated :
    IsRelatedTriple axisRelatedTripleAmbient := by
  exact ⟨vectorAxisCycle_norm, spinorPlusAxisCycle_norm,
    spinorMinusAxisCycle_norm, trialityForm_axisCycle⟩

/-- The internal order-three Zorn-axis automorphism is a concrete point of
the outer related-triples group. -/
def axisRelatedTriple : CartanTrialityGroup :=
  ⟨axisRelatedTripleAmbient, axisRelatedTriple_isRelated⟩

theorem spinorMinusToVector_axisCycle (C : SpinorMinus8) :
    spinorMinusToVector (spinorMinusAxisCycle C) =
      vectorAxisCycle (spinorMinusToVector C) := by
  apply (copyLinearEquivCoordinates TrialitySector.vector).injective
  rfl

theorem vectorToSpinorPlus_axisCycle (V : Vector8) :
    vectorToSpinorPlus (vectorAxisCycle V) =
      spinorPlusAxisCycle (vectorToSpinorPlus V) := by
  apply (copyLinearEquivCoordinates TrialitySector.spinorPlus).injective
  rfl

theorem spinorPlusToSpinorMinus_axisCycle (S : SpinorPlus8) :
    spinorPlusToSpinorMinus (spinorPlusAxisCycle S) =
      spinorMinusAxisCycle (spinorPlusToSpinorMinus S) := by
  apply (copyLinearEquivCoordinates TrialitySector.spinorMinus).injective
  rfl

/-- The internal Zorn-axis symmetry is fixed by the outer permutation because
the same coordinate automorphism acts on all three carriers. -/
theorem cartanTrialityCycle_axisRelatedTriple :
    cartanTrialityCycle axisRelatedTriple = axisRelatedTriple := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply LinearMap.ext
    intro V
    change vectorAct (trialityCycleAmbient axisRelatedTripleAmbient).1 V =
      vectorAct axisRelatedTripleAmbient.1 V
    conv_lhs => rw [← spinorMinusToVector.apply_symm_apply V]
    rw [trialityCycleAmbient_vector_apply,
      axisRelatedTriple_spinorMinus_apply,
      spinorMinusToVector_axisCycle,
      spinorMinusToVector.apply_symm_apply,
      axisRelatedTriple_vector_apply]
  · apply Prod.ext
    · apply Units.ext
      apply LinearMap.ext
      intro S
      change spinorPlusAct (trialityCycleAmbient axisRelatedTripleAmbient).2.1 S =
        spinorPlusAct axisRelatedTripleAmbient.2.1 S
      conv_lhs => rw [← vectorToSpinorPlus.apply_symm_apply S]
      rw [trialityCycleAmbient_spinorPlus_apply,
        axisRelatedTriple_vector_apply, vectorToSpinorPlus_axisCycle,
        vectorToSpinorPlus.apply_symm_apply,
        axisRelatedTriple_spinorPlus_apply]
    · apply Units.ext
      apply LinearMap.ext
      intro C
      change spinorMinusAct (trialityCycleAmbient axisRelatedTripleAmbient).2.2 C =
        spinorMinusAct axisRelatedTripleAmbient.2.2 C
      conv_lhs => rw [← spinorPlusToSpinorMinus.apply_symm_apply C]
      rw [trialityCycleAmbient_spinorMinus_apply,
        axisRelatedTriple_spinorPlus_apply, spinorPlusToSpinorMinus_axisCycle,
        spinorPlusToSpinorMinus.apply_symm_apply,
        axisRelatedTriple_spinorMinus_apply]

/-! ## Five-graded and affine-projective interfaces -/

def relatedVectorGradePlus (g : CartanTrialityGroup) (V : Vector8) :
    ConformalMatrix := vectorGradePlus (vectorAct g.1.1 V)

def relatedSpinorGradePlus (g : CartanTrialityGroup) (S : SpinorPlus8) :
    ConformalMatrix := spinorPlusGradePlus (spinorPlusAct g.1.2.1 S)

def relatedSpinorGradeMinus (g : CartanTrialityGroup) (C : SpinorMinus8) :
    ConformalMatrix := spinorMinusGradeMinus (spinorMinusAct g.1.2.2 C)

theorem relatedVectorGradePlus_mem (g : CartanTrialityGroup) (V : Vector8) :
    relatedVectorGradePlus g V ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 :=
  vectorGradePlus_mem _

theorem relatedSpinorGradePlus_mem (g : CartanTrialityGroup)
    (S : SpinorPlus8) :
    relatedSpinorGradePlus g S ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 :=
  spinorPlusGradePlus_mem _

theorem relatedSpinorGradeMinus_mem (g : CartanTrialityGroup)
    (C : SpinorMinus8) :
    relatedSpinorGradeMinus g C ∈
      conformalGrade TKKJordanPairData.TKKGrade.m1 :=
  spinorMinusGradeMinus_mem _

theorem cartanTrialityCycle_vector_grade (g : CartanTrialityGroup)
    (C : SpinorMinus8) :
    relatedVectorGradePlus (cartanTrialityCycle g) (spinorMinusToVector C) =
      vectorGradePlus
        (spinorMinusToVector (spinorMinusAct g.1.2.2 C)) := by
  apply congrArg vectorGradePlus
  exact trialityCycleAmbient_vector_apply g.1 C

theorem cartanTrialityCycle_spinor_plus_grade (g : CartanTrialityGroup)
    (V : Vector8) :
    relatedSpinorGradePlus (cartanTrialityCycle g) (vectorToSpinorPlus V) =
      spinorPlusGradePlus (vectorToSpinorPlus (vectorAct g.1.1 V)) := by
  apply congrArg spinorPlusGradePlus
  exact trialityCycleAmbient_spinorPlus_apply g.1 V

theorem cartanTrialityCycle_spinor_minus_grade (g : CartanTrialityGroup)
    (S : SpinorPlus8) :
    relatedSpinorGradeMinus (cartanTrialityCycle g)
        (spinorPlusToSpinorMinus S) =
      spinorMinusGradeMinus
        (spinorPlusToSpinorMinus (spinorPlusAct g.1.2.1 S)) := by
  apply congrArg spinorMinusGradeMinus
  exact trialityCycleAmbient_spinorMinus_apply g.1 S

/-- If the vector component of a related triple carries one real Zorn point
to another, the induced real `(4,4)` quadratic value is preserved. -/
theorem relatedTriple_realQuadratic_preserved
    (g : CartanTrialityGroup) (x y : RealSplit44)
    (hxy : vectorAct g.1.1 (realSplit44ToVector8 x) =
      realSplit44ToVector8 y) :
    realQuadratic44 y = realQuadratic44 x := by
  have hnorm := g.2.1 (realSplit44ToVector8 x)
  rw [hxy] at hnorm
  have hq : (realQuadratic44 y : ℂ) = (realQuadratic44 x : ℂ) := by
    rw [← vectorQuadratic_realSplit44ToVector8,
      ← vectorQuadratic_realSplit44ToVector8,
      vectorQuadratic_apply, vectorQuadratic_apply]
    exact hnorm
  exact Complex.ofReal_injective hq

/-- A real-compatible related-triple action preserves the affine conformal
projective null lift and remains in the concrete grade `+1` block. -/
theorem relatedTriple_affine_projective_five_grade
    (g : CartanTrialityGroup) (x y : RealSplit44)
    (hxy : vectorAct g.1.1 (realSplit44ToVector8 x) =
      realSplit44ToVector8 y) :
    realQuadratic44 y = realQuadratic44 x ∧
    Q55 (conformalEmbed44to55 (realSplit44ToPAC44 y)) = 0 ∧
    relatedVectorGradePlus g (realSplit44ToVector8 x) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 := by
  exact ⟨relatedTriple_realQuadratic_preserved g x y hxy,
    realSplit44_projective_null y, relatedVectorGradePlus_mem g _⟩

/-- Capstone: outer Cartan triality, its order-three law, the three five-grade
lanes, and the affine projective closure are connected without assuming that
arbitrary complex related triples preserve the real locus. -/
theorem outer_triality_five_grade_projective_closure
    (g : CartanTrialityGroup) (x y : RealSplit44)
    (hxy : vectorAct g.1.1 (realSplit44ToVector8 x) =
      realSplit44ToVector8 y) (S : SpinorPlus8) (C : SpinorMinus8) :
    cartanTrialityOuterEquiv
        (cartanTrialityOuterEquiv (cartanTrialityOuterEquiv g)) = g ∧
    relatedVectorGradePlus g (realSplit44ToVector8 x) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradePlus g S ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradeMinus g C ∈
      conformalGrade TKKJordanPairData.TKKGrade.m1 ∧
    realQuadratic44 y = realQuadratic44 x ∧
    Q55 (conformalEmbed44to55 (realSplit44ToPAC44 y)) = 0 := by
  exact ⟨cartanTrialityOuterEquiv_order_three g,
    relatedVectorGradePlus_mem g _, relatedSpinorGradePlus_mem g S,
    relatedSpinorGradeMinus_mem g C,
    relatedTriple_realQuadratic_preserved g x y hxy,
    realSplit44_projective_null y⟩

end CanonicalZornOuterTrialityGroup

end noncomputable section
