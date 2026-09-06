import InfoGeometry.Canonical.RealDoubledKreinMirrorTopologicalDirectSum

/-!
# Continuous direct-sum equivalence for the real mirror splitting

The two complementary continuous mirror submodules are assembled into an
actual finite-dimensional `ContinuousLinearEquiv`.  This remains a statement
about the bounded operator space and its real topological decomposition.
-/

namespace InfoGeometry.Canonical.DoubledHestenesKreinData

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable (K : DoubledHestenesKreinData V)

theorem mirrorProjectionToProduct_fromProduct
    (p : mirrorEvenSubmodule K × mirrorOddSubmodule K) :
    mirrorProjectionToProduct K (mirrorProjectionFromProduct K p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    change mirrorEvenPart K
        ((p.1 : ContinuousOperator V) + (p.2 : ContinuousOperator V)) =
      (p.1 : ContinuousOperator V)
    have hEven : mirrorConjugateContinuous K
        (p.1 : ContinuousOperator V) = (p.1 : ContinuousOperator V) :=
      (mem_mirrorEvenSubmodule_iff K (p.1 : ContinuousOperator V)).1
        p.1.property
    have hOdd : mirrorConjugateContinuous K
        (p.2 : ContinuousOperator V) = -(p.2 : ContinuousOperator V) :=
      (mem_mirrorOddSubmodule_iff K (p.2 : ContinuousOperator V)).1
        p.2.property
    unfold mirrorEvenPart
    change (1 / 2 : ℝ) •
      ((p.1 : ContinuousOperator V) + (p.2 : ContinuousOperator V) +
        mirrorConjugateContinuousLinear K
          ((p.1 : ContinuousOperator V) + (p.2 : ContinuousOperator V))) =
      (p.1 : ContinuousOperator V)
    have hEven' : mirrorConjugateContinuousLinear K
        (p.1 : ContinuousOperator V) = (p.1 : ContinuousOperator V) := by
      simpa [mirrorConjugateContinuousLinear_apply] using hEven
    have hOdd' : mirrorConjugateContinuousLinear K
        (p.2 : ContinuousOperator V) = -(p.2 : ContinuousOperator V) := by
      simpa [mirrorConjugateContinuousLinear_apply] using hOdd
    rw [map_add, hEven', hOdd']
    module
  · apply Subtype.ext
    change mirrorOddPart K
        ((p.1 : ContinuousOperator V) + (p.2 : ContinuousOperator V)) =
      (p.2 : ContinuousOperator V)
    have hEven : mirrorConjugateContinuous K
        (p.1 : ContinuousOperator V) = (p.1 : ContinuousOperator V) :=
      (mem_mirrorEvenSubmodule_iff K (p.1 : ContinuousOperator V)).1
        p.1.property
    have hOdd : mirrorConjugateContinuous K
        (p.2 : ContinuousOperator V) = -(p.2 : ContinuousOperator V) :=
      (mem_mirrorOddSubmodule_iff K (p.2 : ContinuousOperator V)).1
        p.2.property
    unfold mirrorOddPart
    change (1 / 2 : ℝ) •
      ((p.1 : ContinuousOperator V) + (p.2 : ContinuousOperator V) -
        mirrorConjugateContinuousLinear K
          ((p.1 : ContinuousOperator V) + (p.2 : ContinuousOperator V))) =
      (p.2 : ContinuousOperator V)
    have hEven' : mirrorConjugateContinuousLinear K
        (p.1 : ContinuousOperator V) = (p.1 : ContinuousOperator V) := by
      simpa [mirrorConjugateContinuousLinear_apply] using hEven
    have hOdd' : mirrorConjugateContinuousLinear K
        (p.2 : ContinuousOperator V) = -(p.2 : ContinuousOperator V) := by
      simpa [mirrorConjugateContinuousLinear_apply] using hOdd
    rw [map_add, hEven', hOdd']
    module

noncomputable def mirrorProjectionLinearEquiv :
    ContinuousOperator V ≃ₗ[ℝ]
      (mirrorEvenSubmodule K × mirrorOddSubmodule K) :=
  { toFun := mirrorProjectionToProduct K
    invFun := mirrorProjectionFromProduct K
    left_inv := mirrorProjectionFromProduct_toProduct K
    right_inv := mirrorProjectionToProduct_fromProduct K
    map_add' := fun x y => by
      exact map_add (mirrorProjectionToProduct K) x y
    map_smul' := fun a x => by
      exact map_smul (mirrorProjectionToProduct K) a x }

noncomputable def mirrorProjectionContinuousLinearEquiv :
    ContinuousOperator V ≃L[ℝ]
      (mirrorEvenSubmodule K × mirrorOddSubmodule K) :=
  (mirrorProjectionLinearEquiv K).toContinuousLinearEquiv

@[simp] theorem mirrorProjectionContinuousLinearEquiv_apply
    (T : ContinuousOperator V) :
    mirrorProjectionContinuousLinearEquiv K T =
      mirrorProjectionToProduct K T := rfl

end
end InfoGeometry.Canonical.DoubledHestenesKreinData
