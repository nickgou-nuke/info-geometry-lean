import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinReal
import InfoGeometry.Krein.KreinSpace

/-!
# Native Mathlib Krein bridge for the doubled chiral carrier

The earlier chiral owner uses an explicit cross-sheet bilinear form.  This
file packages the same swap as Mathlib's `LinearIsometryEquiv` and supplies a
local `KreinSpace` datum.  Consequently the standard native definitions
`KreinSpace.kreinAdjoint`, `IsKreinSelfAdjoint`, and `IsKreinIsometry` can be
used without changing the repository's canonical diagonal Krein instance.

The instance is deliberately a value rather than a global typeclass instance:
`DoubledSpace E` already has the canonical diagonal Krein instance, and the
cross-sheet form is a distinct polarization of the same Hilbert carrier.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinNative

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinReal

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev Carrier := DoubledSpace E
abbrev End := Carrier (E := E) →L[ℝ] Carrier (E := E)

/-- The cross-sheet swap as a linear map. -/
noncomputable def chiralSwapMap : Carrier (E := E) →ₗ[ℝ] Carrier (E := E) :=
  (etaChiral (E := E)).toLinearMap

private lemma chiralSwapMap_invol (u : Carrier (E := E)) :
    chiralSwapMap (E := E) (chiralSwapMap (E := E) u) = u := by
  simpa [chiralSwapMap, etaChiral, ContinuousLinearMap.comp_apply] using
    congrArg (fun T : End (E := E) => T u)
      (etaChiral_involution (E := E))

private lemma chiralSwapMap_norm (u : Carrier (E := E)) :
    ‖chiralSwapMap (E := E) u‖ = ‖u‖ := by
  have hsq : ‖chiralSwapMap (E := E) u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact etaChiral_hilbert_isometry (E := E) u u
  nlinarith [norm_nonneg (chiralSwapMap (E := E) u), norm_nonneg u]

/-- The cross-sheet swap as a native `LinearIsometryEquiv`. -/
noncomputable def chiralSwapLIE : Carrier (E := E) ≃ₗᵢ[ℝ] Carrier (E := E) where
  toLinearEquiv := LinearEquiv.ofLinear
    (chiralSwapMap (E := E)) (chiralSwapMap (E := E))
    (LinearMap.ext chiralSwapMap_invol)
    (LinearMap.ext chiralSwapMap_invol)
  norm_map' := chiralSwapMap_norm (E := E)

@[simp] theorem chiralSwapLIE_apply (u : Carrier (E := E)) :
    chiralSwapLIE (E := E) u = etaChiral (E := E) u := rfl

/-- The native `KreinSpace` value for the cross-sheet polarization. -/
noncomputable def chiralKreinSpace : KreinSpace (Carrier (E := E)) where
  J := chiralSwapLIE (E := E)
  J_invol := by
    intro u
    exact chiralSwapMap_invol (E := E) u
  J_selfAdj := by
    intro u v
    simpa [chiralSwapLIE_apply] using
      etaChiral_hilbert_selfAdjoint (E := E) u v

theorem chiralKreinSpace_kreinInner (u v : Carrier (E := E)) :
    @KreinSpace.kreinInner (Carrier (E := E)) _ _ _
      (chiralKreinSpace (E := E)) u v =
      chiralKreinForm (E := E) u v := by
  change inner ℝ (chiralSwapLIE (E := E) u) v =
    chiralKreinForm (E := E) u v
  rw [chiralSwapLIE_apply, chiralKreinForm_eq_inner_eta]

theorem chiralKreinSpace_kreinAdjoint (A : End (E := E)) :
    @KreinSpace.kreinAdjoint (Carrier (E := E)) _ _ _
      (chiralKreinSpace (E := E)) A =
      chiralKreinAdjoint (E := E) A := by
  apply ContinuousLinearMap.ext
  intro u
  simp [KreinSpace.kreinAdjoint, KreinSpace.jCLM,
    chiralKreinSpace, chiralSwapLIE, chiralSwapMap,
    chiralKreinAdjoint, ContinuousLinearMap.comp_apply]

/-- Native J-Hermiticity for the cross-sheet polarization. -/
def IsNativeJHermitian (A : End (E := E)) : Prop :=
  @KreinSpace.IsKreinSelfAdjoint (Carrier (E := E)) _ _ _
    (chiralKreinSpace (E := E)) A

/-- Native J-unitarity for the cross-sheet polarization. -/
def IsNativeJUnitary (A : End (E := E)) : Prop :=
  @KreinSpace.IsKreinIsometry (Carrier (E := E)) _ _ _
    (chiralKreinSpace (E := E)) A

theorem nativeJHermitian_iff_chiral (A : End (E := E)) :
    IsNativeJHermitian (E := E) A ↔
      IsChiralKreinSelfAdjoint (E := E) A := by
  change
    @KreinSpace.kreinAdjoint (Carrier (E := E)) _ _ _
        (chiralKreinSpace (E := E)) A = A ↔
      chiralKreinAdjoint (E := E) A = A
  rw [chiralKreinSpace_kreinAdjoint (E := E) A]

theorem nativeJUnitary_iff_chiral (A : End (E := E)) :
    IsNativeJUnitary (E := E) A ↔
      IsChiralKreinUnitary (E := E) A := by
  constructor
  · intro h u v
    simpa only [chiralKreinSpace_kreinInner (E := E)] using h u v
  · intro h u v
    simpa only [chiralKreinSpace_kreinInner (E := E)] using h u v

theorem chiralSwap_nativeJHermitian :
    IsNativeJHermitian (E := E) (etaChiral (E := E)) := by
  rw [nativeJHermitian_iff_chiral]
  exact (isChiralKreinSelfAdjoint_iff_form (E := E)
    (etaChiral (E := E))).mpr
    (etaChiral_isChiralKreinHermitian (E := E))

theorem chiralSwap_nativeJUnitary :
    IsNativeJUnitary (E := E) (etaChiral (E := E)) := by
  rw [nativeJUnitary_iff_chiral]
  exact etaChiral_isChiralKreinUnitary (E := E)

/-! ## Real-structure bridge -/

theorem realStructure_map_nativeJUnitary
    (C : ChiralRealStructure (E := E)) :
    IsNativeJUnitary (E := E) C.map := by
  rw [nativeJUnitary_iff_chiral]
  exact C.preserves_chiralKreinForm

theorem etaChiralRealStructure_nativeJUnitary :
    IsNativeJUnitary (E := E)
      (etaChiralRealStructure (E := E)).map := by
  exact realStructure_map_nativeJUnitary (E := E)
    (etaChiralRealStructure (E := E))

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinNative
