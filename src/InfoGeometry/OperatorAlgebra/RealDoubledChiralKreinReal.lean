import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Real structures on the doubled chiral Krein carrier

This is the honest real shadow of a Real/anti-linear structure.  The carrier in
this lane is over `ℝ`, so anti-linearity is not asserted here.  Instead we
record an involutive Hilbert isometry which commutes with the cross-sheet
fundamental symmetry.  Such a map preserves the chiral Krein form and is the
data that can later be transported to a complexification.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinReal

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev ChiralEnd := DoubledSpace E →L[ℝ] DoubledSpace E

/-- Real involutive structure compatible with the chiral Krein metric.

On a real carrier this is the precise finite substitute for the linear part
of a complex anti-linear Real structure.  Complex conjugation itself belongs
to a later complexification layer.
-/
structure ChiralRealStructure where
  map : ChiralEnd (E := E)
  map_involutive : map.comp map = ContinuousLinearMap.id ℝ (DoubledSpace E)
  map_hilbert_isometry : ∀ u v,
    inner ℝ (map u) (map v) = inner ℝ u v
  commutes_with_eta :
    map.comp (etaChiral (E := E)) =
      (etaChiral (E := E)).comp map

namespace ChiralRealStructure

@[simp] theorem map_involutive_apply (C : ChiralRealStructure (E := E))
    (u : DoubledSpace E) : C.map (C.map u) = u := by
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun T : ChiralEnd (E := E) => T u) C.map_involutive

theorem preserves_chiralKreinForm (C : ChiralRealStructure (E := E))
    (u v : DoubledSpace E) :
    chiralKreinForm (C.map u) (C.map v) = chiralKreinForm u v := by
  rw [chiralKreinForm_eq_inner_eta, chiralKreinForm_eq_inner_eta]
  have hcomm (w : DoubledSpace E) :
      C.map (etaChiral w) = etaChiral (C.map w) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : ChiralEnd (E := E) => T w) C.commutes_with_eta
  rw [← hcomm]
  exact C.map_hilbert_isometry _ _

end ChiralRealStructure

/-- The cross-sheet fundamental symmetry is itself a compatible Real shadow. -/
noncomputable def etaChiralRealStructure : ChiralRealStructure (E := E) where
  map := etaChiral (E := E)
  map_involutive := etaChiral_involution (E := E)
  map_hilbert_isometry := etaChiral_hilbert_isometry (E := E)
  commutes_with_eta := by
    exact etaChiral_involution (E := E) |>.symm

@[simp] theorem etaChiralRealStructure_map :
    (etaChiralRealStructure (E := E)).map = etaChiral (E := E) := rfl

/-- The identity gives the neutral compatible Real structure. -/
noncomputable def identityRealStructure : ChiralRealStructure (E := E) where
  map := ContinuousLinearMap.id ℝ (DoubledSpace E)
  map_involutive := by simp
  map_hilbert_isometry := by simp
  commutes_with_eta := by simp

@[simp] theorem identityRealStructure_map :
    (identityRealStructure (E := E)).map =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := rfl

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinReal
