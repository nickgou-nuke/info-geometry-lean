import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.SplitOctonionImaginaryAction

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Lie.SplitOctonionImaginaryAction

noncomputable section

abbrev SplitOctonionAut :=
  InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut

/-- The split-octonion automorphism transported to the canonical seven-coordinate
model of the imaginary carrier. -/
noncomputable def imaginaryAutCoords
    (φ : SplitOctonionAut) : ImaginaryCoords ≃ₗ[ℝ] ImaginaryCoords :=
  imaginaryCoordLinearEquiv.symm.trans
    ((imaginaryAut φ).trans imaginaryCoordLinearEquiv)

/-- The transported automorphism is a genuine homeomorphism on the finite
dimensional coordinate carrier. -/
noncomputable def imaginaryAutCoordsHomeomorph
    (φ : SplitOctonionAut) : ImaginaryCoords ≃ₜ ImaginaryCoords :=
  (imaginaryAutCoords φ).toContinuousLinearEquiv.toHomeomorph

@[simp] theorem imaginaryAutCoordsHomeomorph_apply
    (φ : SplitOctonionAut) (x : ImaginaryCoords) :
    imaginaryAutCoordsHomeomorph φ x = imaginaryAutCoords φ x :=
  rfl

theorem continuous_imaginaryAutCoordsHomeomorph
    (φ : SplitOctonionAut) :
    Continuous (imaginaryAutCoordsHomeomorph φ) :=
  (imaginaryAutCoords φ).toContinuousLinearEquiv.continuous

/-- The null/norm-level readout transported to the coordinate carrier. -/
def imaginaryCoordsNormLevel (c : ℝ) : Set ImaginaryCoords :=
  {x | imaginaryCoordLinearEquiv.symm x ∈ NormLevel c}

@[simp] theorem imaginaryAutCoords_mem_normLevel_iff
    (φ : SplitOctonionAut) (c : ℝ) (x : ImaginaryCoords) :
    imaginaryAutCoords φ x ∈ imaginaryCoordsNormLevel c ↔
      x ∈ imaginaryCoordsNormLevel c := by
  simpa only [imaginaryCoordsNormLevel, imaginaryAutCoords,
    Set.mem_setOf_eq, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] using
    imaginaryAut_mem_normLevel_iff φ c (imaginaryCoordLinearEquiv.symm x)

@[simp] theorem imaginaryAutCoords_preserves_null
    (φ : SplitOctonionAut) (x : ImaginaryCoords) :
    imaginaryAutCoords φ x ∈ imaginaryCoordsNormLevel 0 ↔
      x ∈ imaginaryCoordsNormLevel 0 :=
  imaginaryAutCoords_mem_normLevel_iff φ 0 x

end

end InfoGeometry.Topology.SplitOctonionImaginaryAction
