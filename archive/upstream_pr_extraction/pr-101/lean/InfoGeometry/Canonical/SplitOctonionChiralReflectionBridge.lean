import InfoGeometry.Canonical.SplitOctonionColorS3Automorphisms
import InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations

namespace InfoGeometry.Canonical

open SplitOctonionColour

noncomputable section

def colourReflectionColour : SplitOctonionColour → SplitOctonionColour
  | .red => .green
  | .green => .red
  | .blue => .blue

def colourReflectionSign : SplitOctonionColour → ℚ
  | .blue => -1
  | _ => 1

theorem colourReflectionColour_involutive (c : SplitOctonionColour) :
    colourReflectionColour (colourReflectionColour c) = c := by
  cases c <;> rfl

theorem colorReflection_rationalBasis (b : IntegralSplitBasis) :
    colorReflection (rationalBasis b) =
      colorReflectionSign b • rationalBasis (colorReflectionBasis b) := by
  ext d
  cases b <;> cases d <;>
    simp [colorReflection, colorReflectionBasisEquiv,
      colorReflectionBasis, colorReflectionSign, rationalBasis]

theorem colorReflection_colourUnit (c : SplitOctonionColour) :
    colorReflection (colourUnit c) =
      colourReflectionSign c • colourUnit (colourReflectionColour c) := by
  cases c
  · simpa [colourUnit, colourReflectionColour, colourReflectionSign,
      colorReflectionBasis, colorReflectionSign] using
      colorReflection_rationalBasis IntegralSplitBasis.i
  · simpa [colourUnit, colourReflectionColour, colourReflectionSign,
      colorReflectionBasis, colorReflectionSign] using
      colorReflection_rationalBasis IntegralSplitBasis.j
  · simpa [colourUnit, colourReflectionColour, colourReflectionSign,
      colorReflectionBasis, colorReflectionSign] using
      colorReflection_rationalBasis IntegralSplitBasis.k

theorem colorReflection_colourLUnit (c : SplitOctonionColour) :
    colorReflection (colourLUnit c) =
      colourReflectionSign c • colourLUnit (colourReflectionColour c) := by
  cases c
  · simpa [colourLUnit, colourReflectionColour, colourReflectionSign,
      colorReflectionBasis, colorReflectionSign] using
      colorReflection_rationalBasis IntegralSplitBasis.il
  · simpa [colourLUnit, colourReflectionColour, colourReflectionSign,
      colorReflectionBasis, colorReflectionSign] using
      colorReflection_rationalBasis IntegralSplitBasis.jl
  · simpa [colourLUnit, colourReflectionColour, colourReflectionSign,
      colorReflectionBasis, colorReflectionSign] using
      colorReflection_rationalBasis IntegralSplitBasis.kl

theorem colorReflection_one :
    colorReflection (rationalBasis .one) = rationalBasis .one := by
  simpa [colorReflectionBasis, colorReflectionSign] using
    colorReflection_rationalBasis IntegralSplitBasis.one

theorem colorReflection_fundamentalSymmetry :
    colorReflection fundamentalSymmetry = fundamentalSymmetry := by
  simpa [fundamentalSymmetry, colorReflectionBasis, colorReflectionSign] using
    colorReflection_rationalBasis IntegralSplitBasis.l

theorem colorReflection_modularNPlus :
    colorReflection modularNPlus = modularNPlus := by
  simp [modularNPlus, colorReflection_one,
    colorReflection_fundamentalSymmetry]

theorem colorReflection_modularNMinus :
    colorReflection modularNMinus = modularNMinus := by
  simp [modularNMinus, colorReflection_one,
    colorReflection_fundamentalSymmetry]

theorem colorReflection_modularSigmaPlus (c : SplitOctonionColour) :
    colorReflection (modularSigmaPlus c) =
      colourReflectionSign c • modularSigmaPlus (colourReflectionColour c) := by
  have hJ : colorReflection (modularJ c) =
      colourReflectionSign c • modularJ (colourReflectionColour c) := by
    rw [modularJ_eq_colourLUnit, modularJ_eq_colourLUnit,
      colorReflection_colourLUnit]
  simp only [modularSigmaPlus, phaseAxis, map_smul, map_sub, hJ,
    colorReflection_colourUnit]
  module

theorem colorReflection_modularSigmaMinus (c : SplitOctonionColour) :
    colorReflection (modularSigmaMinus c) =
      colourReflectionSign c • modularSigmaMinus (colourReflectionColour c) := by
  have hJ : colorReflection (modularJ c) =
      colourReflectionSign c • modularJ (colourReflectionColour c) := by
    rw [modularJ_eq_colourLUnit, modularJ_eq_colourLUnit,
      colorReflection_colourLUnit]
  simp only [modularSigmaMinus, phaseAxis, map_smul, map_add, hJ,
    colorReflection_colourUnit]
  module

theorem colorReflection_chiralZornBasis (c : SplitOctonionColour) :
    colorReflection (modularSigmaPlus c) =
        colourReflectionSign c • modularSigmaPlus (colourReflectionColour c) ∧
      colorReflection (modularSigmaMinus c) =
        colourReflectionSign c • modularSigmaMinus (colourReflectionColour c) := by
  exact ⟨colorReflection_modularSigmaPlus c,
    colorReflection_modularSigmaMinus c⟩

end
end InfoGeometry.Canonical
