import InfoGeometry.Projective.PuncturedAffineLogDeRhamBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.KleinQuadricLogCharacter

/-!
# Logarithmic H¹ lattice to the unit-circle winding character

This owner connects the already-proved integer lattice in punctured-affine
logarithmic cohomology directly to the existing unit-circle winding character.
It introduces neither a universal-cover carrier nor a second cohomology
quotient.
-/

noncomputable section

namespace InfoGeometry.Projective.PuncturedAffineWindingCharacterBridge

open InfoGeometry.Projective.PuncturedAffineLogDeRhamBridge
open InfoGeometry.Projective.KleinQuadric.LogDeRhamClass

/-- The cohomological winding lattice has exactly its integer as complex
logarithmic readout. -/
@[simp] theorem puncturedAffineWindingAddHom_readout (n : ℤ) :
    puncturedAffineH1EquivComplex (puncturedAffineWindingAddHom n) =
      (n : ℂ) := by
  exact puncturedAffineH1EquivComplex_windingClass n

/-- The complex value of the unit-circle character factors through the
concrete logarithmic H¹ lattice embedding and its canonical complex readout. -/
theorem windingCharacterCircleHom_factors_through_puncturedAffineH1
    (α : ℝ) (n : ℤ) :
    (((windingCharacterCircleHom α (Multiplicative.ofAdd n) :
        unitCircleUnits) : ℂˣ) : ℂ) =
      Complex.exp
        ((α : ℂ) *
          puncturedAffineH1EquivComplex (puncturedAffineWindingAddHom n) *
            (2 * Real.pi * Complex.I)) := by
  rw [windingCharacterCircleHom_val,
    puncturedAffineWindingAddHom_readout]
  rfl

/-- Pullback by Laurent inversion reverses the embedded winding lattice. -/
theorem algebraicDeRhamH1Pullback_windingAddHom (n : ℤ) :
    algebraicDeRhamH1Pullback (puncturedAffineWindingAddHom n) =
      puncturedAffineWindingAddHom (-n) := by
  exact algebraicDeRhamH1Pullback_windingClass n

/-- Under the same inversion, the factored unit-circle character is inverted. -/
theorem windingCharacterCircleHom_pullback_inversion
    (α : ℝ) (n : ℤ) :
    windingCharacterCircleHom α (Multiplicative.ofAdd (-n)) =
      (windingCharacterCircleHom α (Multiplicative.ofAdd n))⁻¹ := by
  exact windingCharacterCircleHom_neg α n

end InfoGeometry.Projective.PuncturedAffineWindingCharacterBridge
