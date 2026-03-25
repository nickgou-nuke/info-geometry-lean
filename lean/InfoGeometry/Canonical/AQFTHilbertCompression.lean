import InfoGeometry.Canonical.AQFTOperatorSignatures
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# InfoGeometry.Canonical.AQFTHilbertCompression

Concrete real and complex Hilbert compression realizations for the AQFT operator interface.
-/

namespace InfoGeometry.Canonical.AQFTOperatorInterface

open InfoGeometry.Krein
open InfoGeometry.Canonical.KMSSinkhornBridge

section ConcreteHilbertModels

/-! ### Real Hilbert model (instantiates the AQFT interface directly) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Real Hilbert bounded-operator algebra (adjoint/star model). -/
abbrev RealHilbertObs
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  E →L[ℝ] E

/-- First-leg embedding `x ↦ (x,0)` into doubled space. -/
def firstLegEmbedding : E →L[ℝ] InfoGeometry.Krein.DoubledSpace E where
  toLinearMap :=
    { toFun := fun x => InfoGeometry.Krein.to_doubled x (0 : E)
      map_add' := by
        intro x y
        apply (WithLp.ofLp_injective 2)
        simp [InfoGeometry.Krein.to_doubled]
      map_smul' := by
        intro a x
        apply (WithLp.ofLp_injective 2)
        simp [InfoGeometry.Krein.to_doubled, smul_zero] }
  cont := by
    simpa [InfoGeometry.Krein.to_doubled] using
      (WithLp.prod_continuous_toLp (p := 2) (α := E) (β := E)).comp
        (continuous_id.prodMk (continuous_const (y := (0 : E))))

/-- First-leg projection `(x,y) ↦ x` from doubled space. -/
def firstLegProjection : InfoGeometry.Krein.DoubledSpace E →L[ℝ] E where
  toLinearMap :=
    { toFun := fun v => WithLp.fst v
      map_add' := by
        intro v w
        simp [WithLp.add_fst]
      map_smul' := by
        intro a v
        simp [WithLp.smul_fst] }
  cont := by
    simpa using
      WithLp.continuous_fst (p := 2) (α := E) (β := E)

/-- Compression of doubled operators onto the first Hilbert leg. -/
def firstLegCompression (A : AlgebraEnd E) : RealHilbertObs E :=
  (firstLegProjection (E := E)).comp (A.comp (firstLegEmbedding (E := E)))

/-- Concrete interpretation into real Hilbert bounded operators via first-leg compression. -/
def realHilbertCompressionInterpretation :
    AQFTOperatorInterpretation E (RealHilbertObs E) where
  interpret := firstLegCompression (E := E)

/-! ### Complex Hilbert model (adjoint/star bounded operators) -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Complex doubled operator source type (complex-linear counterpart). -/
abbrev ComplexHilbertOp
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  InfoGeometry.Krein.DoubledSpace H →L[ℂ] InfoGeometry.Krein.DoubledSpace H

/-- Complex Hilbert bounded-operator algebra (adjoint/star model). -/
abbrev ComplexHilbertObs
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  H →L[ℂ] H

/-- Complex first-leg embedding `x ↦ (x,0)` into doubled space. -/
def complexFirstLegEmbedding : H →L[ℂ] InfoGeometry.Krein.DoubledSpace H where
  toLinearMap :=
    { toFun := fun x => InfoGeometry.Krein.to_doubled x (0 : H)
      map_add' := by
        intro x y
        apply (WithLp.ofLp_injective 2)
        simp [InfoGeometry.Krein.to_doubled]
      map_smul' := by
        intro a x
        apply (WithLp.ofLp_injective 2)
        simp [InfoGeometry.Krein.to_doubled, smul_zero] }
  cont := by
    simpa [InfoGeometry.Krein.to_doubled] using
      (WithLp.prod_continuous_toLp (p := 2) (α := H) (β := H)).comp
        (continuous_id.prodMk (continuous_const (y := (0 : H))))

/-- Complex first-leg projection `(x,y) ↦ x` from doubled space. -/
def complexFirstLegProjection : InfoGeometry.Krein.DoubledSpace H →L[ℂ] H where
  toLinearMap :=
    { toFun := fun v => WithLp.fst v
      map_add' := by
        intro v w
        simp [WithLp.add_fst]
      map_smul' := by
        intro a v
        simp [WithLp.smul_fst] }
  cont := by
    simpa using
      WithLp.continuous_fst (p := 2) (α := H) (β := H)

/-- Complex compression of doubled operators onto the first Hilbert leg. -/
def complexFirstLegCompression (A : ComplexHilbertOp H) : ComplexHilbertObs H :=
  (complexFirstLegProjection (H := H)).comp (A.comp (complexFirstLegEmbedding (H := H)))

/-- Complex-operator interpretation wrapper (complex-source counterpart). -/
structure ComplexAQFTOperatorInterpretation
    (H : Type*) (Obs : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NonUnitalNormedRing Obs] [StarRing Obs] where
  interpret : ComplexHilbertOp H → Obs

/-- Complex interpretation into Hilbert bounded operators via first-leg compression. -/
def complexHilbertCompressionInterpretation :
    ComplexAQFTOperatorInterpretation H (ComplexHilbertObs H) where
  interpret := complexFirstLegCompression (H := H)

end ConcreteHilbertModels

end InfoGeometry.Canonical.AQFTOperatorInterface
