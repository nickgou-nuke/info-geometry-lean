import InfoGeometry.Canonical.AQFTOperatorSignatures
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Krein.DoubledSpace

/-!
# InfoGeometry.Canonical.AQFTHilbertCompression

Concrete real Hilbert compression realizations for the AQFT operator interface.

This module formalizes the translation from abstract complex-algebra notions 
to the repo-native doubled real Krein carrier. The "complex" model is 
represented as the real endomorphisms of the doubled space commuting with 
the canonical complex structure `Jε`.
-/

namespace InfoGeometry.Canonical.AQFTOperatorInterface

open InfoGeometry.Krein
open InfoGeometry.Canonical.KMSSinkhornBridge

section ConcreteHilbertModels

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Doubled Real Hilbert model (The Repo-Native Carrier) -/

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

/-! 
### Real-Doubled "Complex" model 

The "Complex" Hilbert space is represented as the doubled real space 
carrying the complex structure `I = J ∘ ε`.
-/

/-- 
A real operator is "Complex-linear" if it commutes with the canonical 
complex structure `complex_i`.
-/
def IsComplexLinear (A : AlgebraEnd E) : Prop :=
  Commute A (complex_i (E := E))

/-- 
The subalgebra of complex-linear operators within the real doubled carrier.
This is the formal translation of B(H_ℂ) into B(H_ℝ ⊕ H_ℝ).
-/
def DoubledComplexAlgebra (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  { A : AlgebraEnd E // IsComplexLinear A }

end ConcreteHilbertModels

end InfoGeometry.Canonical.AQFTOperatorInterface
