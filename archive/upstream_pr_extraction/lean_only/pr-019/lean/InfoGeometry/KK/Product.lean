import InfoGeometry.KK.KasparovCycle

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Krein

/--
Interface target for the Kasparov product in the bounded layer.
This packages the output cycle while deferring concrete tensor-product analysis.
-/
structure KasparovProductData
    (A B C H₁ H₂ P : Type*)
    [NormedRing A] [NormedRing B] [NormedRing C]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B] [NormedAlgebra ℝ C]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    [KreinSpace H₁] [KreinGradedModule H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    [KreinSpace H₂] [KreinGradedModule H₂]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
    [KreinSpace P] [KreinGradedModule P]
    (X : KasparovCycle A B H₁)
    (Y : KasparovCycle B C H₂) where
  /-- Candidate product cycle `(X ⊗_B Y)` in interface form. -/
  out : KasparovCycle A C P

end InfoGeometry.KK

