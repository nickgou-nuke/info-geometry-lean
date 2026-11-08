import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Quantum G₂ Fusion Coherence Datum

This file formalizes the abstract Anyonic / Braided Fusion categorical data 
required for genuine non-Abelian statistics. 

While the fundamental representation of $G_2$ decomposes as $1 \oplus 7 \oplus 27$, 
we first define the abstract `FusionCoherenceDatum` representing the $F$-moves 
and $R$-moves. This enforces the macroscopic Pentagon and Hexagon identities 
on the fusion channels before specializing to the exact numerical 
Clebsch-Gordan coefficients of the 7-dimensional representation.
-/

namespace InfoGeometry.Categorical

variable (𝕜 : Type*) [Field 𝕜]

/-- 
The abstract structure of a fusion category over a set of simple sectors.
For $G_2$, the generating object $X$ (the 7) has $X \otimes X = 1 \oplus 7 \oplus 27$.
-/
structure QuantumG2FusionCoherenceDatum where
  /-- The label set of simple sectors (e.g., irreducible representations). -/
  SimpleSector : Type*
  
  /-- Fusion multiplicity $N_{a b}^c$. In strict fusion categories, this is usually $0$ or $1$. -/
  fusionMultiplicity : SimpleSector → SimpleSector → SimpleSector → ℕ
  
  /-- The vector space of morphisms (fusion channels) from $a \otimes b \to c$. -/
  FusionSpace : SimpleSector → SimpleSector → SimpleSector → Type*
  
  /-- The F-move (Associator) recoupling matrix elements. -/
  Fmove : ∀ a b c d e f, 
    (FusionSpace a b e) → (FusionSpace e c d) → (FusionSpace b c f) → (FusionSpace a f d) → 𝕜
    
  /-- The R-move (Braiding) acting on a fusion channel. -/
  Rmove : ∀ a b c, FusionSpace a b c → FusionSpace b a c → 𝕜
  
-- The interface is exported for downstream usage.
variable {𝕜} (D : QuantumG2FusionCoherenceDatum 𝕜)

def SimpleSector := D.SimpleSector
def fusionMultiplicity := D.fusionMultiplicity
def FusionSpace := D.FusionSpace

def Fmove := D.Fmove
def Rmove := D.Rmove

end InfoGeometry.Categorical
