import Mathlib

namespace InfoGeometry.GrandUnification

open Matrix

/-!
# Siegel Upper Half Space

The Siegel upper half space `𝔥_g` is the space of complex symmetric `g × g` matrices
whose imaginary part is positive definite.

In the context of the E10 Grand Unification architecture, this space provides the 
precise moduli space for our `Pin(5,5)` vacuum and split real forms. The Cartan 
translations of the Kac-Moody Weyl group act directly on this bounded symmetric domain.
-/

/-- The Siegel upper half space `𝔥_g`: complex symmetric `g × g` matrices
whose imaginary part (entrywise) is positive definite.

Defined as a subtype so that `TopologicalSpace`, `MetricSpace`, and
`NormedAddCommGroup` transfer automatically from the ambient matrix space. -/
def SiegelUpperHalfSpace (g : ℕ) : Type :=
  { τ : Matrix (Fin g) (Fin g) ℂ // τ.IsSymm ∧ (τ.map Complex.im).PosDef }

namespace SiegelUpperHalfSpace

variable {g : ℕ}

/-- Access the underlying matrix of a Siegel upper-half-space point. -/
def val (τ : SiegelUpperHalfSpace g) : Matrix (Fin g) (Fin g) ℂ := τ.1

/-- The symmetry condition `τ = τᵀ`. -/
theorem isSymm (τ : SiegelUpperHalfSpace g) : τ.val.IsSymm := τ.2.1

/-- The imaginary part (entrywise) is positive definite. -/
theorem imPosDef (τ : SiegelUpperHalfSpace g) : (τ.val.map Complex.im).PosDef := τ.2.2

instance : CoeFun (SiegelUpperHalfSpace g) (fun _ => Matrix (Fin g) (Fin g) ℂ) :=
  ⟨fun τ => τ.val⟩

@[ext]
theorem ext {τ σ : SiegelUpperHalfSpace g} (h : τ.val = σ.val) : τ = σ :=
  Subtype.ext h

end SiegelUpperHalfSpace

end InfoGeometry.GrandUnification
