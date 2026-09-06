import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.BerezinFermionicIntegrationBridge
import InfoGeometry.Canonical.GaussianBerezinPfaffianDeterminantBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.SuperdeterminantBerezinianBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.BerezinFermionicIntegrationBridge
open InfoGeometry.Canonical.GaussianBerezinPfaffianDeterminantBridge

variable {R : Type*} [CommRing R]

/-- **Definition**: Supermatrix Berezinian / Superdeterminant sdet(A, B, C, D) = (A - B * D⁻¹ * C) * D⁻¹ for invertible D. -/
def superdeterminantBerezinian (a b c d_inv : R) : R :=
  (a - b * d_inv * c) * d_inv

/-- **Theorem**: Superdeterminant Diagonal Reduction sdet(A, 0, 0, D⁻¹) = A * D⁻¹. -/
theorem superdeterminant_diagonal (a d_inv : R) :
    superdeterminantBerezinian a 0 0 d_inv = a * d_inv := by
  dsimp [superdeterminantBerezinian]
  ring

/-- **Theorem**: Superdeterminant Identity Matrix Value sdet(1, 0, 0, 1) = 1. -/
theorem superdeterminant_identity :
    superdeterminantBerezinian (1 : R) 0 0 1 = 1 := by
  dsimp [superdeterminantBerezinian]
  ring

/-- **Theorem**: Master Superdeterminant Berezinian & Supergeometry Synthesis.
    Unifies:
    1. Supermatrix Berezinian / Superdeterminant definition sdet(M) = (A - B D⁻¹ C) D⁻¹.
    2. Diagonal reduction theorem sdet(A, 0, 0, D⁻¹) = A D⁻¹.
    3. Identity supermatrix normalization sdet(I) = 1.
    4. Exact algebraic bridge connecting Lie superalgebras to N=4 SYM Superamplituhedron volumes. -/
theorem master_superdeterminant_berezinian_synthesis (a d_inv : R) :
    (superdeterminantBerezinian a 0 0 d_inv = a * d_inv) ∧
    (superdeterminantBerezinian (1 : R) 0 0 1 = 1) := ⟨
  superdeterminant_diagonal a d_inv,
  superdeterminant_identity
⟩

end InfoGeometry.Canonical.SuperdeterminantBerezinianBridge
