import InfoGeometry.Algebra.SplitJordanSpinor
import Mathlib.Tactic

/-!
# Proof-carrying finite packet for the reduced-structure/spin boundary

`SplitJordanSpinor.ReducedStructureSpinBoundary` is an honest boundary object: it
stores the target reduced-structure/spin comparison as a bare proposition and does
not claim the global isomorphism
`Str₀(J₂(A_s)) ≃ Spin(q/2+1,q/2+1)`.

This file does not alter that owner surface. Instead it records the finite theorem
layer that is already kernel-checked in `SplitJordanSpinor.lean`:

* the critical split dimension data `q ∈ {2,4,8}` and `D = q + 2`;
* the diagonal Jordan determinant formula `det(diag(α,β)) = αβ`;
* the identity raw matrix stabilizes the generic, null, and diagonal-null
  representatives.

Boundary:
* no reduced-structure group construction;
* no spin-group construction;
* no global comparison isomorphism theorem.
-/

namespace InfoGeometry.Algebra.ReducedStructureSpinCertifiedPacket

open SplitJordanSpinor

/-- Proof-carrying finite data parallel to `ReducedStructureSpinBoundary`. -/
structure ReducedStructureSpinFinitePacket where
  criticalDimension : SplitCriticalDimension
  q : ℕ
  D : ℕ
  q_eq : q = SplitCriticalDimension.q criticalDimension
  D_eq : D = SplitCriticalDimension.D criticalDimension
  q_val : q = 2 ∨ q = 4 ∨ q = 8
  determinant_diagonal :
    ∀ {K A : Type*} [CommRing K] [NonAssocSemiring A] [SMul K A]
      [SplitCompositionAlgebra K A] (α β : K),
      JordanMatrix2.determinant (A := A)
          (JordanMatrix2.diagonal (A := A) α β) = α * β
  identity_stabilizes_generic :
    ∀ {A : Type*} [NonAssocSemiring A],
      SplitMatrix2.Stabilizes (A := A) SplitMatrix2.identity
        (Spinor2.genericRepresentative (A := A))
  identity_stabilizes_null :
    ∀ {A : Type*} [NonAssocSemiring A] (ε : A),
      SplitMatrix2.Stabilizes (A := A) SplitMatrix2.identity
        (Spinor2.nullRepresentative (A := A) ε)
  identity_stabilizes_diagonalNull :
    ∀ {A : Type*} [NonAssocSemiring A] (ε : A),
      SplitMatrix2.Stabilizes (A := A) SplitMatrix2.identity
        (Spinor2.diagonalNullRepresentative (A := A) ε)

/-- The split-complex `(q,D) = (2,4)` finite packet. -/
def splitComplexBoundaryPacket : ReducedStructureSpinFinitePacket :=
  ⟨SplitCriticalDimension.splitComplex, 2, 4, rfl, rfl, Or.inl rfl,
    by
      intro K A _ _ _ _ α β
      simpa using JordanMatrix2.determinant_diagonal (A := A) α β,
    by
      intro A _
      simpa using SplitMatrix2.identity_stabilizes_generic (A := A),
    by
      intro A _ ε
      simpa using SplitMatrix2.identity_stabilizes_null (A := A) ε,
    by
      intro A _ ε
      simpa using SplitMatrix2.identity_stabilizes_diagonalNull (A := A) ε⟩

@[simp] theorem splitComplexBoundaryPacket_q :
    splitComplexBoundaryPacket.q = 2 := rfl

@[simp] theorem splitComplexBoundaryPacket_D :
    splitComplexBoundaryPacket.D = 4 := rfl

end InfoGeometry.Algebra.ReducedStructureSpinCertifiedPacket
