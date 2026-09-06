import InfoGeometry.Algebra.SplitJordanSpinor

/-!
# Split-octonionic Jordan--Cayley boundary interface

This file records the theorem-safe interface needed to extend the concrete
`J₂(C_s)` and `J₂(H_s)` trace-reversal identities to the split-octonionic
`J₂(O_s)` branch.

It does **not** construct split octonions, prove a concrete octonionic matrix
inverse, or prove `Str₀(J₂(O_s)) ≃ Spin(5,5)`.  Instead it packages the exact
kernel obligations: a trace-reversal/product packet and a proof of the
fundamental determinant identity.  Once such a proof is supplied for a concrete
split-octonion model, the Klein-quadric corollary follows automatically.
-/

namespace InfoGeometry.Algebra.SplitOctonionicJordanCayleyBoundary

open InfoGeometry.Algebra.SplitJordanSpinor

variable {K A : Type*} [CommRing K] [NonAssocSemiring A] [SMul K A]
variable [SplitCompositionAlgebra K A]

/-- The affine cone over the quadratic Klein quadric `det(X)=0` for `J₂(A_s)`. -/
def KleinQuadric (X : JordanMatrix2 K A) : Prop :=
  JordanMatrix2.determinant X = 0

/-- The diagonal packet returned by a trace-reversal product calculation. -/
structure DiagonalProduct (K : Type*) where
  e11 : K
  e22 : K
  deriving Repr

/--
Boundary/interface for a Jordan--Cayley trace-reversal identity on `J₂(A_s)`.

For non-associative algebras such as split octonions, this is deliberately a
structure of obligations rather than a fake matrix-multiplication theorem.
The field `fundamental_identity` is the kernel-checked content required from a
concrete model.
-/
structure JordanCayleyBoundary (K A : Type*) [CommRing K] [NonAssocSemiring A] [SMul K A]
    [SplitCompositionAlgebra K A] where
  /-- Trace reversal/adjugate candidate. -/
  traceReversal : JordanMatrix2 K A → JordanMatrix2 K A
  /-- The computed diagonal product packet for `X` and its trace reversal. -/
  productPacket : JordanMatrix2 K A → DiagonalProduct K
  /-- Fundamental determinant identity, in the sign convention of the coordinate packet. -/
  fundamental_identity : ∀ X : JordanMatrix2 K A,
    productPacket X =
      { e11 := JordanMatrix2.determinant X,
        e22 := -JordanMatrix2.determinant X }

namespace JordanCayleyBoundary

variable (B : JordanCayleyBoundary K A)

/-- On the Klein quadric, the diagonal trace-reversal product packet vanishes. -/
theorem on_klein_quadric (X : JordanMatrix2 K A) (hX : KleinQuadric X) :
    (B.productPacket X).e11 = 0 ∧ (B.productPacket X).e22 = 0 := by
  have hfund := B.fundamental_identity X
  constructor
  · have h11 := congrArg (fun P : DiagonalProduct K => P.e11) hfund
    simpa [KleinQuadric] using h11.trans hX
  · have h22 := congrArg (fun P : DiagonalProduct K => P.e22) hfund
    have hneg : -JordanMatrix2.determinant X = (0 : K) := by
      rw [hX]
      simp
    exact h22.trans hneg

end JordanCayleyBoundary

/--
Specialized boundary object for the split-octonionic branch `q=8`.

The `q_eq_8` field is the precise critical-dimension assertion.  The `cayley`
field is the trace-reversal determinant identity still required from a concrete
split-octonion model.
-/
structure SplitOctonionicBoundary (K A : Type*) [CommRing K] [NonAssocSemiring A] [SMul K A]
    [SplitCompositionAlgebra K A] where
  q_eq_8 : SplitCompositionAlgebra.q (K := K) (A := A) = 8
  cayley : JordanCayleyBoundary K A

namespace SplitOctonionicBoundary

/-- The ambient split-signature Jordan dimension is `q+2=10` in the octonionic branch. -/
theorem ambient_dimension_eq_ten (B : SplitOctonionicBoundary K A) :
    SplitCompositionAlgebra.q (K := K) (A := A) + 2 = 10 := by
  rw [SplitOctonionicBoundary.q_eq_8 B]

/-- The Klein-quadric zero-product corollary inherited from the packaged Cayley identity. -/
theorem on_klein_quadric (B : SplitOctonionicBoundary K A)
    (X : JordanMatrix2 K A) (hX : KleinQuadric X) :
    ((SplitOctonionicBoundary.cayley B).productPacket X).e11 = 0 ∧
      ((SplitOctonionicBoundary.cayley B).productPacket X).e22 = 0 :=
  (SplitOctonionicBoundary.cayley B).on_klein_quadric X hX

end SplitOctonionicBoundary

end InfoGeometry.Algebra.SplitOctonionicJordanCayleyBoundary
