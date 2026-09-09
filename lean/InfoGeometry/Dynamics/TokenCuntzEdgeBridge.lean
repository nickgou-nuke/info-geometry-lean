import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Algebra.CuntzContractionLemmas
import InfoGeometry.Dynamics.EntropicTokenDynamics

/-!
# Cuntz edge transport for the token model

The token carrier and the Cuntz quotient are intentionally kept distinct.
This file is the algebraic edge interface: it exposes the two finite Cuntz
channels supplied by the canonical quotient owner, without claiming an
operator representation on `TokenHilbertSpace`.
-/

namespace InfoGeometry.Dynamics

noncomputable section

open InfoGeometry.Algebra.CuntzTensorQuotient

/-- The two formal transport edges of the token model. -/
def tokenCuntzEdge (i : Fin 2) : CuntzAlg 2 := cuntzS 2 i

/-- The formal reverse edge paired with a token transport edge. -/
def tokenCuntzReverseEdge (i : Fin 2) : CuntzAlg 2 := cuntzSdag 2 i

/-! A representation is an input datum, not an automatic consequence of the
formal quotient.  Once supplied, the quotient relations transport through
the algebra homomorphism into the associative endomorphism algebra. -/
structure TokenCuntzRepresentation (V : Type*) [Fintype V] where
  rep : CuntzAlg 2 →ₐ[ℂ] Module.End ℂ (TokenHilbertSpace V)

def tokenCuntzOperator {V : Type*} [Fintype V]
    (representation : TokenCuntzRepresentation V) (i : Fin 2) :
    Module.End ℂ (TokenHilbertSpace V) :=
  representation.rep (tokenCuntzEdge i)

def tokenCuntzAdjointOperator {V : Type*} [Fintype V]
    (representation : TokenCuntzRepresentation V) (i : Fin 2) :
    Module.End ℂ (TokenHilbertSpace V) :=
  representation.rep (tokenCuntzReverseEdge i)

@[simp] theorem tokenCuntzEdge_reverse_product (i j : Fin 2) :
    tokenCuntzReverseEdge i * tokenCuntzEdge j =
      if i = j then 1 else 0 := by
  simp [tokenCuntzReverseEdge, tokenCuntzEdge,
    cuntz_orthogonality]

theorem tokenCuntzEdge_range_sum :
    ∑ i : Fin 2, tokenCuntzEdge i * tokenCuntzReverseEdge i = 1 := by
  simpa [tokenCuntzEdge, tokenCuntzReverseEdge] using
    (cuntz_ranges_sum_one 2)

theorem tokenCuntzEdge_partial_isometry (i : Fin 2) :
    tokenCuntzEdge i * tokenCuntzReverseEdge i * tokenCuntzEdge i =
      tokenCuntzEdge i := by
  simpa [tokenCuntzEdge, tokenCuntzReverseEdge] using
    (InfoGeometry.Algebra.CuntzContractionLemmas.partial_isometry 2 i)

theorem tokenCuntzOperator_reverse_product
    {V : Type*} [Fintype V]
    (representation : TokenCuntzRepresentation V) (i j : Fin 2) :
    tokenCuntzAdjointOperator representation i *
        tokenCuntzOperator representation j =
      if i = j then 1 else 0 := by
  rw [tokenCuntzAdjointOperator, tokenCuntzOperator, ← map_mul]
  rw [tokenCuntzEdge_reverse_product]
  simp

theorem tokenCuntzOperator_range_sum
    {V : Type*} [Fintype V]
    (representation : TokenCuntzRepresentation V) :
    ∑ i : Fin 2, tokenCuntzOperator representation i *
        tokenCuntzAdjointOperator representation i = 1 := by
  have h := congrArg representation.rep tokenCuntzEdge_range_sum
  simpa [tokenCuntzOperator, tokenCuntzAdjointOperator] using h

theorem tokenCuntzOperator_partial_isometry
    {V : Type*} [Fintype V]
    (representation : TokenCuntzRepresentation V) (i : Fin 2) :
    tokenCuntzOperator representation i *
        tokenCuntzAdjointOperator representation i *
        tokenCuntzOperator representation i =
      tokenCuntzOperator representation i := by
  have h := congrArg representation.rep (tokenCuntzEdge_partial_isometry i)
  simpa [tokenCuntzOperator, tokenCuntzAdjointOperator] using h

end
end InfoGeometry.Dynamics
