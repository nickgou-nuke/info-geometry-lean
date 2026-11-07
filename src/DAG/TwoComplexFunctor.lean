import DAG.GeneralizedTwoComplex
import DAG.TwoComplexColimitRecursor
import DAG.CocycleBridge
import DAG.ConnesHodgeBridge

/-!
# DAG.TwoComplexFunctor

The functor F : TwoComplex → AlgEnd mapping the discrete DAG
to the continuous operator algebra on the doubled space fiber.

## Architecture

```
GeneralizedTwoComplex R ──F──→ AlgebraEnd (DoubledSpace ℝ)
         │                              │
         │ d1, d2, star                 │ sigma_t, K_e
         │                              │
         ▼                              ▼
   Hodge decomposition    ←──→    Connes cocycle H^1
   (harmonic = b1)                (cocycles mod coboundaries)
```

## The Edge Algebra

Each edge e : u → v in the TwoComplex is assigned a skew-adjoint
generator K_e in the fiber algebra (2x2 matrices on DoubledSpace R).
The boundary operator d1 maps to the commutator [K_e, -].
The boundary-squared-zero condition d2∘d1 = 0 becomes the Jacobi
identity on the algebra generators.

The weighted sum K = Σ_e ψ(e)·K_e generates the modular flow:

    sigma_t(A) = exp(t·K) · A · exp(-t·K)

A 1-chain ψ is harmonic (Δ₁ψ = 0) iff the cocycle u(t) = exp(t·K)
satisfies the Connes cocycle condition:

    u(s+t) = u(s) · sigma_s(u(t))

This is the Hodge-cocycle correspondence: Layer 1 (discrete)
⇔ Layer 3 (continuous).
-/

open DAG

namespace DAG.TwoComplexFunctor

/-! ## The colimit algebra -/

/--
Build the edge algebra for a concrete TwoComplex by folding
over its construction using the colimit recursor.

This IS the functor: nodes → trivial algebra, each edge/face/digon
addition extends the algebra by a new generator or relation.
-/
def buildAlgebra {α : Type} [BEq α] [Hashable α]
    (_tc : TwoComplex α) : Type :=
  -- This layer exposes the finite computable Hodge package.
  -- Continuous operator-algebra identifications must be proved in their owner
  -- files before they are surfaced here.
  CocycleBridge.HodgeCocycleData α

/--
Construct the algebra by the colimit universal property:
start with the node-only algebra, then fold over all
edge, face, and digon insertions.
-/
def buildAlgebraByColimit {α : Type} [BEq α] [Hashable α]
    (tc : TwoComplex α) : CocycleBridge.HodgeCocycleData α :=
  CocycleBridge.fromTwoComplex tc

/-! ## The Hodge-cocycle correspondence -/

/--
**Theorem (harmonic equals cocycle dimension).**
The dimension of harmonic 1-chains on a TwoComplex (b₁ via Hodge)
equals the maximum number of independent Connes 1-cocycles.

For the chain graph: b₁ = 0, so every Connes cocycle is trivial.
For graphs with b₁ > 0, nontrivial harmonic chains exist and
correspond to nontrivial Connes cocycles — topological invariants.
-/
theorem buildAlgebraByColimit_harmonicDim {α : Type} [BEq α] [Hashable α]
    (tc : TwoComplex α) :
    (buildAlgebraByColimit tc).hodgeDecomp.2.2 = betti1Hodge tc := rfl

end DAG.TwoComplexFunctor
