import InfoGeometry.Categorical.FibonacciBraidDirectLimit
import InfoGeometry.Categorical.FibonacciBraidedTowerCone

namespace InfoGeometry.Categorical.FibonacciUniversalityColimit

open InfoGeometry.Categorical.FibonacciBraidDirectLimit
open InfoGeometry.Categorical.FibonacciBraidedTowerCone
open InfoGeometry.Topological.FibonacciAnyons

/-- The finite-stage Fibonacci braid Artin relation transports to the algebraic
direct-limit matrix images. -/
theorem braid_limit_artin_relation_of_finite_stage
    {Stage : Nat → Type _} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) (q qInv τ sqrtτ : Stage n)
    (hArtin :
      R_matrixOf q qInv * B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv =
        B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv *
          B_matrixOf q qInv τ sqrtτ) :
    limitRMatrix bond n q qInv * limitBMatrix bond n q qInv τ sqrtτ *
        limitRMatrix bond n q qInv =
      limitBMatrix bond n q qInv τ sqrtτ * limitRMatrix bond n q qInv *
        limitBMatrix bond n q qInv τ sqrtτ :=
  limit_artin_relation_of_finite_stage bond n q qInv τ sqrtτ hArtin

/-- Order-theoretic maximal-support readout for the tower lane, obtained from
chain-union closure and nonemptiness. -/
theorem zorn_maximal_support_readout
    (family : Set (Set ℕ))
    (chain_sUnion_mem : ∀ c ⊆ family, IsChain (· ⊆ ·) c → ⋃₀ c ∈ family)
    (nonempty : family.Nonempty) :
    ∃ M ∈ family, ∀ X ∈ family, M ⊆ X → X = M :=
  zorn_maximal_support family chain_sUnion_mem nonempty

end InfoGeometry.Categorical.FibonacciUniversalityColimit
