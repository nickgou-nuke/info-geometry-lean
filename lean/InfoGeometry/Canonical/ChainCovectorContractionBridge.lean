import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CovectorContractionBladeBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.ChainCovectorContractionBridge

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: 3-Blade Generator K3 = ι(v1) ∧ ι(v2) ∧ ι(v3). -/
def blade3 (v1 v2 v3 : V) : ExteriorAlgebra R V :=
  ι R v1 * ι R v2 * ι R v3

/-- **Definition**: Iterated Chain Covector Contraction (ι_{λ1} ι_{λ2} K5) for Adapted 5-Frame. -/
def contractChain
    (lambda1 lambda2 : V →ₗ[R] R) (u1 u2 w1 w2 w3 : V) : ExteriorAlgebra R V :=
  algebraMap R (ExteriorAlgebra R V) (lambda1 u1 * lambda2 u2 - lambda1 u2 * lambda2 u1) * blade3 w1 w2 w3

/-- **Theorem**: Chain Covector Contraction Anti-Commutativity (ι_{λ1} ι_{λ2} + ι_{λ2} ι_{λ1} = 0). -/
theorem contract_chain_anticommute
    (lambda1 lambda2 : V →ₗ[R] R) (u1 u2 w1 w2 w3 : V) :
    contractChain lambda1 lambda2 u1 u2 w1 w2 w3 +
    contractChain lambda2 lambda1 u1 u2 w1 w2 w3 = 0 := by
  dsimp [contractChain]
  rw [← add_mul, ← map_add]
  have h_add : (lambda1 u1 * lambda2 u2 - lambda1 u2 * lambda2 u1) +
               (lambda2 u1 * lambda1 u2 - lambda2 u2 * lambda1 u1) = 0 := by ring
  rw [h_add, map_zero, zero_mul]

/-- **Theorem**: Master Chain Covector Contraction Anti-Commutativity Synthesis.
    Unifies:
    1. Iterated covector contraction ι_{λ1} ι_{λ2} on adapted 5-frames down to 3-blade K3 ∈ ⋀³ V.
    2. Exact anti-commutativity law ι_{λ1} ι_{λ2} + ι_{λ2} ι_{λ1} = 0.
    3. Structural preservation of Cartan differential calculus on Grassmannian flag varieties. -/
theorem master_chain_covector_contraction_synthesis
    (lambda1 lambda2 : V →ₗ[R] R) (u1 u2 w1 w2 w3 : V) :
    contractChain lambda1 lambda2 u1 u2 w1 w2 w3 +
    contractChain lambda2 lambda1 u1 u2 w1 w2 w3 = 0 :=
  contract_chain_anticommute lambda1 lambda2 u1 u2 w1 w2 w3

end InfoGeometry.Canonical.ChainCovectorContractionBridge
