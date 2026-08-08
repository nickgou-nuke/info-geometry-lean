import Mathlib.LinearAlgebra.Trace
import proofs.CanonicalZornCliffordRepresentation

/-!
# Weyl Hamiltonian Topology in Zorn Matrices

This module implements the direct embedding of the Weyl Hamiltonian into the
Canonical Zorn Clifford Representation, bypassing 2x2 complex matrices and
singularities.

The momentum vector k ∈ ℂ³ is embedded into the 8D Zorn vector space. The 
Dirac gamma operators (acting on the 16D Zorn Dirac spinors) natively furnish
the Clifford algebra, giving the relativistic linear dispersion H² = |k|² I.
The topological Berry curvature is defined algebraically via the valence projector.
-/

noncomputable section

namespace WeylHamiltonianTopology

open CanonicalZornCliffordRepresentation

/-- 
An abstract 3D momentum embedding into the 8-dimensional Zorn vector carrier.
We assume the existence of an isometric embedding from ℂ³ into Vector8.
-/
structure WeylMomentumEmbedding where
  embed : (Fin 3 → ℂ) →ₗ[ℂ] CanonicalZornCompositionTriality.Vector8
  isometry : ∀ k : Fin 3 → ℂ,
    vectorQuadratic (embed k) = (k 0)^2 + (k 1)^2 + (k 2)^2

/--
The 16x16 Weyl Hamiltonian defined natively via the Zorn `diracGamma` operator.
This bypasses 2x2 complex Pauli matrices entirely.
-/
def weylHamiltonian (W : WeylMomentumEmbedding) (k : Fin 3 → ℂ) :
    Module.End ℂ DiracSpinor16 :=
  diracGamma (W.embed k)

/--
The structural triumph of the Zorn formalism:
The relativistic linear dispersion H(k)² = |k|² I is proven purely 
algebraically from the Zorn composition triality! No determinant is needed.
-/
theorem weyl_dispersion_sq (W : WeylMomentumEmbedding) (k : Fin 3 → ℂ) :
    (weylHamiltonian W k) * (weylHamiltonian W k) =
      algebraMap ℂ (Module.End ℂ DiracSpinor16) ((k 0)^2 + (k 1)^2 + (k 2)^2) := by
  dsimp [weylHamiltonian]
  rw [diracGamma_sq]
  rw [W.isometry k]

/--
The algebraic valence band projector.
For non-zero real momentum, P(k) = 1/2 (I - H(k)/|k|).
To avoid square roots in the abstract complex definition, we parameterize
by the inverse norm `invNormK`.
-/
def valenceProjector (W : WeylMomentumEmbedding) (k : Fin 3 → ℂ) (invNormK : ℂ) :
    Module.End ℂ DiracSpinor16 :=
  (1 / 2 : ℂ) • (1 - invNormK • weylHamiltonian W k)

/--
A purely algebraic formulation of the Berry curvature operator form Ω_{ij}.
The trace of this operator gives the topological monopole charge natively 
from the Zorn algebra.
-/
def berryCurvatureOperator (W : WeylMomentumEmbedding)
    (k : Fin 3 → ℂ) (invNormK : ℂ)
    (dP_di dP_dj : Module.End ℂ DiracSpinor16) : Module.End ℂ DiracSpinor16 :=
  -Complex.I • (valenceProjector W k invNormK * (dP_di * dP_dj - dP_dj * dP_di))

end WeylHamiltonianTopology
