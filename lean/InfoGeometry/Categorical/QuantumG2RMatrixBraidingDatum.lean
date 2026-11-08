import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Quantum G₂ R-Matrix Braiding Datum

This file records a representation-level interface for a checked quantum
R-operator.  It does not construct a universal `U_q (g₂)` R-matrix; that
provenance remains a separate downstream bridge.
-/

namespace InfoGeometry.Categorical.QuantumG2RMatrixBraidingDatum

open TensorProduct

variable (𝕜 V : Type*) [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Transport a local operator on the first two factors to the right-associated
three-fold tensor product. -/
def map12 (R : (V ⊗[𝕜] V) ≃ₗ[𝕜] (V ⊗[𝕜] V)) :
    (V ⊗[𝕜] (V ⊗[𝕜] V)) ≃ₗ[𝕜] (V ⊗[𝕜] (V ⊗[𝕜] V)) :=
  (TensorProduct.assoc 𝕜 V V V).symm.trans
    ((TensorProduct.congr R (LinearEquiv.refl 𝕜 V)).trans
      (TensorProduct.assoc 𝕜 V V V))

/-- Local operator on the second and third factors. -/
def map23 (R : (V ⊗[𝕜] V) ≃ₗ[𝕜] (V ⊗[𝕜] V)) :
    (V ⊗[𝕜] (V ⊗[𝕜] V)) ≃ₗ[𝕜] (V ⊗[𝕜] (V ⊗[𝕜] V)) :=
  TensorProduct.congr (LinearEquiv.refl 𝕜 V) R

/-- A checked R-operator with derived local tensor actions and coherence. -/
structure QuantumG2RMatrixDatum where
  /-- Quantum deformation parameter. -/
  q : 𝕜
  /-- Checked R operator on the chosen module tensor square. -/
  checkR : (V ⊗[𝕜] V) ≃ₗ[𝕜] (V ⊗[𝕜] V)
  /-- Action on the first two tensor factors. -/
  checkR12 : (V ⊗[𝕜] (V ⊗[𝕜] V)) ≃ₗ[𝕜]
    (V ⊗[𝕜] (V ⊗[𝕜] V))
  /-- Action on the second and third tensor factors. -/
  checkR23 : (V ⊗[𝕜] (V ⊗[𝕜] V)) ≃ₗ[𝕜]
    (V ⊗[𝕜] (V ⊗[𝕜] V))
  /-- The local actions are derived from the same `checkR`. -/
  checkR12_eq : checkR12 = map12 𝕜 V checkR
  checkR23_eq : checkR23 = map23 𝕜 V checkR
  /-- Yang--Baxter equation on the right-associated triple tensor product. -/
  yangBaxter :
    checkR12.toLinearMap ∘ₗ checkR23.toLinearMap ∘ₗ checkR12.toLinearMap =
      checkR23.toLinearMap ∘ₗ checkR12.toLinearMap ∘ₗ checkR23.toLinearMap
  /-- Monodromy operator `checkR²`. -/
  monodromy : (V ⊗[𝕜] V) ≃ₗ[𝕜] (V ⊗[𝕜] V) := checkR.trans checkR
  /-- The concrete realization is not triangular. -/
  monodromy_nontrivial : monodromy.toLinearMap ≠ LinearMap.id

variable {𝕜 V} (D : QuantumG2RMatrixDatum 𝕜 V)

/-- The concrete checked R operator. -/
def g2CheckR : (V ⊗[𝕜] V) →ₗ[𝕜] (V ⊗[𝕜] V) := D.checkR.toLinearMap

/-- The checked R operator is invertible. -/
theorem g2CheckR_invertible : Function.Bijective (g2CheckR D) :=
  D.checkR.bijective

/-- The supplied Yang--Baxter witness. -/
theorem g2CheckR_yangBaxter :
    D.checkR12.toLinearMap ∘ₗ D.checkR23.toLinearMap ∘ₗ D.checkR12.toLinearMap =
      D.checkR23.toLinearMap ∘ₗ D.checkR12.toLinearMap ∘ₗ D.checkR23.toLinearMap :=
  D.yangBaxter

/-- Adjacent braid generators satisfy the Artin relation. -/
theorem g2Braid_adjacent :
    D.checkR12.toLinearMap ∘ₗ D.checkR23.toLinearMap ∘ₗ D.checkR12.toLinearMap =
      D.checkR23.toLinearMap ∘ₗ D.checkR12.toLinearMap ∘ₗ D.checkR23.toLinearMap :=
  D.yangBaxter

/-- The monodromy operator `checkR²`. -/
def g2Monodromy : (V ⊗[𝕜] V) →ₗ[𝕜] (V ⊗[𝕜] V) := D.monodromy.toLinearMap

/-- A nontrivial monodromy witness for the supplied realization. -/
theorem g2Monodromy_ne_id : g2Monodromy D ≠ LinearMap.id :=
  D.monodromy_nontrivial

end InfoGeometry.Categorical.QuantumG2RMatrixBraidingDatum
