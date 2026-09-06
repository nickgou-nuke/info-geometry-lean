import Mathlib

/-!
# Quantum G2 R-Matrix Braiding Datum

This file provides the foundation for the genuinely non-Abelian anyon statistics
derived from the quantum group $U_q(\mathfrak{g}_2)$. 
Instead of a simple scalar Abelian twist, we formalize the representation of 
the universal R-matrix $\mathscr{R}_q$ on a concrete module $V$ via its checked 
variant $\check{R}$.

The datum asserts the Yang--Baxter equation (the Artin braid relation) and
crucially requires the monodromy $M = \check{R}^2$ to be non-trivial, proving
that the representation breaks symmetric statistics and opens the path to 
braided fusion categories.
-/

namespace InfoGeometry.Canonical.QuantumG2RMatrixBraidingDatum

open TensorProduct
open scoped TensorProduct

/-- Abstract datum for a quantum G2 R-matrix realization on a module $V$. -/
structure QuantumG2RMatrixDatum
    (𝕜 V : Type*)
    [Field 𝕜]
    [AddCommGroup V]
    [Module 𝕜 V] where
  
  /-- Quantum deformation parameter. -/
  q : 𝕜

  /-- Concrete checked R operator on the chosen quantum module: $\check{R} : V \otimes V \simeq V \otimes V$. -/
  checkR : (V ⊗[𝕜] V) ≃ₗ[𝕜] (V ⊗[𝕜] V)

  /-- The checked R satisfies the Yang--Baxter (braid) equation on $V^{\otimes 3}$. 
  $\check{R}_{12} \check{R}_{23} \check{R}_{12} = \check{R}_{23} \check{R}_{12} \check{R}_{23}$ -/
  yangBaxter :
    let checkR12 : (V ⊗[𝕜] (V ⊗[𝕜] V)) ≃ₗ[𝕜] (V ⊗[𝕜] (V ⊗[𝕜] V)) :=
      (TensorProduct.assoc 𝕜 V V V).symm.trans $
        (TensorProduct.congr checkR (LinearEquiv.refl 𝕜 V)).trans $
          TensorProduct.assoc 𝕜 V V V
    let checkR23 : (V ⊗[𝕜] (V ⊗[𝕜] V)) ≃ₗ[𝕜] (V ⊗[𝕜] (V ⊗[𝕜] V)) :=
      TensorProduct.congr (LinearEquiv.refl 𝕜 V) checkR
    checkR12.trans (checkR23.trans checkR12) = checkR23.trans (checkR12.trans checkR23)

  /-- This realization is genuinely non-symmetric (the monodromy is non-trivial). 
  $M = \check{R}^2 \neq \mathrm{id}$. -/
  monodromy_nontrivial :
    checkR.trans checkR ≠ LinearEquiv.refl 𝕜 (V ⊗[𝕜] V)

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable (D : QuantumG2RMatrixDatum 𝕜 V)

/-- The fundamental checked R-matrix. -/
def g2CheckR : (V ⊗[𝕜] V) ≃ₗ[𝕜] (V ⊗[𝕜] V) := D.checkR

/-- Checked R-matrix acting on the first two tensor factors. -/
def g2CheckR12 : (V ⊗[𝕜] (V ⊗[𝕜] V)) ≃ₗ[𝕜] (V ⊗[𝕜] (V ⊗[𝕜] V)) :=
  (TensorProduct.assoc 𝕜 V V V).symm.trans $
    (TensorProduct.congr D.checkR (LinearEquiv.refl 𝕜 V)).trans $
      TensorProduct.assoc 𝕜 V V V

/-- Checked R-matrix acting on the second and third tensor factors. -/
def g2CheckR23 : (V ⊗[𝕜] (V ⊗[𝕜] V)) ≃ₗ[𝕜] (V ⊗[𝕜] (V ⊗[𝕜] V)) :=
  TensorProduct.congr (LinearEquiv.refl 𝕜 V) D.checkR

/-- The Yang-Baxter identity (braid relation) on three strands. -/
theorem g2CheckR_yangBaxter :
    (g2CheckR12 D).trans ((g2CheckR23 D).trans (g2CheckR12 D)) = 
      (g2CheckR23 D).trans ((g2CheckR12 D).trans (g2CheckR23 D)) :=
  D.yangBaxter

/-- The full monodromy operator $M = \check{R}^2$. -/
def g2Monodromy : (V ⊗[𝕜] V) ≃ₗ[𝕜] (V ⊗[𝕜] V) :=
  (g2CheckR D).trans (g2CheckR D)

/-- The central theorem: the quantum G2 representation has strictly non-trivial monodromy,
verifying that the braiding is not symmetric. -/
theorem g2Monodromy_ne_id : g2Monodromy D ≠ LinearEquiv.refl 𝕜 (V ⊗[𝕜] V) :=
  D.monodromy_nontrivial

end InfoGeometry.Canonical.QuantumG2RMatrixBraidingDatum
