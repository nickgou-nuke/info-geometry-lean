import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm

/-! # Operator surprisal / BKM Hessian / Souriau KKS bridge

The existing faithful density, CFC surprisal, Kubo--Mori pairing, and real
BKM form remain the owners.  This module adds only the commutator readout.
The Fréchet identification of `CFC.log` with the inverse Kubo--Mori map is
left as an explicit analytic frontier.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorSurprisalBKMKKS

open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
open SouriauOnsagerBKM

variable {n : ℕ}

theorem faithful_stateSurprisal_apply (D : FaithfulDensityOperator n) :
    stateSurprisal D.rho = -cfc Real.log D.rho := by
  exact stateSurprisal_apply D.rho

theorem faithful_exp_neg_stateSurprisal (D : FaithfulDensityOperator n) :
    NormedSpace.exp (-stateSurprisal D.rho) = D.rho := by
  exact exp_neg_stateSurprisal D.rho D.strictlyPositive

theorem bkm_hessian_readout (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (A B : FiniteOperatorAlgebra n) :
    D.bkmRealBilinForm hpow A B = (D.kuboMoriPairing A B).re := by
  exact D.bkmRealBilinForm_apply hpow A B

theorem bkm_hessian_symm (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) :
    (D.bkmRealBilinForm hpow).IsSymm := by
  exact D.bkmRealBilinForm_symm hpow

def operatorKKS (D : FaithfulDensityOperator n)
    (X Y : FiniteOperatorAlgebra n) : ℝ :=
  (finiteOperatorTrace (D.rho * (X * Y - Y * X))).re

@[simp] theorem operatorKKS_apply (D : FaithfulDensityOperator n)
    (X Y : FiniteOperatorAlgebra n) :
    operatorKKS D X Y =
      (finiteOperatorTrace (D.rho * (X * Y - Y * X))).re := rfl

@[simp] theorem operatorKKS_self (D : FaithfulDensityOperator n)
    (X : FiniteOperatorAlgebra n) : operatorKKS D X X = 0 := by
  simp [operatorKKS]

theorem operatorKKS_skew (D : FaithfulDensityOperator n)
    (X Y : FiniteOperatorAlgebra n) :
    operatorKKS D Y X = -operatorKKS D X Y := by
  unfold operatorKKS
  have h : Y * X - X * Y = -(X * Y - Y * X) := by
    noncomm_ring
  rw [h]
  simp

theorem operatorKKS_add_left (D : FaithfulDensityOperator n)
    (X₁ X₂ Y : FiniteOperatorAlgebra n) :
    operatorKKS D (X₁ + X₂) Y =
      operatorKKS D X₁ Y + operatorKKS D X₂ Y := by
  unfold operatorKKS
  simp [add_mul, mul_add]
  ring

theorem operatorKKS_add_right (D : FaithfulDensityOperator n)
    (X Y₁ Y₂ : FiniteOperatorAlgebra n) :
    operatorKKS D X (Y₁ + Y₂) =
      operatorKKS D X Y₁ + operatorKKS D X Y₂ := by
  unfold operatorKKS
  simp [add_mul, mul_add]
  ring

theorem operatorKKS_ne_zero_of_detected_commutator
    (D : FaithfulDensityOperator n) (X Y : FiniteOperatorAlgebra n)
    (h : (finiteOperatorTrace
      (D.rho * (X * Y - Y * X))).re ≠ 0) :
    operatorKKS D X Y ≠ 0 := h

end InfoGeometry.Canonical.OperatorSurprisalBKMKKS
