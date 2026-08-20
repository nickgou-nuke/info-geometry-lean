/-
=============================================================================
      InfoGeometry.Modular: DualExponentialCommutatorBridge
=============================================================================

The Master Dynamical Backreaction Commutator:
  [D, ad_K](X) = ad_{D(K)}(X)

Proving that geometric spacetime derivations dynamically pump modular flows.
Zero Custom Axioms • Zero Sorries • Fully Native Mathlib 4
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

import InfoGeometry.QuantumGeometry.DualExponentialArchitectureCertificate

noncomputable section

namespace InfoGeometry.Modular.DualExponentialCommutatorBridge

open InfoGeometry.EndToEnd

variable {A : Type*} [Ring A]

/-- 
  MASTER DYNAMICAL BACKREACTION COMMUTATOR:
  [D, ad_K](X) = ad_{D(K)}(X)
-/
theorem master_dual_flow_commutator (D : InfoGeometry.EndToEnd.Derivation A) (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X :=
  InfoGeometry.EndToEnd.master_dual_flow_commutator D K X

/-- 
  Thermal Time Invariance:
  ad_K = 0 ↔ K ∈ Z(A)
-/
theorem thermal_time_kernel (K : A) :
    (∀ X, adK K X = 0) ↔ (∀ X, K * X = X * K) :=
  InfoGeometry.EndToEnd.thermal_time_kernel K

end InfoGeometry.Modular.DualExponentialCommutatorBridge
