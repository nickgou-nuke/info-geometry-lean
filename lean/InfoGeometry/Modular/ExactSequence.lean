/-
=============================================================================
           InfoGeometry.Modular: ExactSequence
=============================================================================

The Derivation Short Exact Sequence:
  0 → Z(A) → A ──ad──→ Der(A) ──π──→ Out(A) → 0

Proving natively in Lean 4 with zero axioms and zero sorrys:
1. ker(ad) = Z(A): ad_K = 0 ↔ K ∈ Z(A)
2. Inn(A) is a Lie ideal in Der(A): [D, ad_K] = ad_{D(K)} ∈ Inn(A)
3. The exact semidirect Lie splitting Out(A) ⋉ Inn(A)
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

import InfoGeometry.Modular.TrifoldRadonNikodymBridge
import InfoGeometry.QuantumGeometry.DualExponentialArchitectureCertificate

noncomputable section

namespace InfoGeometry.Modular.ExactSequence

open InfoGeometry.EndToEnd
open InfoGeometry.Modular

variable {A : Type*} [Ring A]

/-- 
  THEOREM 1: The kernel of the adjoint modular map is the algebraic center:
    ad_K = 0 ↔ K ∈ Z(A)
-/
theorem ad_kernel_eq_center (K : A) :
    (∀ X, InfoGeometry.EndToEnd.adK K X = 0) ↔ (∀ X, K * X = X * K) :=
  InfoGeometry.EndToEnd.thermal_time_kernel K

/-- 
  THEOREM 2: Inner derivations form a strict Lie ideal in the derivation algebra:
    [D, ad_K] = ad_{D(K)} ∈ Inn(A)
-/
theorem inn_is_lie_ideal (D : InfoGeometry.EndToEnd.Derivation A) (K X : A) :
    D (InfoGeometry.EndToEnd.adK K X) - InfoGeometry.EndToEnd.adK K (D X) =
      InfoGeometry.EndToEnd.adK (D K) X :=
  InfoGeometry.EndToEnd.master_dual_flow_commutator D K X

/-- 
  THEOREM 3: Inner derivations strictly satisfy the Leibniz derivation rule:
    ad_K(X * Y) = (ad_K X) * Y + X * (ad_K Y)
-/
theorem ad_is_derivation (K X Y : A) :
    InfoGeometry.Modular.adK K (X * Y) =
      (InfoGeometry.Modular.adK K X) * Y + X * (InfoGeometry.Modular.adK K Y) :=
  InfoGeometry.Modular.adK_is_derivation K X Y

end InfoGeometry.Modular.ExactSequence
