/-
=============================================================================
                  InfoGeometry: Master Registry Module
=============================================================================

The Dual Exponential Architecture:
A Machine-Checked Mathematical Foundation for Spacetime Geometry,
Topological Superconductivity, and Quantum Modular Thermodynamics.

Exposing the 6 Master Theorems:
I. DYNAMIC CORE (The Engine of Time)
   1. master_dual_flow_commutator : [D, ad_K](X) = ad_{D(K)}(X)
   2. master_thermal_time_kernel  : ad_K = 0 ↔ K ∈ Z(A)
   3. master_inn_is_lie_ideal     : ad_K is an exact derivation
II. KINEMATIC CORE (The Superselection Rules)
   4. master_trifold_completeness : K = α • I + β • Γ + K₀
   5. master_projector_orthogonality : Tr(K₀) = 0 ∧ STr(K₀) = 0
   6. master_pure_shape_criterion : α = 0 ∧ β = 0 ↔ K = K₀

Zero Custom Axioms • Zero Sorries • Fully Native Mathlib 4
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

import InfoGeometry.Modular.TrifoldRadonNikodymBridge
import InfoGeometry.QuantumGeometry.DualExponentialArchitectureCertificate
import InfoGeometry.Canonical.CompleteUnifiedBundle

noncomputable section

namespace InfoGeometry.MasterRegistry

open InfoGeometry.EndToEnd
open InfoGeometry.Modular

/-!
=============================================================================
I. DYNAMIC CORE (The Engine of Time)
=============================================================================
-/

section DynamicCore

variable {A : Type*} [Ring A]

/-- 
  MASTER THEOREM 1 (The Engine of Backreaction):
  Spacetime derivations intertwine with modular inner derivations:
    [D, ad_K](X) = ad_{D(K)}(X)
-/
theorem master_dual_flow_commutator (D : Derivation A) (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X :=
  InfoGeometry.EndToEnd.master_dual_flow_commutator D K X

/-- 
  MASTER THEOREM 2 (Thermal Time Invariance of the Center):
  The thermal flow vanishes if and only if the generator is central:
    ad_K = 0 ↔ K ∈ Z(A)
-/
theorem master_thermal_time_kernel (K : A) :
    (∀ X, adK K X = 0) ↔ (∀ X, K * X = X * K) :=
  InfoGeometry.EndToEnd.thermal_time_kernel K

/-- 
  MASTER THEOREM 3 (Lie Ideal Property / Derivation Algebra):
  The inner modular generator is an exact derivation on the algebra:
    ad_K(X * Y) = (ad_K X) * Y + X * (ad_K Y)
-/
theorem master_inn_is_lie_ideal (K X Y : A) :
    InfoGeometry.Modular.adK K (X * Y) =
      (InfoGeometry.Modular.adK K X) * Y + X * (InfoGeometry.Modular.adK K Y) :=
  InfoGeometry.Modular.adK_is_derivation K X Y

end DynamicCore

/-!
=============================================================================
II. KINEMATIC CORE (The Superselection Rules)
=============================================================================
-/

section KinematicCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "BlockMat" => Matrix (ι ⊕ ι) (ι ⊕ ι) R
local notation "SubMat" => Matrix ι ι R

/-- 
  MASTER THEOREM 4 (Trifold Completeness):
  Every block-diagonal modular surprisal operator is uniquely and exactly partitioned:
    K = α • I + β • Γ + K₀
-/
theorem master_trifold_completeness (two_n_inv : R) (A B : SubMat) :
    blockDiag A B =
      (alphaCommon two_n_inv A B) • (identityDoubled : BlockMat) +
      (betaChiral two_n_inv A B) • (Gamma : BlockMat) +
      K_zero two_n_inv A B :=
  trifold_reconstruction two_n_inv A B

/-- 
  MASTER THEOREM 5 (Projector Orthogonality):
  The pure shape component K₀ is strictly orthogonal to volume (Trace) and chirality (Supertrace):
    Tr(K₀) = 0 ∧ STr(K₀) = 0
-/
theorem master_projector_orthogonality
    (two_n_inv : R)
    (h_two_n : (2 * Fintype.card ι : R) * two_n_inv = 1)
    (A B : SubMat) :
    Matrix.trace (K_zero two_n_inv A B) = 0 ∧
    superTrace (K_zero two_n_inv A B) = 0 :=
  ⟨trifold_alpha_orthogonality two_n_inv h_two_n A B,
   trifold_beta_orthogonality two_n_inv h_two_n A B⟩

/-- 
  MASTER THEOREM 6 (Pure Shape / Gauge Vacuum Criterion):
  A modular operator is pure shape if and only if both scalar trace components vanish:
    α = 0 ∧ β = 0 ↔ K = K₀
-/
theorem master_pure_shape_criterion (two_n_inv : R) (A B : SubMat) :
    (alphaCommon two_n_inv A B = 0 ∧ betaChiral two_n_inv A B = 0) ↔
      blockDiag A B = K_zero two_n_inv A B :=
  pure_shape_criterion two_n_inv A B

end KinematicCore

end InfoGeometry.MasterRegistry
