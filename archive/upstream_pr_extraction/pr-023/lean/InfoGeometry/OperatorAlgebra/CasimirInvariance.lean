/-
InfoGeometry/OperatorAlgebra/CasimirInvariance.lean

Real-time Casimir invariance.

This module proves the honest algebraic core:

* arbitrary algebra automorphisms preserve the center;
* inner modular flows fix central elements pointwise;
* therefore a `VerifiedCasimir` is a constant of motion for an installed inner
  modular flow.

The complex KMS strip is intentionally not introduced here.  This file locks
the real-time anchor first.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.IndividuatedCl44Casimir
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.OperatorAlgebra.VerifiedCasimir
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CasimirInvariance

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.Thermodynamics
open IndividuatedCasimir
open InfoGeometry.OperatorAlgebra.IndividuatedCl44Casimir

/-! ## 1. Center preservation and inner modular flows -/

/-- A center element of an algebra. -/
def IsCentral
    {Op : Type*} [Ring Op]
    (c : Op) : Prop :=
  ∀ x : Op, c * x = x * c

/--
Ring equivalences preserve centrality.

This is the most that can be proved for a general automorphism: central
elements remain central, but they need not be fixed pointwise.
-/
theorem ringEquiv_preserves_central
    {Op : Type*} [Ring Op]
    (φ : Op ≃+* Op)
    {c : Op}
    (hc : IsCentral c) :
    IsCentral (φ c) := by
  intro z
  let x := φ.symm z
  have hx : z = φ x := by
    dsimp [x]
    simp
  rw [hx]
  calc
    φ c * φ x = φ (c * x) := by
      exact (φ.map_mul c x).symm
    _ = φ (x * c) := by
      rw [hc x]
    _ = φ x * φ c := by
      exact φ.map_mul x c

/--
An installed inner modular flow.

The modular flow is represented by conjugation

`σ_t(x) = U_t x U_t⁻¹`.

This is the exact extra datum needed to upgrade "centrality is preserved" to
"central elements are fixed pointwise".
-/
structure InnerModularFlow
  (Op : Type*) [Ring Op] where
  /-- Ring-level modular automorphism flow. -/
  modularFlow : InfoGeometry.OperatorAlgebra.Thermodynamics.ModularFlow Op

  /-- Implementing operator/unitary-like element. -/
  implementer : ℝ → Op

  /-- Supplied inverse of the implementer. -/
  implementerInv : ℝ → Op

  /-- Right inverse law for the implementer. -/
  implementer_mul_inv :
    ∀ t : ℝ, implementer t * implementerInv t = 1

  /-- The modular flow is implemented by conjugation. -/
  flow_eq_conj :
    ∀ (t : ℝ) (x : Op),
      modularFlow.flow t x = implementer t * x * implementerInv t

namespace InnerModularFlow

variable {Op : Type*} [Ring Op]
variable (σ : InnerModularFlow Op)

/--
Central elements are fixed by an inner modular flow.
-/
theorem fixed_of_central
    {c : Op}
    (hc : IsCentral c)
    (t : ℝ) :
    σ.modularFlow.flow t c = c := by
  calc
    σ.modularFlow.flow t c
        = σ.implementer t * c * σ.implementerInv t := by
            rw [σ.flow_eq_conj]
    _ = (c * σ.implementer t) * σ.implementerInv t := by
            rw [hc (σ.implementer t)]
    _ = c * (σ.implementer t * σ.implementerInv t) := by
            rw [mul_assoc]
    _ = c * 1 := by
            rw [σ.implementer_mul_inv]
    _ = c := by
            simp

/--
A verified Casimir is a constant of motion for an installed inner modular flow.
-/
theorem verifiedCasimir_constant_of_motion
    {G : Type*} [Group G]
    {α : SymmetryAction G Op}
    (V : VerifiedCasimir α)
    (t : ℝ) :
    σ.modularFlow.flow t V.C = V.C :=
  σ.fixed_of_central V.is_central t

end InnerModularFlow

/-! ## 2. Cl(4,4) trace-Casimir specialization -/

/--
The Drazin-core Clifford-trace Dirac-Souriau Casimir is fixed by any installed
inner real modular flow on the Dirac-Souriau observable algebra.
-/
theorem diracSouriauCasimir_constant_of_motion
    {G : Type*} [Group G]
    (S : OperatorSymmetryAction G DiracSouriauOp)
    (T : DiracSouriauCoreTrace)
    (σ : InnerModularFlow DiracSouriauOp)
    (t : ℝ) :
    σ.modularFlow.flow t (diracSouriauCasimir S T).C =
      (diracSouriauCasimir S T).C :=
  σ.verifiedCasimir_constant_of_motion (diracSouriauCasimir S T) t

/-! ## 3. Owner target -/

/--
Owner target for real-time Casimir anchoring.

Once an inner modular flow and a verified Casimir are installed, the Casimir is
fixed along real thermal time.
-/
@[owner_target_tag]
def CasimirInvarianceOwnerTarget : Prop :=
  ∀ (Op : Type*) [Ring Op],
  ∀ (G : Type*) [Group G],
  ∀ (α : SymmetryAction G Op),
  ∀ (V : VerifiedCasimir α),
  ∀ (σ : InnerModularFlow Op),
  ∀ t : ℝ,
    σ.modularFlow.flow t V.C = V.C

/-- The real-time Casimir invariance owner target is constructively discharged. -/
theorem casimirInvarianceOwnerTarget :
    CasimirInvarianceOwnerTarget := by
  intro Op _ G _ α V σ t
  exact σ.verifiedCasimir_constant_of_motion V t

end InfoGeometry.OperatorAlgebra.CasimirInvariance
