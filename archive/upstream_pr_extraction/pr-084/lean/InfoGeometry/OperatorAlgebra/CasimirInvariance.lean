/-
InfoGeometry/OperatorAlgebra/CasimirInvariance.lean

Algebraic Casimir invariance.

This module proves the honest algebraic core:

* arbitrary algebra automorphisms preserve the center;
* conjugation by an explicitly displayed inverse pair fixes central elements;
* therefore a `VerifiedCasimir` is fixed by such a displayed conjugation.

No modular-flow implementation is installed as a structure here.  In a standard
representation, modular time is spatially implemented by the modular operator;
the implementing unitaries need not lie inside the represented algebra.

The complex KMS strip is intentionally not introduced here.  This file locks
the algebraic center/Casimir anchor first.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.IndividuatedCl44Casimir
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.OperatorAlgebra.VerifiedCasimir

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CasimirInvariance

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.Thermodynamics
open IndividuatedCasimir
open InfoGeometry.OperatorAlgebra.IndividuatedCl44Casimir

/-! ## 1. Center preservation and displayed conjugations -/

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

variable {Op : Type*} [Ring Op]

/--
Central elements are fixed by a displayed conjugation inverse pair.

This is only a ring lemma.  It does not install, infer, or assume an inner
Tomita modular flow.
-/
theorem central_fixed_under_conjugation
    {c : Op}
    (hc : IsCentral c)
    (u v : Op)
    (huv : u * v = 1) :
    u * c * v = c := by
  calc
    u * c * v = (c * u) * v := by
            rw [hc u]
    _ = c * (u * v) := by
            rw [mul_assoc]
    _ = c * 1 := by
            rw [huv]
    _ = c := by
            simp

/--
A verified Casimir is fixed by a displayed conjugation inverse pair.
-/
theorem verifiedCasimir_fixed_under_conjugation
    {G : Type*} [Group G]
    {α : SymmetryAction G Op}
    (C : VerifiedCasimir α)
    (hcentral : IsCentral C)
    (u v : Op)
    (huv : u * v = 1) :
    u * C * v = C :=
  central_fixed_under_conjugation hcentral u v huv

/-! ## 2. Cl(4,4) trace-Casimir specialization -/

/--
The Drazin-core Clifford-trace Dirac-Souriau Casimir is fixed by a displayed
conjugation inverse pair on the Dirac-Souriau observable algebra.
-/
theorem diracSouriauCasimir_fixed_under_conjugation
    (T : DiracSouriauCoreTrace)
    (u v : DiracSouriauOp)
    (huv : u * v = 1) :
    u * diracSouriauCasimir T * v =
      diracSouriauCasimir T := by
  dsimp [diracSouriauCasimir, DiracSouriauCoreTrace.constructCasimirElement]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one]
  rw [huv]

/-! ## 3. Casimir invariance theorem -/

/--
Owner theorem for algebraic Casimir anchoring.

Once a verified Casimir and an explicit inverse pair are displayed, conjugation
fixes the Casimir.  This is not a modular-flow theorem.
-/
theorem verifiedCasimir_invariant_under_inverse_pair :
  ∀ (Op : Type*) [Ring Op],
  ∀ (G : Type*) [Group G],
  ∀ (α : SymmetryAction G Op),
  ∀ (C : VerifiedCasimir α),
  ∀ (hcentral : IsCentral C),
  ∀ u v : Op,
    u * v = 1 →
      u * C * v = C := by
  intro Op _ G _ α C hcentral u v huv
  exact verifiedCasimir_fixed_under_conjugation C hcentral u v huv

end InfoGeometry.OperatorAlgebra.CasimirInvariance
