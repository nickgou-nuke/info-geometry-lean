/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.SplitOctonionStandardModel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PhysicalGhostZeroCochainSectorBridge
import InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Color Confinement BRST Bridge

This module bridges the SU(3) color grading sector from the Split Octonion Standard Model
with the integer-graded BRST Cohomology core.

Following the Kugo-Ojima confinement criterion, we establish that if the SU(3) color charge
operator is BRST-exact, then its action on a BRST-closed state is exact and therefore
represents zero in the quotient `ker q / im q`. This quotient statement alone does not
assert that the color charge annihilates the state vector.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ColorConfinement

open InfoGeometry.Canonical.PhysicalGhostZeroCochainSectorBridge
open InfoGeometry.Canonical.IntegerGradedBRSTCochainComplexBridge
open InfoGeometry.Canonical.BRSTExactClassZeroBridge
open InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- 
Kugo-Ojima Color Confinement Criterion (Algebraic Core).
If a color charge operator `c_op` is BRST-exact (i.e. `c_op = {Q, K} = Q ∘ K + K ∘ Q`),
then its action on any physical state `ψ` (where `Q ψ = 0`) is purely BRST-exact.
This is an exactness statement on the vector representative; it does not assert
that `c_op ψ = 0` as a vector.
-/
theorem kugo_ojima_color_confinement_exactness
    (q c_op k_op : Module.End R (ExteriorAlgebra R V))
    (h_color_exact : c_op = q.comp k_op + k_op.comp q)
    (psi : ExteriorAlgebra R V)
    (h_phys : q psi = 0) :
    c_op psi = q (k_op psi) := by
  calc c_op psi
    _ = (q.comp k_op + k_op.comp q) psi := by rw [h_color_exact]
    _ = q (k_op psi) + k_op (q psi) := rfl
    _ = q (k_op psi) + k_op 0 := by rw [h_phys]
    _ = q (k_op psi) + 0 := by rw [map_zero]
    _ = q (k_op psi) := add_zero _

/-- Any operator action already identified with a BRST-exact vector is zero
    in the corresponding element of the quotient `ker q / im q`. -/
theorem brst_exact_action_class_eq_zero
    {M : Type*} [AddCommGroup M] [Module R M]
    (q c_op : Module.End R M)
    (hq2 : q.comp q = 0)
    (psi chi : M)
    (h_action : c_op psi = q chi) :
    Submodule.Quotient.mk
      (p := LinearMap.range (brstExactToClosed q hq2))
      ⟨c_op psi, by
        rw [LinearMap.mem_ker, h_action]
        exact LinearMap.congr_fun hq2 chi⟩ =
      (Submodule.Quotient.mk 0 : brstCohomologyModule q hq2) := by
  have h_closed : q (q chi) = 0 := LinearMap.congr_fun hq2 chi
  have h_rep :
      (⟨c_op psi, by
        rw [LinearMap.mem_ker, h_action]
        exact h_closed⟩ : LinearMap.ker q) =
      ⟨q chi, by rw [LinearMap.mem_ker]; exact h_closed⟩ := by
    apply Subtype.ext
    exact h_action
  calc
    Submodule.Quotient.mk
        (p := LinearMap.range (brstExactToClosed q hq2))
        ⟨c_op psi, by
          rw [LinearMap.mem_ker, h_action]
          exact h_closed⟩ =
      Submodule.Quotient.mk
        (p := LinearMap.range (brstExactToClosed q hq2))
        ⟨q chi, by rw [LinearMap.mem_ker]; exact h_closed⟩ := by rw [h_rep]
    _ = (Submodule.Quotient.mk 0 : brstCohomologyModule q hq2) :=
      InfoGeometry.Canonical.BRSTExactClassZeroBridge.exact_state_class_eq_zero
        q hq2 chi

/-- A BRST-exact color charge acts trivially on the BRST cohomology class of
    every physical state.  This composes the color-charge exactness identity
    with the repository's quotient `ker q / im q`; the nilpotency hypothesis
    is needed to make exact states closed representatives. This quotient
    conclusion does not say that the charge annihilates the state vector. -/
theorem kugo_ojima_color_charge_class_eq_zero
    (q c_op k_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (h_color_exact : c_op = q.comp k_op + k_op.comp q)
    (psi : ExteriorAlgebra R V)
    (h_phys : q psi = 0) :
    Submodule.Quotient.mk
      (p := LinearMap.range (brstExactToClosed q hq2))
      ⟨c_op psi, by
        rw [LinearMap.mem_ker]
        rw [kugo_ojima_color_confinement_exactness
          q c_op k_op h_color_exact psi h_phys]
        exact LinearMap.congr_fun hq2 (k_op psi)⟩ =
      (Submodule.Quotient.mk 0 : brstCohomologyModule q hq2) := by
  exact brst_exact_action_class_eq_zero q c_op hq2 psi (k_op psi)
    (kugo_ojima_color_confinement_exactness
      q c_op k_op h_color_exact psi h_phys)

end InfoGeometry.OperatorAlgebra.ColorConfinement
