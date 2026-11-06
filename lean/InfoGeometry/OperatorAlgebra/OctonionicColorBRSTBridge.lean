/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.ColorConfinementBRSTBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SplitOctonionStandardModel
import InfoGeometry.OperatorAlgebra.DiracKahlerSpinorBridge
import InfoGeometry.OperatorAlgebra.WeakBdGColorConfinementBridge
import InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge
import InfoGeometry.Canonical.Drazin

namespace InfoGeometry.OperatorAlgebra.ColorBRST

open InfoGeometry.OperatorAlgebra.ColorConfinement
open InfoGeometry.OperatorAlgebra.DiracKahler
open InfoGeometry.OperatorAlgebra.SplitOctonions.StandardModel
open InfoGeometry.OperatorAlgebra.WeakBdGColorConfinement
open InfoGeometry.Canonical.BRSTExactClassZeroBridge
open InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge

variable {V_base : Type*} [AddCommGroup V_base] [Module ℤ V_base]

/-- **Concrete color-to-BRST cohomology bridge.** On the finite 32-component
    operator module, the `g0Core` color grading has zero class in `ker Q / im Q`
    for every horizon boundary zero mode. The exact representative `-Q(K ψ)`
    follows from the owned horizon color-grading identity. -/
theorem horizon_color_charge_cohomology_class_eq_zero
    (S : ModularHorizonBoundaryState) :
    Submodule.Quotient.mk
      (p := LinearMap.range (brstExactToClosed
        horizonQ horizonQ_nilpotent))
      ⟨colorGradingEnd S.psi, by
        apply LinearMap.mem_ker.mpr
        have h_action : colorGradingEnd S.psi = horizonQ (-horizonK S.psi) := by
          rw [horizon_color_grading_brst_exact S, map_neg]
        rw [h_action]
        exact LinearMap.congr_fun horizonQ_nilpotent (-horizonK S.psi)⟩ =
      (Submodule.Quotient.mk 0 : brstCohomologyModule
        horizonQ horizonQ_nilpotent) := by
  have h_action : colorGradingEnd S.psi = horizonQ (-horizonK S.psi) := by
    rw [horizon_color_grading_brst_exact S, map_neg]
  exact brst_exact_action_class_eq_zero horizonQ colorGradingEnd
    horizonQ_nilpotent S.psi (-horizonK S.psi) h_action

/-- Every closed vector in the concrete 32-component horizon complex is exact.
    This follows from `Q K + K Q = 1`; it is a finite-carrier algebraic result. -/
theorem horizonQ_closed_state_is_exact (psi : Spin32Vec)
    (h_closed : horizonQ psi = 0) :
    ∃ chi : Spin32Vec, horizonQ chi = psi := by
  have h_id := LinearMap.congr_fun horizon_anticomm_end psi
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h_id
  rw [h_closed, map_zero, add_zero] at h_id
  exact ⟨horizonK psi, h_id⟩

/-- Every closed horizon vector represents zero in the algebraic BRST quotient
    `ker Q / im Q` on `Spin32Vec`. Thus this specific finite complex is
    contractible; this theorem makes no claim about the exterior-algebra model. -/
theorem horizonQ_closed_state_class_eq_zero (psi : Spin32Vec)
    (h_closed : horizonQ psi = 0) :
    Submodule.Quotient.mk
      (p := LinearMap.range (brstExactToClosed horizonQ horizonQ_nilpotent))
      ⟨psi, LinearMap.mem_ker.mpr h_closed⟩ =
      (Submodule.Quotient.mk 0 : brstCohomologyModule
        horizonQ horizonQ_nilpotent) := by
  obtain ⟨chi, h_exact⟩ := horizonQ_closed_state_is_exact psi h_closed
  have hrep :
      (⟨psi, LinearMap.mem_ker.mpr h_closed⟩ : LinearMap.ker horizonQ) =
        ⟨horizonQ chi, LinearMap.congr_fun horizonQ_nilpotent chi⟩ := by
    apply Subtype.ext
    exact h_exact.symm
  calc
    Submodule.Quotient.mk ⟨psi, LinearMap.mem_ker.mpr h_closed⟩ =
        Submodule.Quotient.mk
          ⟨horizonQ chi, LinearMap.congr_fun horizonQ_nilpotent chi⟩ :=
      congrArg (Submodule.Quotient.mk (p :=
        LinearMap.range (brstExactToClosed horizonQ horizonQ_nilpotent))) hrep
    _ = Submodule.Quotient.mk 0 :=
      exact_state_class_eq_zero horizonQ horizonQ_nilpotent chi

/-- The concrete horizon BRST differential is Drazin-nilpotent with zero
    Drazin inverse for parameter 2. This records the overlap of the finite
    `Spin32Vec` horizon carrier with the repository's canonical Drazin laws;
    it does not identify this carrier with the exterior-algebra BRST module. -/
theorem horizonQ_drazin_inverse_zero :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse horizonQ 0 2 := by
  have h₂ : horizonQ ^ 2 = 0 := by
    simpa [pow_two, Module.End.mul_eq_comp] using horizonQ_nilpotent
  have h₃ : horizonQ ^ 3 = 0 := by
    rw [pow_succ, h₂]
    simp
  refine ⟨by simp, by simp, ?_⟩
  change horizonQ ^ 3 * 0 = horizonQ ^ 2
  rw [h₃, zero_mul, h₂]

/-- Conditional color-to-BRST statement. The operator identity expressing the
    transported color grading as a BRST anticommutator is an explicit input;
    the theorem proves its consequence on a BRST-closed vector and its quotient
    class. It does not derive the assumed identity from split-octonion
    multiplication or establish vector-level color singletness. -/
theorem octonionic_color_is_brst_exact
    (spinEq : SpinorExteriorEquiv (R := ℤ) (V_base := V_base))
    (q_ext k_op_ext : Module.End ℤ (ExteriorAlgebra ℤ V_base))
    (h_q_nilpotent : q_ext.comp q_ext = 0)
    (h_exactness : spinEq.equiv.conj colorGradingEnd = q_ext.comp k_op_ext + k_op_ext.comp q_ext)
    (psi : ExteriorAlgebra ℤ V_base)
    (h_phys : q_ext psi = 0) :
    (spinEq.equiv.conj colorGradingEnd psi = q_ext (k_op_ext psi)) ∧
      (Submodule.Quotient.mk
        (p := LinearMap.range (brstExactToClosed q_ext h_q_nilpotent))
        ⟨spinEq.equiv.conj colorGradingEnd psi, by
          change q_ext (spinEq.equiv.conj colorGradingEnd psi) = 0
          rw [kugo_ojima_color_confinement_exactness
            q_ext (spinEq.equiv.conj colorGradingEnd) k_op_ext
            h_exactness psi h_phys]
          exact LinearMap.congr_fun h_q_nilpotent (k_op_ext psi)⟩ =
       (Submodule.Quotient.mk 0 : brstCohomologyModule q_ext h_q_nilpotent)) := by
  constructor
  · exact kugo_ojima_color_confinement_exactness
      q_ext (spinEq.equiv.conj colorGradingEnd) k_op_ext h_exactness psi h_phys
  · exact kugo_ojima_color_charge_class_eq_zero
      q_ext (spinEq.equiv.conj colorGradingEnd) k_op_ext
      h_q_nilpotent h_exactness psi h_phys

end InfoGeometry.OperatorAlgebra.ColorBRST
