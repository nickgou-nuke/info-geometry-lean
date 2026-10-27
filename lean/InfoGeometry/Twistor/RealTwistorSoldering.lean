/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorIncidence
import InfoGeometry.Clifford.SolderingLinearEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The existing real soldering equivalence acting on incidence planes

The spacetime/endomorphism equivalence below composes the repository's existing
`Vec22` soldering equivalence with Mathlib's matrix/operator equivalence. It is
not a new scalar stand-in for a soldering form. The actual operator, its native
incidence submodule and its projectivization have compatible real carriers.
The metric/null-intersection theorem reuses the existing determinant identity.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealTwistorSoldering

open InfoGeometry.Clifford.Soldering
open InfoGeometry.Clifford.SolderingIsomorphism
open RealTwistorIncidence

abbrev Spinor := Fin 2 → ℝ

/-- Full real soldering into spinor endomorphisms. Both factors are established
linear equivalences; hence no injectivity or surjectivity field is assumed. -/
def operatorSoldering : Vec22 ≃ₗ[ℝ] Module.End ℝ Spinor :=
  solderingEquiv.trans Matrix.toLin'

@[simp] theorem operatorSoldering_apply (v : Vec22) (π : Spinor) :
    operatorSoldering v π = (soldering v).mulVec π := rfl

/-- A flat split-signature spacetime point determines its native real plane. -/
def spacetimeIncidenceSpace (v : Vec22) : Submodule ℝ (Carrier Spinor Spinor) :=
  incidenceSpace (operatorSoldering v)

/-- The incidence plane retains the full spacetime point. -/
theorem spacetimeIncidenceSpace_injective : Function.Injective spacetimeIncidenceSpace :=
  incidenceSpace_injective.comp operatorSoldering.injective

/-- Each flat incidence plane is a genuine two-dimensional real submodule. -/
theorem finrank_spacetimeIncidenceSpace (v : Vec22) :
    Module.finrank ℝ (spacetimeIncidenceSpace v) = 2 := by
  change Module.finrank ℝ (incidenceSpace (operatorSoldering v)) = 2
  rw [← (spinorEquivIncidence (operatorSoldering v)).finrank_eq]
  simp [Spinor]

/-- Null displacement is exactly intersection of the real incidence planes
away from the zero twistor. The result is specific to the existing `(2,2)` form. -/
theorem null_iff_shared_nonzero_twistor (v w : Vec22) :
    q22 (v - w) = 0 ↔
      ∃ z : Carrier Spinor Spinor, z ≠ 0 ∧
        z ∈ spacetimeIncidenceSpace v ∧ z ∈ spacetimeIncidenceSpace w := by
  change q22 (v - w) = 0 ↔
    ∃ z : Carrier Spinor Spinor, z ≠ 0 ∧
      z ∈ incidenceSpace (operatorSoldering v) ∧
      z ∈ incidenceSpace (operatorSoldering w)
  rw [shared_nonzero_twistor_iff]
  rw [← det_soldering_eq_q22]
  have hdet : (soldering (v - w)).det = 0 ↔
      ∃ π : Spinor, π ≠ 0 ∧ (soldering (v - w)).mulVec π = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.symm
  have heval (π : Spinor) :
      (soldering (v - w)).mulVec π =
        (operatorSoldering v - operatorSoldering w) π := by
    rw [← map_sub operatorSoldering v w]
    rfl
  simpa only [heval] using hdet

end InfoGeometry.Twistor.RealTwistorSoldering
