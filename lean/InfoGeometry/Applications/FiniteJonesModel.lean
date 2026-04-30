/-
InfoGeometry/Applications/FiniteJonesModel.lean

Concrete finite two-channel Jones model.

This is a small application-facing facade over the Fresnel/Jones reflection
socket.  It names the `s/p` carrier, projectors, and diagonal Jones operators
used by finite optical Erlanger instantiations.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.FresnelJonesReflection

noncomputable section

namespace InfoGeometry.Applications.FiniteJonesModel

open InfoGeometry.OperatorAlgebra.FresnelJonesReflection

/-! ## 1. Two-channel Jones carrier -/

/-- Two-component Jones vector in the Fresnel `s/p` basis. -/
abbrev JonesVector :=
  InfoGeometry.OperatorAlgebra.FresnelJonesReflection.JonesVector

/-- Jones operators on the finite two-channel carrier. -/
abbrev JonesOperator :=
  JonesVector →ₗ[ℂ] JonesVector

namespace Polarization

/-- The `s` Fresnel channel. -/
abbrev s : Fin 2 :=
  sIndex

/-- The `p` Fresnel channel. -/
abbrev p : Fin 2 :=
  pIndex

end Polarization

open Polarization

/-! ## 2. Diagonal Jones operators and projectors -/

/-- Diagonal Jones operator in the `s/p` basis. -/
def diagonalJones
    (r_s r_p : ℂ) : JonesOperator :=
  InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones r_s r_p

/-- The `s`-channel projector. -/
def Ps : JonesOperator :=
  InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector

/-- The `p`-channel projector. -/
def Pp : JonesOperator :=
  InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pProjector

/-- Projector onto one of the two basis channels. -/
def modeProjector
    (mode : Fin 2) : JonesOperator where
  toFun E := fun i => if i = mode then E mode else 0
  map_add' := by
    intro E F
    ext i
    by_cases hi : i = mode <;> simp [hi]
  map_smul' := by
    intro c E
    ext i
    by_cases hi : i = mode <;> simp [hi]

/-- The `s` projector is the mode projector at `s`. -/
theorem Ps_eq_modeProjector_s :
    Ps = modeProjector s := by
  ext E i
  fin_cases i <;> simp [Ps, modeProjector, s, sIndex, pIndex,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones]

/-- The `p` projector is the mode projector at `p`. -/
theorem Pp_eq_modeProjector_p :
    Pp = modeProjector p := by
  ext E i
  fin_cases i <;> simp [Pp, modeProjector, p, sIndex, pIndex,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pProjector,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones]

/-- The `s` projector is idempotent. -/
theorem Ps_idempotent :
    Ps.comp Ps = Ps :=
  InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector_idempotent

/-- The `p` projector is idempotent. -/
theorem Pp_idempotent :
    Pp.comp Pp = Pp :=
  InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pProjector_idempotent

/-- The two channel projectors sum to the identity. -/
theorem Ps_add_Pp :
    Ps + Pp = LinearMap.id :=
  InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector_add_pProjector

/-- A diagonal Jones operator with killed `p` channel is a scalar multiple of `Ps`. -/
theorem diagonalJones_p_zero
    (r_s : ℂ) :
    diagonalJones r_s 0 = r_s • Ps := by
  ext E i
  fin_cases i <;> simp [diagonalJones, Ps, sIndex, pIndex,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector]

end InfoGeometry.Applications.FiniteJonesModel
