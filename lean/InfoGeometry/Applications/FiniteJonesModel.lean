/-
InfoGeometry/Applications/FiniteJonesModel.lean

Concrete finite two-channel Jones model.

This is a small application-facing facade over the Fresnel/Jones reflection
socket.  It names the `s/p` carrier, projectors, and diagonal Jones operators
used by finite optical Erlanger instantiations.

It proves the first concrete optical laboratory facts:

* the `s` and `p` projectors are idempotent and complementary;
* a diagonal Jones operator decomposes as `r_s • Ps + r_p • Pp`;
* a Brewster/rank-collapse event `r_p = 0` leaves only the `s` channel.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Basic
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

/-- The two channel projectors are disjoint in one order. -/
theorem Ps_comp_Pp :
    Ps.comp Pp = 0 :=
  InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector_comp_pProjector

/-- The two channel projectors are disjoint in the other order. -/
theorem Pp_comp_Ps :
    Pp.comp Ps = 0 :=
  InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pProjector_comp_sProjector

/-- The two channel projectors sum to the identity. -/
theorem Ps_add_Pp :
    Ps + Pp = LinearMap.id :=
  InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector_add_pProjector

/--
The diagonal Jones operator decomposes into its two polarization projectors:

`J(r_s,r_p) = r_s • Ps + r_p • Pp`.
-/
theorem diagonalJones_eq_projector_decomposition
    (r_s r_p : ℂ) :
    diagonalJones r_s r_p = r_s • Ps + r_p • Pp := by
  ext E i
  fin_cases i <;> simp [diagonalJones, Ps, Pp, sIndex, pIndex,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pProjector]

/-- A Brewster/rank-collapse event is the vanishing of the `p` channel. -/
def IsBrewsterCollapse
    (_r_s r_p : ℂ) : Prop :=
  r_p = 0

/--
At a Brewster collapse, the diagonal Jones operator is only the surviving
`s`-channel component.
-/
theorem diagonalJones_brewster
    (r_s r_p : ℂ)
    (hB : IsBrewsterCollapse r_s r_p) :
    diagonalJones r_s r_p = r_s • Ps := by
  rw [diagonalJones_eq_projector_decomposition]
  dsimp [IsBrewsterCollapse] at hB
  rw [hB]
  ext E i
  fin_cases i <;> simp [Ps, Pp, sIndex, pIndex,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pProjector,
    InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones]

/-- A diagonal Jones operator with killed `p` channel is a scalar multiple of `Ps`. -/
theorem diagonalJones_p_zero
    (r_s : ℂ) :
    diagonalJones r_s 0 = r_s • Ps :=
  diagonalJones_brewster r_s 0 rfl

/-- A pure `p`-polarized input is killed at Brewster collapse. -/
theorem brewster_kills_p_input
    (r_s : ℂ)
    (v : JonesVector)
    (hpure : Ps v = 0) :
    diagonalJones r_s 0 v = 0 := by
  ext i
  fin_cases i
  · have hs : v s = 0 := by
      have h := congrArg (fun f : JonesVector => f s) hpure
      simpa [Ps, s, sIndex,
        InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector,
        InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones] using h
    have hs0 : v 0 = 0 := by
      simpa [s, sIndex] using hs
    simp [diagonalJones, sIndex, pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones, hs0]
  · simp [diagonalJones, sIndex, pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones]

/-- A pure `s`-polarized input survives as scalar multiplication by `r_s`. -/
theorem brewster_scales_s_input
    (r_s : ℂ)
    (v : JonesVector)
    (hpure : Pp v = 0) :
    diagonalJones r_s 0 v = r_s • v := by
  ext i
  fin_cases i
  · simp [diagonalJones, sIndex, pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones]
  · have hp : v p = 0 := by
      have h := congrArg (fun f : JonesVector => f p) hpure
      simpa [Pp, p, pIndex, sIndex,
        InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pProjector,
        InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones] using h
    have hp1 : v 1 = 0 := by
      simpa [p, pIndex] using hp
    simp [diagonalJones, sIndex, pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones, hp1]

/-! ## 3. Jones events as projector-split optical readouts -/

/-- A finite Jones event packages the two amplitudes and its diagonal operator. -/
structure FiniteJonesEvent where
  r_s : ℂ
  r_p : ℂ

/-- The operator associated to a finite Jones event. -/
def FiniteJonesEvent.operator
    (E : FiniteJonesEvent) : JonesOperator :=
  diagonalJones E.r_s E.r_p

/-- The event is Brewster-collapsed when its `p`-channel amplitude vanishes. -/
def FiniteJonesEvent.IsBrewster
    (E : FiniteJonesEvent) : Prop :=
  E.r_p = 0

/--
Constructive witness that the `p`-channel has collapsed at Brewster.

This packages the equality witness as first-class event data instead of a
bare hypothesis in downstream theorem signatures.
-/
structure FiniteJonesEvent.BrewsterWitness
    (E : FiniteJonesEvent) : Type where
  rp_zero : E.r_p = 0

namespace FiniteJonesEvent

/-- Every finite Jones event decomposes into its `s/p` channel projectors. -/
theorem operator_decomposition
    (E : FiniteJonesEvent) :
    E.operator = E.r_s • Ps + E.r_p • Pp :=
  diagonalJones_eq_projector_decomposition E.r_s E.r_p

/-- A Brewster event is exactly the `s`-channel core operator. -/
theorem operator_eq_s_core_of_brewster
    (E : FiniteJonesEvent)
    (hE : E.IsBrewster) :
    E.operator = E.r_s • Ps := by
  dsimp [operator, IsBrewster] at *
  exact diagonalJones_brewster E.r_s E.r_p hE

/--
Constructive-witness variant of `operator_eq_s_core_of_brewster`.
-/
theorem operator_eq_s_core_of_sorry
    (E : FiniteJonesEvent)
    (w : BrewsterWitness E) :
    E.operator = E.r_s • Ps := by
  exact operator_eq_s_core_of_brewster E w.rp_zero

end FiniteJonesEvent

end InfoGeometry.Applications.FiniteJonesModel
