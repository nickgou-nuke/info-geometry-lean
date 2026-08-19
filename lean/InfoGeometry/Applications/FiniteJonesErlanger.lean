/-
InfoGeometry/Applications/FiniteJonesErlanger.lean

Finite Jones model as the first Erlanger instantiation.

The admissible optical phase group is the diagonal Jones phase centralizer.  It
preserves the `s/p` projectors, so the Brewster/Drazin core projector is an
Erlanger-invariant object under admissible optical phase conjugation.

Under a general Jones transform mixing `s` and `p`, the same projector is only
transported covariantly.
-/

import Mathlib.Tactic
import InfoGeometry.Applications.FiniteJonesModel

noncomputable section

namespace InfoGeometry.Applications.FiniteJonesErlanger

open InfoGeometry.Applications.FiniteJonesModel
open InfoGeometry.Applications.FiniteJonesModel.Polarization

/-! ## 1. Diagonal Jones phase units -/

/-- A diagonal optical phase unit: the finite Jones centralizer of the `s/p` splitting. -/
structure JonesPhaseUnit where
  phaseS : ℂˣ
  phaseP : ℂˣ

namespace JonesPhaseUnit

/-- The Jones operator associated to a diagonal phase unit. -/
def op
    (U : JonesPhaseUnit) : JonesOperator :=
  diagonalJones (U.phaseS : ℂ) (U.phaseP : ℂ)

/-- The inverse Jones operator. -/
def invOp
    (U : JonesPhaseUnit) : JonesOperator :=
  diagonalJones ((U.phaseS⁻¹ : ℂˣ) : ℂ) ((U.phaseP⁻¹ : ℂˣ) : ℂ)

/-- Conjugation by a diagonal Jones phase unit: `T ↦ U T U⁻¹`. -/
def conj
    (U : JonesPhaseUnit)
    (T : JonesOperator) : JonesOperator :=
  U.op.comp (T.comp U.invOp)

/-- The phase operator composed with its inverse is the identity. -/
theorem op_comp_invOp
    (U : JonesPhaseUnit) :
    U.op.comp U.invOp = LinearMap.id := by
  apply LinearMap.ext
  intro E
  funext i
  fin_cases i <;>
    simp [op, invOp, diagonalJones,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones]

/-- The inverse phase operator composed with the phase operator is the identity. -/
theorem invOp_comp_op
    (U : JonesPhaseUnit) :
    U.invOp.comp U.op = LinearMap.id := by
  apply LinearMap.ext
  intro E
  funext i
  fin_cases i <;>
    simp [op, invOp, diagonalJones,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones]

/-! ## 2. Phase invariance of the channel projectors -/

/-- The `s`-channel projector is invariant under diagonal optical phase conjugation. -/
theorem conj_Ps
    (U : JonesPhaseUnit) :
    U.conj Ps = Ps := by
  apply LinearMap.ext
  intro E
  funext i
  fin_cases i <;>
    simp [conj, op, invOp, Ps, diagonalJones,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones]

/-- The `p`-channel projector is invariant under diagonal optical phase conjugation. -/
theorem conj_Pp
    (U : JonesPhaseUnit) :
    U.conj Pp = Pp := by
  apply LinearMap.ext
  intro E
  funext i
  fin_cases i <;>
    simp [conj, op, invOp, Pp, diagonalJones,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pProjector,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones]

/-- A diagonal Jones operator is invariant under diagonal optical phase conjugation. -/
theorem conj_diagonalJones
    (U : JonesPhaseUnit)
    (r_s r_p : ℂ) :
    U.conj (diagonalJones r_s r_p) = diagonalJones r_s r_p := by
  apply LinearMap.ext
  intro E
  funext i
  fin_cases i <;>
    simp [conj, op, invOp, diagonalJones,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones,
      mul_left_comm]

end JonesPhaseUnit

/-! ## 3. Erlanger-invariant finite Jones operators -/

/-- Fixed by every admissible diagonal optical phase conjugation. -/
def IsPhaseErlangerInvariantOperator
    (T : JonesOperator) : Prop :=
  ∀ U : JonesPhaseUnit, U.conj T = T

/-- The Brewster/Drazin core projector is phase-Erlanger-invariant. -/
theorem Ps_phaseErlangerInvariant :
    IsPhaseErlangerInvariantOperator Ps := by
  intro U
  exact U.conj_Ps

/-- The killed/nil `p`-channel projector is phase-Erlanger-invariant. -/
theorem Pp_phaseErlangerInvariant :
    IsPhaseErlangerInvariantOperator Pp := by
  intro U
  exact U.conj_Pp

/-- Every diagonal Jones operator is invariant under the diagonal phase centralizer. -/
theorem diagonalJones_phaseErlangerInvariant
    (r_s r_p : ℂ) :
    IsPhaseErlangerInvariantOperator (diagonalJones r_s r_p) := by
  intro U
  exact U.conj_diagonalJones r_s r_p

/-! ## 4. Concrete finite Drazin core at Brewster collapse -/

/-- Drazin inverse of the Brewster-collapse diagonal Jones operator. -/
def brewsterDrazinInverse
    (r_s : ℂ) : JonesOperator :=
  diagonalJones r_s⁻¹ 0

/-- Core identity: `J(r_s,0) J(r_s⁻¹,0) = Ps`, assuming `r_s ≠ 0`. -/
theorem brewster_drazin_core_identity
    (r_s : ℂ)
    (hrs : r_s ≠ 0) :
    (diagonalJones r_s 0).comp (brewsterDrazinInverse r_s) = Ps := by
  apply LinearMap.ext
  intro E
  funext i
  fin_cases i <;>
    simp [brewsterDrazinInverse, diagonalJones, Ps, hrs,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector]

/-- The opposite core identity also holds in this diagonal finite model. -/
theorem brewster_drazin_left_core_identity
    (r_s : ℂ)
    (hrs : r_s ≠ 0) :
    (brewsterDrazinInverse r_s).comp (diagonalJones r_s 0) = Ps := by
  apply LinearMap.ext
  intro E
  funext i
  fin_cases i <;>
    simp [brewsterDrazinInverse, diagonalJones, Ps, hrs,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.pIndex,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.diagonalJones,
      InfoGeometry.OperatorAlgebra.FresnelJonesReflection.sProjector]

/-- The finite Brewster core identity is invariant under admissible phase conjugation. -/
theorem brewster_core_identity_phase_invariant
    (U : JonesPhaseUnit)
    (r_s : ℂ)
    (hrs : r_s ≠ 0) :
    U.conj ((diagonalJones r_s 0).comp (brewsterDrazinInverse r_s)) = Ps := by
  rw [brewster_drazin_core_identity r_s hrs]
  exact U.conj_Ps

/-- At Brewster collapse, the operator is the surviving amplitude times the core projector. -/
theorem brewster_operator_is_core_amplitude
    (r_s : ℂ) :
    diagonalJones r_s 0 = r_s • Ps :=
  diagonalJones_p_zero r_s

/-- The Brewster operator is phase-Erlanger-invariant. -/
theorem brewster_operator_phaseErlangerInvariant
    (r_s : ℂ) :
    IsPhaseErlangerInvariantOperator (diagonalJones r_s 0) :=
  diagonalJones_phaseErlangerInvariant r_s 0

/-! ## 5. Coordinate covariance boundary -/

/--
General Jones conjugation, intentionally not assumed to preserve the `s/p`
projectors.
-/
structure GeneralJonesConjugation where
  U : JonesOperator
  Uinv : JonesOperator
  U_comp_Uinv :
    U.comp Uinv = LinearMap.id
  Uinv_comp_U :
    Uinv.comp U = LinearMap.id

namespace GeneralJonesConjugation

/-- General conjugation by an arbitrary invertible Jones operator. -/
def conj
    (G : GeneralJonesConjugation)
    (T : JonesOperator) : JonesOperator :=
  G.U.comp (T.comp G.Uinv)

/-- The covariant image of `Ps` under a general Jones conjugation. -/
def transportedCore
    (G : GeneralJonesConjugation) : JonesOperator :=
  G.conj Ps

theorem conj_id (G : GeneralJonesConjugation) :
    G.conj LinearMap.id = LinearMap.id := by
  simpa [conj] using G.U_comp_Uinv

theorem conj_zero (G : GeneralJonesConjugation) :
    G.conj 0 = 0 := by
  simp [conj]

theorem conj_add (G : GeneralJonesConjugation)
    (S T : JonesOperator) :
    G.conj (S + T) = G.conj S + G.conj T := by
  ext x
  simp [conj, LinearMap.comp_apply]

theorem conj_comp (G : GeneralJonesConjugation)
    (S T : JonesOperator) :
    G.conj (S.comp T) = (G.conj S).comp (G.conj T) := by
  apply LinearMap.ext
  intro x
  simp only [conj, LinearMap.comp_apply]
  have h := congrArg (fun f : JonesOperator => f (T (G.Uinv x)))
    G.Uinv_comp_U
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  rw [h]

theorem conj_injective (G : GeneralJonesConjugation) :
    Function.Injective G.conj := by
  intro S T hST
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f : JonesOperator =>
      G.Uinv (f (G.U x))) hST
  simp only [conj, LinearMap.comp_apply] at h
  have hInv : ∀ y, G.Uinv (G.U y) = y := by
    intro y
    have hy := congrArg (fun f : JonesOperator => f y) G.Uinv_comp_U
    simpa [LinearMap.comp_apply, LinearMap.id_apply] using hy
  simp only [hInv] at h
  exact h

theorem commutes_of_conj_eq_self (G : GeneralJonesConjugation)
    (T : JonesOperator) (hT : G.conj T = T) :
    G.U.comp T = T.comp G.U := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f : JonesOperator => f (G.U x)) hT
  simp only [conj, LinearMap.comp_apply] at h
  have hInv : G.Uinv (G.U x) = x := by
    have hx := congrArg (fun f : JonesOperator => f x) G.Uinv_comp_U
    simpa [LinearMap.comp_apply, LinearMap.id_apply] using hx
  rw [hInv] at h
  exact h

theorem conj_eq_self_of_commutes (G : GeneralJonesConjugation)
    (T : JonesOperator) (hT : G.U.comp T = T.comp G.U) :
    G.conj T = T := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f : JonesOperator => f (G.Uinv x)) hT
  simp only [conj, LinearMap.comp_apply] at h ⊢
  have hInv : G.U (G.Uinv x) = x := by
    have hx := congrArg (fun f : JonesOperator => f x) G.U_comp_Uinv
    simpa [LinearMap.comp_apply, LinearMap.id_apply] using hx
  rw [hInv] at h
  exact h

theorem conj_eq_self_iff_commutes (G : GeneralJonesConjugation)
    (T : JonesOperator) :
    G.conj T = T ↔ G.U.comp T = T.comp G.U := by
  constructor
  · exact commutes_of_conj_eq_self G T
  · exact conj_eq_self_of_commutes G T

end GeneralJonesConjugation

end InfoGeometry.Applications.FiniteJonesErlanger
