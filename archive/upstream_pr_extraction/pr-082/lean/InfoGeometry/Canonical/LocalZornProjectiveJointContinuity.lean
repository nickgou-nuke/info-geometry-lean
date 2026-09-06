import Mathlib
import InfoGeometry.Canonical.LocalZornProjectiveContinuity

namespace InfoGeometry.Canonical

open scoped LinearAlgebra.Projectivization

/-!
Joint continuity of the canonical local `SL₂(ℝ)` action.  The quotient is
taken only in the projective-point argument; the matrix parameter remains an
ordinary finite-dimensional real parameter.
-/

noncomputable def localSL2ProjectiveActionJoint :
    SL2R × RealProjectiveBoundary → RealProjectiveBoundary :=
  fun p => localSL2ProjectiveAction p.1 p.2

noncomputable instance realTwoByTwoMatrixLocallyCompact :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  Pi.locallyCompactSpace_of_finite

noncomputable instance realSL2LocallyCompact : LocallyCompactSpace SL2R := by
  exact (Topology.IsClosedEmbedding.subtypeVal
    (isClosed_eq (by fun_prop) continuous_const)).locallyCompactSpace

theorem continuous_localSL2ProjectiveAction_joint :
    Continuous localSL2ProjectiveActionJoint := by
  exact Topology.IsQuotientMap.continuous_lift_prod_right
    (isQuotientMap_quotient_mk' :
      Topology.IsQuotientMap
        (Quotient.mk' :
          {v : Fin 2 → ℝ // v ≠ 0} → RealProjectiveBoundary)) (by
      let lift : SL2R × {v : Fin 2 → ℝ // v ≠ 0} →
          {v : Fin 2 → ℝ // v ≠ 0} := fun p =>
        ⟨p.1.toLin'.toLinearMap p.2,
          by
            intro hzero
            apply p.2.2
            apply p.1.toLin'.injective
            simpa using hzero⟩
      have hlift : Continuous lift := by
        apply Continuous.subtype_mk
        change Continuous (fun p : SL2R × {v : Fin 2 → ℝ // v ≠ 0} =>
          Matrix.toLin' (p.1 : Matrix (Fin 2) (Fin 2) ℝ) p.2)
        simp only [Matrix.toLin'_apply', Matrix.mulVecLin_apply]
        fun_prop
      have hquot : Continuous (fun p => Quotient.mk' (lift p)) :=
        continuous_quotient_mk'.comp hlift
      simpa [localSL2ProjectiveActionJoint, localSL2ProjectiveAction,
        Projectivization.map, lift] using hquot)

theorem continuous_modularBoostProjectiveAction_joint :
    Continuous (fun p : ℝ × RealProjectiveBoundary =>
      modularBoostProjectiveAction p.1 p.2) := by
  have hboost : Continuous (fun s : ℝ => modularBoostSL2 s) := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [modularBoostSL2] <;> fun_prop
  exact continuous_localSL2ProjectiveAction_joint.comp
    ((hboost.comp continuous_fst).prodMk continuous_snd)

end InfoGeometry.Canonical
