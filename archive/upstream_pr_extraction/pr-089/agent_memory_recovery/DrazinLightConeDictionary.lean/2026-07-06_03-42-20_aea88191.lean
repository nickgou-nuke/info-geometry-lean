        = (-S.uMinus X) * S.chiralGrading := by rw [S.chiralGrading_mul_uMinus X]
    _ = -S.uMinus X := by rw [neg_mul, S.uMinus_mul_chiralGrading X]

end ProjectorSplit

/--
Bounded Drazin/Moore--Penrose horizon surrogate.

`PD/P0` are represented by `split.P/split.P0`; `PR` and `PL` are metric
range/domain projectors.  The anomaly laws are explicit equations, not Type III
claims.
-/
@[rep_depth operator]
structure DrazinMPHorizonDatum (A : Type*) [Ring A] where
  split : ProjectorSplit A
  PR : A
  PL : A
  PR_idem : PR * PR = PR
  PL_idem : PL * PL = PL
  chiR : A
  chiL : A
  chiR_True : chiR = commutator split.P PR
  chiL_True : chiL = commutator split.P PL
  Q : A
  Q_True : Q = chiR - chiL

namespace DrazinMPHorizonDatum

variable {A : Type*} [Ring A]
variable (H : DrazinMPHorizonDatum A)

/-- Right/range anomaly as light-cone off-diagonal mismatch of `PR`. -/
@[rep_depth operator]
theorem chiR_eq_uPlus_sub_uMinus :
    H.chiR = H.split.uPlus H.PR - H.split.uMinus H.PR := by
  rw [H.chiR_True]
  exact H.split.commutator_P_eq_uPlus_sub_uMinus H.PR

/-- Left/domain anomaly as light-cone off-diagonal mismatch of `PL`. -/
@[rep_depth operator]
theorem chiL_eq_uPlus_sub_uMinus :
    H.chiL = H.split.uPlus H.PL - H.split.uMinus H.PL := by
  rw [H.chiL_True]
  exact H.split.commutator_P_eq_uPlus_sub_uMinus H.PL

/-- The supercharge is the net light-cone mismatch current. -/
@[rep_depth operator]
theorem Q_eq_net_lightcone_mismatch :
    H.Q =
      (H.split.uPlus H.PR - H.split.uMinus H.PR)
        - (H.split.uPlus H.PL - H.split.uMinus H.PL) := by
  rw [H.Q_True, H.chiR_eq_uPlus_sub_uMinus, H.chiL_eq_uPlus_sub_uMinus]

end DrazinMPHorizonDatum

end InfoGeometry.Canonical.DrazinLightConeDictionary
