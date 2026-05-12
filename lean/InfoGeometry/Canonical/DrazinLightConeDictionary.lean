import InfoGeometry.Meta.Architecture
import Mathlib

/-!
# InfoGeometry.Canonical.DrazinLightConeDictionary

Generic ring-level Drazin/light-cone dictionary.

This file is deliberately independent of Type III analytic claims.  It proves
the finite/bounded algebraic kernel used by the certified inverse-kernel lane:

* a projector split `P + P₀ = 1`;
* off-diagonal arrows `u⁺(X) = P X P₀` and `u⁻(X) = P₀ X P`;
* commutator with `P` is the difference of these arrows;
* same-direction arrow products vanish from projector orthogonality.

Concrete Drazin/Moore--Penrose owner data remain in `CertifiedInverseKernel`
and `DrazinSupercharge`.  Type III realization, if any, is a separate analytic
witness and is not asserted here.
-/

namespace InfoGeometry.Canonical.DrazinLightConeDictionary

/-- Ring commutator. -/
@[rep_depth operator]
def commutator {A : Type*} [Ring A] (X Y : A) : A :=
  X * Y - Y * X

/--
A two-projector split `P + P₀ = 1`.

This is the abstract algebraic substrate of a regular/defect split.
-/
@[rep_depth operator]
structure ProjectorSplit (A : Type*) [Ring A] where
  P : A
  P0 : A
  P_idem : P * P = P
  P0_idem : P0 * P0 = P0
  P_add_P0 : P + P0 = 1
  P_mul_P0 : P * P0 = 0
  P0_mul_P : P0 * P = 0

namespace ProjectorSplit

variable {A : Type*} [Ring A]
variable (S : ProjectorSplit A)

/-- Off-diagonal arrow from defect sector to regular sector. -/
@[rep_depth operator]
def uPlus (X : A) : A :=
  S.P * X * S.P0

/-- Off-diagonal arrow from regular sector to defect sector. -/
@[rep_depth operator]
def uMinus (X : A) : A :=
  S.P0 * X * S.P

/--
Commutator with the regular projector is exactly the difference of the two
off-diagonal light-cone arrows.
-/
@[rep_depth operator]
theorem commutator_P_eq_uPlus_sub_uMinus (X : A) :
    commutator S.P X = S.uPlus X - S.uMinus X := by
  unfold commutator uPlus uMinus
  calc
    S.P * X - X * S.P
        = S.P * X * 1 - 1 * X * S.P := by
            simp
    _ = S.P * X * (S.P + S.P0) - (S.P + S.P0) * X * S.P := by
            rw [S.P_add_P0]
    _ = (S.P * X * S.P + S.P * X * S.P0)
          - (S.P * X * S.P + S.P0 * X * S.P) := by
            noncomm_ring
    _ = S.P * X * S.P0 - S.P0 * X * S.P := by
            noncomm_ring

/-- Same-arrow `u⁺` composition vanishes. -/
@[rep_depth operator]
theorem uPlus_mul_uPlus_eq_zero (X Y : A) :
    S.uPlus X * S.uPlus Y = 0 := by
  unfold uPlus
  calc
    (S.P * X * S.P0) * (S.P * Y * S.P0)
        = S.P * X * (S.P0 * S.P) * Y * S.P0 := by
            noncomm_ring
    _ = 0 := by
            rw [S.P0_mul_P]
            simp

/-- Same-arrow `u⁻` composition vanishes. -/
@[rep_depth operator]
theorem uMinus_mul_uMinus_eq_zero (X Y : A) :
    S.uMinus X * S.uMinus Y = 0 := by
  unfold uMinus
  calc
    (S.P0 * X * S.P) * (S.P0 * Y * S.P)
        = S.P0 * X * (S.P * S.P0) * Y * S.P := by
            noncomm_ring
    _ = 0 := by
            rw [S.P_mul_P0]
            simp

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
  chiR_law : chiR = commutator split.P PR
  chiL_law : chiL = commutator split.P PL
  Q : A
  Q_law : Q = chiR - chiL

namespace DrazinMPHorizonDatum

variable {A : Type*} [Ring A]
variable (H : DrazinMPHorizonDatum A)

/-- Right/range anomaly as light-cone off-diagonal mismatch of `PR`. -/
@[rep_depth operator]
theorem chiR_eq_uPlus_sub_uMinus :
    H.chiR = H.split.uPlus H.PR - H.split.uMinus H.PR := by
  rw [H.chiR_law]
  exact H.split.commutator_P_eq_uPlus_sub_uMinus H.PR

/-- Left/domain anomaly as light-cone off-diagonal mismatch of `PL`. -/
@[rep_depth operator]
theorem chiL_eq_uPlus_sub_uMinus :
    H.chiL = H.split.uPlus H.PL - H.split.uMinus H.PL := by
  rw [H.chiL_law]
  exact H.split.commutator_P_eq_uPlus_sub_uMinus H.PL

/-- The supercharge is the net light-cone mismatch current. -/
@[rep_depth operator]
theorem Q_eq_net_lightcone_mismatch :
    H.Q =
      (H.split.uPlus H.PR - H.split.uMinus H.PR)
        - (H.split.uPlus H.PL - H.split.uMinus H.PL) := by
  rw [H.Q_law, H.chiR_eq_uPlus_sub_uMinus, H.chiL_eq_uPlus_sub_uMinus]

end DrazinMPHorizonDatum

end InfoGeometry.Canonical.DrazinLightConeDictionary
