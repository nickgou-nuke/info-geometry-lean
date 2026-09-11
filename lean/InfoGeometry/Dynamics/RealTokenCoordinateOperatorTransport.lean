import InfoGeometry.Dynamics.RealTokenCoordinateEquivalence
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Transport of the realified token generator to explicit coordinates

This is the canonical conjugation bridge from the realified operator carrier
to its coordinate carrier.  It makes the non-unitary total generator visible
in real coordinates while preserving its operator meaning.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

abbrev RealCoordinateOperator :=
  RealTokenCoordinates (V := V) →ₗ[ℝ] RealTokenCoordinates (V := V)

def transportRealTokenOperator (T : RealTokenOperator (V := V)) :
    RealCoordinateOperator (V := V) :=
  (realTokenCoordinateEquiv (V := V)).toLinearMap.comp
    (T.comp (realTokenCoordinateEquiv (V := V)).symm.toLinearMap)

@[simp] theorem transportRealTokenOperator_apply
    (T : RealTokenOperator (V := V))
    (c : RealTokenCoordinates (V := V)) :
    transportRealTokenOperator T c =
      realTokenCoordinateEquiv (T (realTokenCoordinateEquiv.symm c)) := rfl

theorem transportRealTokenOperator_conjugate
    (T : RealTokenOperator (V := V)) :
    transportRealTokenOperator T =
      (realTokenCoordinateEquiv (V := V)).toLinearMap.comp
        (T.comp (realTokenCoordinateEquiv (V := V)).symm.toLinearMap) := rfl

theorem transportRealTokenOperator_add
    (T U : RealTokenOperator (V := V)) :
    transportRealTokenOperator (T + U) =
      transportRealTokenOperator T + transportRealTokenOperator U := by
  apply LinearMap.ext
  intro c
  funext i
  change realTokenCoordinateEquiv ((T + U) (realTokenCoordinateEquiv.symm c)) i =
    realTokenCoordinateEquiv (T (realTokenCoordinateEquiv.symm c)) i +
      realTokenCoordinateEquiv (U (realTokenCoordinateEquiv.symm c)) i
  change realTokenCoordinateEquiv
      (T (realTokenCoordinateEquiv.symm c) + U (realTokenCoordinateEquiv.symm c)) i = _
  rw [realTokenCoordinateEquiv.map_add]
  rfl

theorem transportRealTokenOperator_real_smul
    (r : ℝ) (T : RealTokenOperator (V := V)) :
    transportRealTokenOperator (r • T) =
      r • transportRealTokenOperator T := by
  apply LinearMap.ext
  intro c
  funext i
  change realTokenCoordinateEquiv (r • T (realTokenCoordinateEquiv.symm c)) i =
    (r • realTokenCoordinateEquiv (T (realTokenCoordinateEquiv.symm c))) i
  rw [map_smul]

theorem transportRealTokenOperator_comp
    (T U : RealTokenOperator (V := V)) :
    transportRealTokenOperator (T.comp U) =
      (transportRealTokenOperator T).comp (transportRealTokenOperator U) := by
  apply LinearMap.ext
  intro c
  funext i
  change realTokenCoordinateEquiv
      (T (U (realTokenCoordinateEquiv.symm c))) i =
    realTokenCoordinateEquiv
      (T (realTokenCoordinateEquiv.symm
        (realTokenCoordinateEquiv (U (realTokenCoordinateEquiv.symm c))))) i
  rw [realTokenCoordinateEquiv.symm_apply_apply]

theorem transportRealTokenOperator_commutator
    (T U : RealTokenOperator (V := V)) :
    transportRealTokenOperator (T.comp U - U.comp T) =
      (transportRealTokenOperator T).comp (transportRealTokenOperator U) -
        (transportRealTokenOperator U).comp (transportRealTokenOperator T) := by
  apply LinearMap.ext
  intro c
  funext i
  change realTokenCoordinateEquiv
      ((T.comp U - U.comp T) (realTokenCoordinateEquiv.symm c)) i = _
  change realTokenCoordinateEquiv
      (T (U (realTokenCoordinateEquiv.symm c)) -
        U (T (realTokenCoordinateEquiv.symm c))) i = _
  change realTokenCoordinateEquiv
      (T (U (realTokenCoordinateEquiv.symm c)) -
        U (T (realTokenCoordinateEquiv.symm c))) i =
      realTokenCoordinateEquiv (T (U (realTokenCoordinateEquiv.symm c))) i -
        realTokenCoordinateEquiv (U (T (realTokenCoordinateEquiv.symm c))) i
  exact congrArg (fun f => f i)
    (realTokenCoordinateEquiv.map_sub
      (T (U (realTokenCoordinateEquiv.symm c)))
      (U (T (realTokenCoordinateEquiv.symm c))))


def transportedRealifiedTotalTokenGenerator
    (gen : TokenGenerator (V := V)) : RealCoordinateOperator (V := V) :=
  transportRealTokenOperator (realifiedTotalTokenGenerator gen)

theorem transportedRealifiedTotalTokenGenerator_apply
    (gen : TokenGenerator (V := V))
    (c : RealTokenCoordinates (V := V)) :
    transportedRealifiedTotalTokenGenerator gen c =
      realTokenCoordinateEquiv
        (realifiedTotalTokenGenerator gen
          (realTokenCoordinateEquiv.symm c)) := rfl

theorem transportedRealifiedTotalTokenGenerator_eq_transport
    (gen : TokenGenerator (V := V)) :
    transportedRealifiedTotalTokenGenerator gen =
      transportRealTokenOperator (realifiedTotalTokenGenerator gen) := rfl

end
end InfoGeometry.Dynamics
