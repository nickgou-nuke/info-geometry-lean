import InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological commutator data for the noncommutative spectral metric

The supremum owner defines the Connes distance set-theoretically.  This owner
supplies the missing topological interface: multiplication and subtraction in
the normed algebra make the commutator continuous, hence its norm is a
continuous real readout and the Lip-1 ball is closed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConnesNCSpectralDistanceTopCat

open CategoryTheory
open InfoGeometry.Canonical.CuntzConnesSpectralDistance
open InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum

variable {A : Type*} [NormedRing A]

def commutatorTopCatHom (D : A) :
    TopCat.of A ⟶ TopCat.of A :=
  TopCat.ofHom
    { toFun := CuntzConnesSpectralDistance.commutator D
      continuous_toFun := by
        have hleft : Continuous (fun a : A => D * a) :=
          continuous_const.mul continuous_id
        have hright : Continuous (fun a : A => a * D) :=
          continuous_id.mul continuous_const
        simpa [CuntzConnesSpectralDistance.commutator] using hleft.sub hright }

@[simp] theorem commutatorTopCatHom_apply (D a : A) :
    commutatorTopCatHom D a = CuntzConnesSpectralDistance.commutator D a :=
  rfl

def commutatorNormContinuousMap (D : A) : ContinuousMap A ℝ :=
  { toFun := CuntzConnesSpectralDistance.commutatorNorm D
    continuous_toFun := by
      exact continuous_norm.comp
        (commutatorTopCatHom D).hom.continuous }

@[simp] theorem commutatorNormContinuousMap_apply (D a : A) :
    commutatorNormContinuousMap D a =
      CuntzConnesSpectralDistance.commutatorNorm D a :=
  rfl

theorem lipSet_closed (D : A) :
    IsClosed (LipSet D) := by
  change IsClosed {a : A |
    CuntzConnesSpectralDistance.commutatorNorm D a ≤ 1}
  exact isClosed_le
    (commutatorNormContinuousMap D).continuous
    continuous_const

end InfoGeometry.Canonical.ConnesNCSpectralDistanceTopCat
