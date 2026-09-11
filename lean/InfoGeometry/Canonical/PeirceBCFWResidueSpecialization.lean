import InfoGeometry.Canonical.PeirceBCFWShiftSpecialization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BCFWMeromorphicResidueRecursion

open scoped BigOperators

namespace InfoGeometry.Canonical

noncomputable section

/-! A typed interface between the Peirce channel pole and the existing finite
partial-fraction residue model.  The latter remains explicitly algebraic: no
analytic continuation or contour theorem is asserted here. -/

def peirceChannelPole
    (data : PeirceBCFWShiftParameters)
    (PI : PeirceKinematicMomentum) : ℂ :=
  -peirceKinematicInner PI PI /
    (2 * peirceKinematicInner PI data.q)

theorem peirceChannelPole_isOnShell
    (data : PeirceBCFWShiftParameters)
    (PI : PeirceKinematicMomentum)
    (hslope : 2 * peirceKinematicInner PI data.q ≠ 0) :
    peirceKinematicInner
        (shiftedChannel data.toBCFWShiftData PI
          (peirceChannelPole data PI))
        (shiftedChannel data.toBCFWShiftData PI
          (peirceChannelPole data PI)) = 0 := by
  unfold peirceChannelPole
  exact peirce_bcfw_channel_goes_onShell data PI hslope

theorem peirce_bcfw_algebraic_residue_identity
    {I : Type*} [Fintype I]
    (c : I → ℂ)
    (data : I → PeirceBCFWShiftParameters)
    (PI : I → PeirceKinematicMomentum)
    (hslopes : ∀ i, 2 * peirceKinematicInner (PI i) (data i).q ≠ 0)
    (hpoles_nonzero : ∀ i, peirceChannelPole (data i) (PI i) ≠ 0) :
    (algebraicAmplitude c
        (fun i => peirceChannelPole (data i) (PI i)) 0 =
      - ∑ i, algebraicResidueOverZ c
        (fun i => peirceChannelPole (data i) (PI i)) i) ∧
    (∀ i, peirceKinematicInner
        (shiftedChannel (data i).toBCFWShiftData (PI i)
          (peirceChannelPole (data i) (PI i)))
        (shiftedChannel (data i).toBCFWShiftData (PI i)
          (peirceChannelPole (data i) (PI i))) = 0) := by
  constructor
  · exact algebraic_residue_identity c
      (fun i => peirceChannelPole (data i) (PI i)) hpoles_nonzero
  · intro i
    exact peirceChannelPole_isOnShell (data i) (PI i) (hslopes i)

end

end InfoGeometry.Canonical
