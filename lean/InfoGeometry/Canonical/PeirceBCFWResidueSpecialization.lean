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
    (q PI : InfoGeometry.Algebra.FiniteSpin.Vec4C) : ℂ :=
  -peirceKinematicForm PI PI /
    (2 * peirceKinematicForm PI q)

theorem peirce_bcfw_algebraic_residue_identity
    {I : Type*} [Fintype I]
    (c : I → ℂ)
    (q : I → InfoGeometry.Algebra.FiniteSpin.Vec4C)
    (PI : I → InfoGeometry.Algebra.FiniteSpin.Vec4C)
    (hq : ∀ i, peirceKinematicForm (q i) (q i) = 0)
    (hslopes : ∀ i, 2 * peirceKinematicForm (PI i) (q i) ≠ 0) :
    (algebraicAmplitude c
        (fun i => peirceChannelPole (q i) (PI i)) 0 =
      - ∑ i, algebraicResidueOverZ c
        (fun i => peirceChannelPole (q i) (PI i)) i) ∧
    (∀ i, peirceKinematicForm
        (shiftedChannel (PI i) (q i) (peirceChannelPole (q i) (PI i)))
        (shiftedChannel (PI i) (q i) (peirceChannelPole (q i) (PI i))) = 0) := by
  constructor
  · exact algebraic_residue_identity c
      (fun i => peirceChannelPole (q i) (PI i))
  · intro i
    unfold peirceChannelPole
    exact bcfw_channel_goes_onShell peirceKinematicForm
      peirceKinematicForm_isSymm (PI i) (q i) (hq i) (hslopes i)

end

end InfoGeometry.Canonical
