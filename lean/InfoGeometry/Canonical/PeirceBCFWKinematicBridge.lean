import InfoGeometry.Canonical.PeirceNullConeKinematicEmbedding
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BCFWOnShellShift

namespace InfoGeometry.Canonical

open Complex
noncomputable section

/-! Complexify the four Peirce channel coordinates and equip them with the
symmetric bilinear form whose diagonal is the channel quadratic.  This is the
minimal typed interface needed to feed the existing BCFW on-shell shift. -/

abbrev PeirceKinematicMomentum := InfoGeometry.Algebra.FiniteSpin.Vec4C

noncomputable def peirceKinematicInner
    (p q : PeirceKinematicMomentum) : ℂ :=
  (1 / 2 : ℂ) *
    (p 0 * q 1 + p 1 * q 0 - p 2 * q 3 - p 3 * q 2)

instance : MomentumSpace PeirceKinematicMomentum where
  inner := peirceKinematicInner
  inner_symm := by
    intro p q
    dsimp [peirceKinematicInner]
    ring
  inner_add_left := by
    intro p q r
    dsimp [peirceKinematicInner]
    ring
  inner_smul_left := by
    intro c p q
    dsimp [peirceKinematicInner]
    ring

theorem peirceKinematicInner_self (p : PeirceKinematicMomentum) :
    peirceKinematicInner p p =
      p 0 * p 1 - p 2 * p 3 := by
  simp [peirceKinematicInner]
  ring

def complexifyChannelCoordinates
    (p : KinematicCoordinates) : PeirceKinematicMomentum :=
  fun i => p i

theorem complexifyChannelCoordinates_inner_self (p : KinematicCoordinates) :
    peirceKinematicInner (complexifyChannelCoordinates p)
        (complexifyChannelCoordinates p) =
      (channelQuadratic p : ℂ) := by
  rw [peirceKinematicInner_self]
  dsimp [complexifyChannelCoordinates, channelQuadratic]
  norm_num

def complexifiedChannel
    (M : Matrix (Fin 2) (Fin 2) ℝ) : PeirceKinematicMomentum :=
  complexifyChannelCoordinates (channelCoordinates M)

theorem complexifiedChannel_peirce_quadratic (M : Matrix (Fin 2) (Fin 2) ℝ) :
    peirceKinematicInner (complexifiedChannel M) (complexifiedChannel M) =
      (splitQuadratic (embedRealSplit M) : ℂ) := by
  unfold complexifiedChannel
  rw [complexifyChannelCoordinates_inner_self,
    embedRealSplit_quadratic_transport]

end
end InfoGeometry.Canonical
