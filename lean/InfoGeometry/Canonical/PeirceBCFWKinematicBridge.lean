import InfoGeometry.Canonical.PeirceNullConeKinematicEmbedding
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BCFWOnShellShift

namespace InfoGeometry.Canonical

open Complex
noncomputable section

/-! Complexify the four Peirce channel coordinates and equip them with the
native Mathlib symmetric bilinear form whose diagonal is the channel
quadratic. The BCFW identities consume this form directly. -/

noncomputable def peirceKinematicForm :
    LinearMap.BilinForm ℂ InfoGeometry.Algebra.FiniteSpin.Vec4C :=
  LinearMap.mk₂ ℂ
    (fun p q => (1 / 2 : ℂ) *
      (p 0 * q 1 + p 1 * q 0 - p 2 * q 3 - p 3 * q 2))
    (by intro p q r; simp [Pi.add_apply]; ring)
    (by intro c p q; simp [Pi.smul_apply, smul_eq_mul]; ring)
    (by intro p q r; simp [Pi.add_apply]; ring)
    (by intro c p q; simp [Pi.smul_apply, smul_eq_mul]; ring)

theorem peirceKinematicForm_isSymm : peirceKinematicForm.IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro p q
  simp [peirceKinematicForm, LinearMap.mk₂_apply]
  ring

theorem peirceKinematicForm_self (p : InfoGeometry.Algebra.FiniteSpin.Vec4C) :
    peirceKinematicForm p p =
      p 0 * p 1 - p 2 * p 3 := by
  simp [peirceKinematicForm, LinearMap.mk₂_apply]
  ring

def complexifyChannelCoordinates
    (p : KinematicCoordinates) : InfoGeometry.Algebra.FiniteSpin.Vec4C :=
  fun i => p i

theorem complexifyChannelCoordinates_form_self (p : KinematicCoordinates) :
    peirceKinematicForm (complexifyChannelCoordinates p)
        (complexifyChannelCoordinates p) =
      (channelQuadratic p : ℂ) := by
  rw [peirceKinematicForm_self]
  dsimp [complexifyChannelCoordinates, channelQuadratic]
  norm_num

def complexifiedChannel
    (M : Matrix (Fin 2) (Fin 2) ℝ) : InfoGeometry.Algebra.FiniteSpin.Vec4C :=
  complexifyChannelCoordinates (channelCoordinates M)

theorem complexifiedChannel_peirce_quadratic (M : Matrix (Fin 2) (Fin 2) ℝ) :
    peirceKinematicForm (complexifiedChannel M) (complexifiedChannel M) =
      (splitQuadratic (embedRealSplit M) : ℂ) := by
  unfold complexifiedChannel
  rw [complexifyChannelCoordinates_form_self,
    embedRealSplit_quadratic_transport]

end
end InfoGeometry.Canonical
