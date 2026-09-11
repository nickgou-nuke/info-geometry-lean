import InfoGeometry.Canonical.PeirceBCFWKinematicBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-! A small specialization layer connecting the Peirce coordinate carrier to
the generic BCFW shift API.  The hypotheses are explicit: this file does not
invent a shift vector or identify a physical momentum space. -/

structure PeirceBCFWShiftParameters where
  pi : PeirceKinematicMomentum
  pj : PeirceKinematicMomentum
  q : PeirceKinematicMomentum
  pi_null : peirceKinematicInner pi pi = 0
  pj_null : peirceKinematicInner pj pj = 0
  q_null : peirceKinematicInner q q = 0
  pi_ortho_q : peirceKinematicInner pi q = 0
  pj_ortho_q : peirceKinematicInner pj q = 0

def PeirceBCFWShiftParameters.toBCFWShiftData
    (data : PeirceBCFWShiftParameters) : BCFWShiftData PeirceKinematicMomentum :=
  { pi := data.pi
    pj := data.pj
    q := data.q
    pi_null := data.pi_null
    pj_null := data.pj_null
    q_null := data.q_null
    pi_ortho_q := data.pi_ortho_q
    pj_ortho_q := data.pj_ortho_q }

theorem complexifiedChannel_isOnShell
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : splitQuadratic (embedRealSplit M) = 0) :
    peirceKinematicInner (complexifiedChannel M)
        (complexifiedChannel M) = 0 := by
  rw [complexifiedChannel_peirce_quadratic]
  exact_mod_cast hM

theorem peirce_bcfw_shift_left_null
    (data : PeirceBCFWShiftParameters) (z : ℂ) :
    peirceKinematicInner
        (shiftedPi data.toBCFWShiftData z)
        (shiftedPi data.toBCFWShiftData z) = 0 := by
  exact bcfw_shift_left_null data.toBCFWShiftData z

theorem peirce_bcfw_shift_right_null
    (data : PeirceBCFWShiftParameters) (z : ℂ) :
    peirceKinematicInner
        (shiftedPj data.toBCFWShiftData z)
        (shiftedPj data.toBCFWShiftData z) = 0 := by
  exact bcfw_shift_right_null data.toBCFWShiftData z

theorem peirce_bcfw_shift_momentum_conservation
    (data : PeirceBCFWShiftParameters) (z : ℂ) :
    shiftedPi data.toBCFWShiftData z + shiftedPj data.toBCFWShiftData z =
      data.pi + data.pj := by
  exact bcfw_shift_momentum_conservation data.toBCFWShiftData z

theorem peirce_bcfw_channel_goes_onShell
    (data : PeirceBCFWShiftParameters)
    (PI : PeirceKinematicMomentum)
    (hslope : 2 * peirceKinematicInner PI data.q ≠ 0) :
    peirceKinematicInner
        (shiftedChannel data.toBCFWShiftData PI
          (-peirceKinematicInner PI PI /
            (2 * peirceKinematicInner PI data.q)))
        (shiftedChannel data.toBCFWShiftData PI
          (-peirceKinematicInner PI PI /
            (2 * peirceKinematicInner PI data.q))) = 0 := by
  exact bcfw_channel_goes_onShell data.toBCFWShiftData PI hslope

end InfoGeometry.Canonical
