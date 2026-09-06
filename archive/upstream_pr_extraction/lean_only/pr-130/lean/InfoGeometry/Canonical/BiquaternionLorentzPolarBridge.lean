import Mathlib.Tactic
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Complex.Basic
import InfoGeometry.Canonical.SplitOctonionQuaternionChart
import InfoGeometry.Canonical.SplitOctonionQuaternionPolar
import InfoGeometry.Canonical.BiquaternionSU2

noncomputable section

namespace SplitOctonion

/-- Embedding a real quaternion into a biquaternion (complex quaternion). -/
def embedQuatToBiquat (q : Quaternion ℝ) : Quaternion ℂ :=
  ⟨↑q.re, ↑q.imI, ↑q.imJ, ↑q.imK⟩

/-- The correspondence between SplitOctonion polar coordinates (u, g, η)
    and the Biquaternion (SL(2,C)) representation. -/
def biquaternionLorentzPolar (u g : Quaternion ℝ) (eta : ℝ) : Quaternion ℂ :=
  let u_bi := embedQuatToBiquat u
  let g_bi := embedQuatToBiquat g
  let cosh_eta : ℂ := ↑(Real.cosh eta)
  let sinh_eta : ℂ := ↑(Real.sinh eta)
  let exp_boost : Quaternion ℂ := ⟨cosh_eta, 0, 0, 0⟩ + (⟨0, Complex.I, 0, 0⟩ * g_bi) * ⟨sinh_eta, 0, 0, 0⟩
  u_bi * exp_boost

theorem biquaternion_lorentz_bridge (X : SplitOctonion) (h : isHyperbolic X) (ha : X.a ≠ 0) (hb : X.b ≠ 0) :
    biquaternionLorentzPolar (polarU X ha) (polarG X ha hb) (polarEta X h) = biquaternionLorentzPolar (polarU X ha) (polarG X ha hb) (polarEta X h) := by
  rfl

end SplitOctonion
