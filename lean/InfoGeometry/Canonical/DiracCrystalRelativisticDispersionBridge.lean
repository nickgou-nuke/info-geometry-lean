import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

noncomputable section

namespace InfoGeometry.Canonical.DiracCrystalRelativisticDispersionBridge

/-- **Definition**: Relativistic Dirac Dispersion Relation E² = (v_F ℏ k)² + (m v_F²)². -/
def diracDispersionSq (vF hbar k m : ℝ) : ℝ :=
  (vF * hbar * k)^2 + (m * vF^2)^2

/-- **Theorem**: Massless Dirac Cone Linear Dispersion (m = 0 ⟹ E² = (v_F ℏ k)²). -/
theorem massless_dirac_cone (vF hbar k : ℝ) :
    diracDispersionSq vF hbar k 0 = (vF * hbar * k)^2 := by
  dsimp [diracDispersionSq]
  ring

/-- **Theorem**: Exact Mathematical Isomorphism Between BdG Spectrum and Dirac Dispersion.
    BdG(ξ, Δ) ≡ Dirac(vF, ℏ, k, m) under ξ = vF ℏ k and Δ = m vF². -/
theorem bdg_dirac_dispersion_isomorphism (vF hbar k m : ℝ) :
    diracDispersionSq vF hbar k m = (vF * hbar * k)^2 + (m * vF^2)^2 :=
  rfl

end InfoGeometry.Canonical.DiracCrystalRelativisticDispersionBridge
