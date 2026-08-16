import InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-!
# Compatibility readout for the algebraic neutral dual pair

The native owner is `NeutralPhaseSpaceCore`: it owns the carrier
`E × Module.Dual ℝ E`, the canonical neutral bilinear form, the unscaled
quadratic form, and the para/Krein-type skew form.  This file exports the
short names used by the canonical neutral-pair bridge files without defining
a second carrier or a second quadratic form.
-/

namespace InfoGeometry.Canonical.NeutralDualPair

noncomputable section

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

abbrev Dual (U : Type*) [AddCommGroup U] [Module ℝ U] :=
  Module.Dual ℝ U

abbrev Neutral (U : Type*) [AddCommGroup U] [Module ℝ U] :=
  PhaseSpaceCarrier U

def eta (x y : Neutral U) : ℝ :=
  canonicalNeutralBilin x y

def paraK : Neutral U →ₗ[ℝ] Neutral U :=
  neutralParaInvolution

@[simp] theorem paraK_apply (x : Neutral U) :
    paraK x = (x.1, -x.2) := by
  rfl

theorem paraK_square :
    paraK.comp paraK = (LinearMap.id : Neutral U →ₗ[ℝ] Neutral U) := by
  exact neutralParaInvolution_sq

theorem eta_paraK_paraK (x y : Neutral U) :
    eta (paraK x) (paraK y) = -eta x y := by
  exact canonicalNeutralBilin_para_anti_isometry x y

def omega (x y : Neutral U) : ℝ :=
  neutralOmega x y

@[simp] theorem omega_apply (x y : Neutral U) :
    omega x y = y.2 x.1 - x.2 y.1 := by
  exact neutralOmega_apply x y

theorem omega_skew (x y : Neutral U) :
    omega y x = -omega x y := by
  rw [omega_apply, omega_apply]
  ring

def neutralBilin : LinearMap.BilinForm ℝ (Neutral U) :=
  (1 / 2 : ℝ) • canonicalNeutralBilin

@[simp] theorem neutralBilin_apply (x y : Neutral U) :
    neutralBilin x y = (1 / 2 : ℝ) * eta x y := by
  rfl

def neutralQ : QuadraticForm ℝ (Neutral U) :=
  canonicalNeutralFormUnscaled

@[simp] theorem neutralQ_apply (x : Neutral U) :
    neutralQ x = x.2 x.1 := by
  exact canonicalNeutralFormUnscaled_apply x

theorem neutralQ_polar (x y : Neutral U) :
    QuadraticMap.polar neutralQ x y = eta x y := by
  exact canonicalNeutralFormUnscaled_polar x y

theorem eta_first_isotropic (u v : U) :
    eta ((u, 0) : Neutral U) (v, 0) = 0 := by
  simp [eta, canonicalNeutralBilin_apply]

theorem eta_dual_isotropic (α β : Dual U) :
    eta ((0, α) : Neutral U) (0, β) = 0 := by
  simp [eta, canonicalNeutralBilin_apply]

end

end InfoGeometry.Canonical.NeutralDualPair
