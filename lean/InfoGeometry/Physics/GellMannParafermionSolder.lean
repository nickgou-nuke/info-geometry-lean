import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain

/-!
# Gell-Mann parafermion solder — theorem-honest carrier

This file keeps only the finite linear-algebraic readout used by downstream
Cantor-boundary examples.  It does not assert an `SU(3)` soldering theorem, a
Bogoliubov theorem, or a parafermion/Cuntz universal-property theorem without
explicit hypotheses.
-/

noncomputable section

namespace InfoGeometry.Physics.GellMannParafermionSolder

/-- Complex `3 × 3` matrices used as color-action coefficients. -/
abbrev M3C := InfoGeometry.Algebra.FiniteSpin.Mat3C

/-- A color spinor with three color components and one singlet component. -/
abbrev ColorSpinor4 (V : Type*) :=
  InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.ColorSpinor4 V

/-- Minimal realization data: three color components and a singlet component in
an arbitrary target carrier. -/
structure ParafermionRealization (V : Type*) where
  color : Fin 3 → V
  singlet : V

/-- Read out the spinor carried by a realization. -/
def realizedParafermionColorSpinor4 {V : Type*} (R : ParafermionRealization V) :
    ColorSpinor4 V :=
  (R.color, R.singlet)

/-- Matrix action on the color lane; the singlet lane is sent to zero. -/
def colorLieAction4 {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (A : M3C) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  (fun i => ∑ j : Fin 3, A i j • ψ.1 j, 0)

/-- The solder readout is the coefficient-matrix action on realized color data. -/
def gellMannParafermionSolder {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (R : ParafermionRealization V) (A : M3C) : ColorSpinor4 V :=
  colorLieAction4 A (realizedParafermionColorSpinor4 R)

/-- Color-coordinate readout for the solder action. -/
theorem gellMannParafermionSolder_color_apply
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (R : ParafermionRealization V) (A : M3C) (i : Fin 3) :
    (gellMannParafermionSolder R A).1 i = ∑ j : Fin 3, A i j • R.color j := by
  rfl

/-- The matrix color action leaves the singlet output at zero by definition. -/
theorem gellMannParafermionSolder_singlet_zero
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (R : ParafermionRealization V) (A : M3C) :
    (gellMannParafermionSolder R A).2 = 0 := by
  rfl

/-- Statement shape for multiplicativity of the ordinary matrix action on the
color lane. -/
def colorLieAction4_mul_statement {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (A B : M3C) (ψ : ColorSpinor4 V) : Prop :=
  colorLieAction4 (A * B) ψ = colorLieAction4 A (colorLieAction4 B ψ)

/-- Statement shape for the additive commutator readout of the ordinary matrix
action. -/
def colorLieAction4_commutator_statement {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : M3C) (ψ : ColorSpinor4 V) : Prop :=
  colorLieAction4 (A * B - B * A) ψ =
    colorLieAction4 A (colorLieAction4 B ψ) -
      colorLieAction4 B (colorLieAction4 A ψ)

/-- Minimal inertial-frame record used by downstream statement surfaces. -/
abbrev BogoliubovInertialFrame :=
  InfoGeometry.Physics.BogoliubovWeylChemicalPotential.BogoliubovInertialFrame

abbrev qRapidity : ℝ → ℂ := InfoGeometry.Physics.SupergradedCuntzBdG.qRapidity

/-- Compatibility name forwarded to the genuine scalar q-braid owner. -/
def qBraid4 {V : Type*} [SMul ℂ V] (q : ℂ) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.qBraid4 q ψ

/-- Compatibility name forwarded to the genuine Bogoliubov frame braid owner. -/
def frameSolderedBraid {V : Type*} [SMul ℂ V]
    (F : BogoliubovInertialFrame) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.frameBraid4 F ψ

/-- The identity braid readout is invariant under changing the scalar frame
parameter. -/
theorem frameSolderedBraid_mu_shift {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (R : ParafermionRealization V) (F : BogoliubovInertialFrame) (δμ : ℝ) :
    frameSolderedBraid { F with μ := F.μ + δμ } (realizedParafermionColorSpinor4 R) =
      qBraid4 (qRapidity (F.β * δμ * F.Q))
        (frameSolderedBraid F (realizedParafermionColorSpinor4 R)) := by
  exact InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.frameBraid4_mu_shift
    F δμ (realizedParafermionColorSpinor4 R)

end InfoGeometry.Physics.GellMannParafermionSolder

end noncomputable section
