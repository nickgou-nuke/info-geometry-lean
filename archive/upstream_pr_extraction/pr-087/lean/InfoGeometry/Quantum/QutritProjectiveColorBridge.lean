import InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
import InfoGeometry.Quantum.Qutrit
import InfoGeometry.Topology.MobiusGeometry
import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Twistor.RollingSpinorMobiusBridge
import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Qutrit projective color bridge

This module separates four projective constructions that must not be conflated:

* the Möbius sphere is `CP¹ = P(ℂ²)`;
* pure qutrit/color rays form `CP² = P(ℂ³)`;
* a color triplet plus a singlet projectivizes to a `CP³` carrier;
* Penrose twistor space is the existing projectivization of `ℂ⁴`, equipped with
  additional signature `(2,2)` geometry in its owner module.

Neither `CP²` nor `CP³` is asserted to cover the Riemann sphere.  A map from
`CP¹` into either higher projective space requires a separately constructed
representation, such as a symmetric-power/Veronese map.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Quantum.QutritProjectiveColorBridge

open InfoGeometry.Quantum.Qutrit
open InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain

/-- Native projective pure-qutrit space: projectivization of the color triplet. -/
abbrev ColorCP2 : Type := ℙ ℂ QutritSpace

/-- The existing four-component color carrier: a color triplet plus one singlet. -/
abbrev ColorSingletCarrier : Type := ColorSpinor4 ℂ

/-- Projectivization of the color-triplet-plus-singlet carrier. -/
abbrev ColorSingletCP3 : Type := ℙ ℂ ColorSingletCarrier

/-- The repository's existing Penrose projective twistor space.  This shares
complex carrier dimension four with `ColorSingletCP3`, but no identification of
its color action with the Penrose `(2,2)` Hermitian geometry is asserted here. -/
abbrev PenroseCP3 : Type :=
  InfoGeometry.Twistor.PenroseTwistor.ProjectiveTwistorSpace

/-- The vector-space carrier underlying `ColorCP2` has complex dimension three. -/
theorem qutritCarrier_finrank : Module.finrank ℂ QutritSpace = 3 := by
  simp [QutritSpace]

/-- The triplet-plus-singlet carrier underlying `ColorSingletCP3` has complex
dimension four. -/
theorem colorSingletCarrier_finrank : Module.finrank ℂ ColorSingletCarrier = 4 := by
  simp [ColorSingletCarrier, ColorSpinor4]

/-- A normalized qutrit state is nonzero. -/
theorem qutritState_ne_zero (ψ : QutritState) : (ψ : QutritSpace) ≠ 0 := by
  intro hψ
  have hnorm : ‖(ψ : QutritSpace)‖ = 1 := mem_sphere_zero_iff_norm.mp ψ.property
  rw [hψ, norm_zero] at hnorm
  norm_num at hnorm

/-- Send a normalized qutrit state to its native projective color ray. -/
def qutritStateRay (ψ : QutritState) : ColorCP2 :=
  Projectivization.mk ℂ (ψ : QutritSpace) (qutritState_ne_zero ψ)

/-- Multiplication by any nonzero complex scalar leaves a projective ray fixed. -/
theorem projectiveRay_smul (c : ℂ) (hc : c ≠ 0) (ψ : QutritSpace) (hψ : ψ ≠ 0) :
    Projectivization.mk ℂ (c • ψ) (smul_ne_zero hc hψ) =
      Projectivization.mk ℂ ψ hψ := by
  rw [Projectivization.mk_eq_mk_iff' ℂ]
  exact ⟨c, rfl⟩

/-- The qutrit global `U(1)` phase is invisible in `ColorCP2`. -/
theorem qutritStateRay_globalPhase (δ : ℝ) (ψ : QutritState) :
    qutritStateRay (globalPhaseAct δ ψ) = qutritStateRay ψ := by
  unfold qutritStateRay
  have hvec :
      ((globalPhaseAct δ ψ : QutritState) : QutritSpace) = phase δ • (ψ : QutritSpace) := by
    exact globalPhaseMatrix_apply δ ψ
  rw [Projectivization.mk_eq_mk_iff' ℂ]
  exact ⟨phase δ, hvec.symm⟩

/-- The commutant of a specified color representation.  The commutant is
representation-relative: without `ρ`, there is no canonical "full-color
commutant" to compute. -/
def ColorRepresentationCommutant {G : Type*}
    (ρ : G → Module.End ℂ QutritSpace) : Set (Module.End ℂ QutritSpace) :=
  {T | ∀ g, T.comp (ρ g) = (ρ g).comp T}

/-- Scalar endomorphisms of the qutrit carrier. -/
def scalarEnd (c : ℂ) : Module.End ℂ QutritSpace :=
  c • LinearMap.id

/-- Scalar endomorphisms commute with every represented color operator. -/
theorem scalarEnd_mem_colorRepresentationCommutant {G : Type*}
    (ρ : G → Module.End ℂ QutritSpace) (c : ℂ) :
    scalarEnd c ∈ ColorRepresentationCommutant ρ := by
  intro g
  apply LinearMap.ext
  intro ψ
  simp [scalarEnd, LinearMap.comp_apply]

end InfoGeometry.Quantum.QutritProjectiveColorBridge
