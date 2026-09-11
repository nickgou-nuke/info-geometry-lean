import InfoGeometry.Canonical.ConnesTomitaModularAutomorphismBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics

/-!
# Noncommutative Radon--Nikodym cocycle/KMS bridge

This owner deliberately works in the multiplicative operator algebra.  The
Radon--Nikodym object is unit-valued and its cocycle law is twisted by the
owned modular automorphism flow.  No scalar exponential, commutative density,
or claim about a KMS state is introduced here.

The KMS fields are consumed from `OperatorThermodynamics.KMSState`; this file
only packages their compatibility with the genuine noncommutative cocycle
interface owned by `ConnesTomita`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RadonNikodymCocycleKMSBridge

open InfoGeometry.OperatorAlgebra.OperatorThermodynamics
open ConnesTomita

variable {M : Type*} [AddMonoid M] [Monoid M]

abbrev UnitCocycle (mod : ModularAutomorphism M) :=
  ModularAutomorphism.RadonNikodymCocycle M

/-- The owned noncommutative Connes cocycle law, exposed at a fixed flow. -/
theorem unit_cocycle_chain
    (c : UnitCocycle mod)
    (u : ℝ → Mˣ)
    (t₁ t₂ : ℝ) :
    u (t₁ + t₂) =
      Units.map (mod.flow t₁).toMonoidHom (u t₂) * u t₁ :=
  ModularAutomorphism.cocycle_chain_rule c u mod t₁ t₂

/-- Three-step cocycle reassociation in the noncommutative unit group. -/
theorem unit_cocycle_chain_assoc
    (c : UnitCocycle mod)
    (u : ℝ → Mˣ)
    (t₁ t₂ t₃ : ℝ) :
    u (t₁ + t₂ + t₃) =
      Units.map (mod.flow t₁).toMonoidHom
          (Units.map (mod.flow t₂).toMonoidHom (u t₃) * u t₂) * u t₁ := by
  calc
    u (t₁ + t₂ + t₃) = u (t₁ + (t₂ + t₃)) := by
      congr 1
      ring
    _ = Units.map (mod.flow t₁).toMonoidHom (u (t₂ + t₃)) * u t₁ := by
      rw [unit_cocycle_chain c u t₁ (t₂ + t₃)]
    _ = Units.map (mod.flow t₁).toMonoidHom
          (Units.map (mod.flow t₂).toMonoidHom (u t₃) * u t₂) * u t₁ := by
      rw [unit_cocycle_chain c u t₂ t₃]

/-- A typed package carrying both a genuine KMS boundary state and a unit
Connes cocycle for the same modular flow. -/
structure KMSCocycleData
    (mod : ModularAutomorphism M) (beta : ℝ) where
  state : KMSState M mod beta
  cocycle : UnitCocycle mod

namespace KMSCocycleData

variable {mod : ModularAutomorphism M} {beta : ℝ}

theorem lower_boundary
    (D : KMSCocycleData mod beta)
    (A B : M) (t : ℝ) :
    D.state.correlation A B (t : ℂ) =
      D.state.state.eval (A * mod.flow t B) :=
  D.state.correlation_lower_boundary A B t

theorem upper_boundary
    (D : KMSCocycleData mod beta)
    (A B : M) (t : ℝ) :
    D.state.correlation A B ((t : ℂ) + (beta : ℂ) * Complex.I) =
      D.state.state.eval (mod.flow t B * A) :=
  D.state.correlation_upper_boundary A B t

theorem cocycle_chain
    (D : KMSCocycleData mod beta)
    (u : ℝ → Mˣ) (t₁ t₂ : ℝ) :
    u (t₁ + t₂) =
      Units.map (mod.flow t₁).toMonoidHom (u t₂) * u t₁ :=
  D.cocycle mod t₁ t₂ u

end KMSCocycleData

end InfoGeometry.OperatorAlgebra.RadonNikodymCocycleKMSBridge
