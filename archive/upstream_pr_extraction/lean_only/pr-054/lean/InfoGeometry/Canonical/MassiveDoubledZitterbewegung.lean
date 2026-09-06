import InfoGeometry.Canonical.RealBdG

/-!
# Massive doubled oscillator

The canonical doubled/BdG carrier already has a square-minus-one axis
`modularK`.  This owner records the finite algebraic mass-dependent generator
`D ω = ω K`.  It proves the generator square and the resulting second-order
equation; it does not assert an observable-level Zitterbewegung frequency.
-/

namespace InfoGeometry.Canonical.MassiveDoubledZitterbewegung

open InfoGeometry.Canonical.RealBdG
open InfoGeometry.Krein

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The mass/frequency-scaled doubled oscillator generator. -/
noncomputable def massiveGenerator (ω : ℝ) : EndH (E := E) :=
  ω • modularK (E := E)

omit [CompleteSpace E] in
@[simp] theorem massiveGenerator_apply (ω : ℝ) (v : DoubledSpace E) :
    massiveGenerator (E := E) ω v = ω • modularK (E := E) v := by
  rfl

/-- The massive doubled generator has the expected square. -/
theorem massiveGenerator_sq (ω : ℝ) :
    (massiveGenerator (E := E) ω).comp
        (massiveGenerator (E := E) ω) =
      (-(ω ^ 2)) • ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro v
  change ω • modularK (E := E) (ω • modularK (E := E) v) =
    -(ω ^ 2) • v
  rw [map_smul, modularK_apply_modularK]
  module

/-- Right-hand side of the finite first-order doubled flow. -/
noncomputable def firstOrderRhs (ω : ℝ) (ψ : DoubledSpace E) : DoubledSpace E :=
  massiveGenerator (E := E) ω ψ

/-- Every state satisfies the algebraic second-order equation induced by the
massive generator. -/
theorem massive_second_order (ω : ℝ) (v : DoubledSpace E) :
    massiveGenerator (E := E) ω
        (massiveGenerator (E := E) ω v) =
      -(ω ^ 2) • v := by
  have h := congrArg
    (fun T : EndH (E := E) => T v) (massiveGenerator_sq (E := E) ω)
  simpa using h

end

end InfoGeometry.Canonical.MassiveDoubledZitterbewegung
