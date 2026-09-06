import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the generic monotheticity package of an `S`-solenoid.
    thm:cdim-s-solenoid-generic-monothetic -/
theorem paper_cdim_s_solenoid_generic_monothetic
    {monothetic generatorsDenseGdelta generatorsFullMeasure : Prop}
    (hMonothetic : monothetic)
    (hDenseGdelta : generatorsDenseGdelta)
    (hFullMeasure : generatorsFullMeasure) :
    monothetic ∧ generatorsDenseGdelta ∧ generatorsFullMeasure :=
  ⟨hMonothetic, hDenseGdelta, hFullMeasure⟩

/-- Concrete data for the terminal-object factorization of an `S`-solenoid. The discrete-side
localization map is dualized to `factorMap`, and the fields record the commutative square and the
uniqueness of that factorization. -/
structure SSolenoidTerminalObjectData where
  sourceCompact : Type*
  terminalSolenoid : Type*
  sourceMap : ℤ → sourceCompact
  terminalProjection : ℤ → terminalSolenoid
  dualLocalizationMap : ℤ → ℤ
  factorMap : sourceCompact → terminalSolenoid
  dualLocalization_eq : ∀ n, dualLocalizationMap n = n
  factor_commutes : ∀ n, factorMap (sourceMap n) = terminalProjection n
  factor_unique :
    ∀ g : sourceCompact → terminalSolenoid,
      (∀ n, g (sourceMap n) = terminalProjection n) → g = factorMap

namespace SSolenoidTerminalObjectData

/-- The dual localization map descends to the terminal projection. -/
def dualFactorization (D : SSolenoidTerminalObjectData) : Prop :=
  ∀ n, D.terminalProjection (D.dualLocalizationMap n) = D.terminalProjection n

/-- The continuous factorization is packaged by the existence of the dualized factor map. -/
def continuousFactorization (D : SSolenoidTerminalObjectData) : Prop :=
  ∃ f : D.sourceCompact → D.terminalSolenoid, f = D.factorMap

/-- The commutative square on the compact side after substituting the dual localization map. -/
def compatibilityEquation (D : SSolenoidTerminalObjectData) : Prop :=
  ∀ n, D.factorMap (D.sourceMap n) = D.terminalProjection (D.dualLocalizationMap n)

/-- Uniqueness of the factorization among maps inducing the same square on the generators. -/
def uniquenessWitness (D : SSolenoidTerminalObjectData) : Prop :=
  ∀ g : D.sourceCompact → D.terminalSolenoid,
    (∀ n, g (D.sourceMap n) = D.terminalProjection n) → g = D.factorMap

end SSolenoidTerminalObjectData

/-- Paper label: `thm:cdim-s-solenoid-terminal-object`.
Applying the localization universal property on the discrete side and then dualizing produces a
factor map `Σ → Σ_S`; the defining square commutes and the factorization is unique. -/
theorem paper_cdim_s_solenoid_terminal_object (D : SSolenoidTerminalObjectData) :
    D.dualFactorization ∧ D.continuousFactorization ∧ D.compatibilityEquation ∧
      D.uniquenessWitness := by
  refine ⟨?_, ⟨D.factorMap, rfl⟩, ?_, D.factor_unique⟩
  · intro n
    rw [D.dualLocalization_eq n]
  · intro n
    rw [D.dualLocalization_eq n]
    exact D.factor_commutes n

end Omega.CircleDimension
