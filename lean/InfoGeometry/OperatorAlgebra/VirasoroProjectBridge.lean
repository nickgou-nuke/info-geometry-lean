/-
InfoGeometry/OperatorAlgebra/VirasoroProjectBridge.lean

Partial transport between the abstract Virasoro socket and the
`VirasoroProject` surface.

This file is honest about its scope:

- the concrete `VirasoroDatum` realization is certified by `VirasoroProject`.
- the Sugawara central charge calibration for the Heisenberg case is honest debt.
-/

import InfoGeometry.External.Virasoro.VirasoroAlgebra
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

noncomputable section

namespace InfoGeometry.OperatorAlgebra.VirasoroProjectBridge

open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
open VirasoroProject

/--
Predicate recording that a given `VirasoroDatum` is realized by the
`VirasoroProject` implementation on `ℝ`.
-/
def VirasoroProjectRealizes (V : VirasoroDatum (VirasoroAlgebra ℝ)) : Prop :=
  (∀ n, V.Lmode n = VirasoroAlgebra.lgen ℝ n) ∧ V.central = VirasoroAlgebra.cgen ℝ

/-- The concrete Virasoro datum induced by `VirasoroProject`. -/
def virasoroProjectVirasoroDatum :
    VirasoroDatum (VirasoroAlgebra ℝ) :=
{ Lmode := fun n => VirasoroAlgebra.lgen ℝ n
  central := VirasoroAlgebra.cgen ℝ }

/-- The concrete `VirasoroProject` datum is realized by its own generators. -/
theorem virasoroProjectVirasoroDatum_realizes :
    VirasoroProjectRealizes virasoroProjectVirasoroDatum := by
  constructor
  · intro n
    rfl
  · rfl

/-- The concrete central element commutes, via the partial affine bridge laws. -/
theorem virasoroProjectVirasoroDatum_central_commutes :
    VirasoroDatum.central_commutes_True virasoroProjectVirasoroDatum := by
  intro X
  simpa [virasoroProjectVirasoroDatum] using VirasoroAlgebra.cgen_bracket (𝕜 := ℝ) X

/-- The concrete Virasoro bracket law is the expected one. -/
theorem virasoroProjectVirasoroDatum_bracket :
    VirasoroDatum.virasoro_bracket_True virasoroProjectVirasoroDatum := by
  intro m n
  by_cases hmn : m + n = 0
  · simpa [virasoroProjectVirasoroDatum, virasoroCentralCoefficient, hmn] using
      (VirasoroAlgebra.lgen_bracket (𝕜 := ℝ) m n)
  · simpa [virasoroProjectVirasoroDatum, virasoroCentralCoefficient, hmn] using
      (VirasoroAlgebra.lgen_bracket (𝕜 := ℝ) m n)

/--
Existence of a concrete `VirasoroDatum` realized by `VirasoroProject`.
-/
theorem virasoro_project_has_realized_datum :
    ∃ V : VirasoroDatum (VirasoroAlgebra ℝ), VirasoroProjectRealizes V :=
  ⟨virasoroProjectVirasoroDatum, virasoroProjectVirasoroDatum_realizes⟩

/-- Alias for compatibility with prime bridge naming. -/
theorem virasoro_project_is_certified :
    ∃ V : VirasoroDatum (VirasoroAlgebra ℝ), VirasoroProjectRealizes V :=
  virasoro_project_has_realized_datum

/--
Concrete Sugawara datum for the Heisenberg case.

For a single boson (dimG = 1) and abelian affine algebra (hDual = 0), the
central charge is `1`.
-/
def heisenbergSugawaraDatum : AffineVirasoroBridge.SugawaraDatum where
  level := 1
  dimG := 1
  hDual := 0
  centralCharge := 1

/-- The concrete Sugawara datum satisfies the expected central-charge law. -/
theorem heisenbergSugawaraDatum_sugawara_True :
    heisenbergSugawaraDatum.sugawara_True := by
  unfold SugawaraDatum.sugawara_True sugawaraCentralCharge heisenbergSugawaraDatum
  norm_num

end InfoGeometry.OperatorAlgebra.VirasoroProjectBridge
