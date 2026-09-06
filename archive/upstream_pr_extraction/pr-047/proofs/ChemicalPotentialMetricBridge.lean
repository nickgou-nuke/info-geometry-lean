import proofs.ChemicalPotentialTKKGradeZero
import proofs.LightConeTripotentMatrixBridge
import proofs.EinsteinThermodynamicBridge

/-!
# Chemical-potential metric bridge

This file adds the finite Pauli-soldered metric shadow of the chemical
potential:

* a local shift `δμ` acts on the time/energy component by `E ↦ E - δμ`;
* the determinant/Minkowski quadric changes by the explicit algebraic term
  `δμ^2 - 2 δμ E`;
* any Tolman--Ehrenfest, Einstein-limit, or field-equation reading of `g₀₀` is
  a non-formalized external interpretation of these finite identities.

No field equations or continuum gravity are asserted in the Lean kernel.
-/

noncomputable section

namespace ChemicalPotentialMetricBridge

open ChiralPoincareSouriauBridge
open LightConeTripotentMatrixBridge

/-- A local thermodynamic state carrying the chemical-potential shift used by the
Pauli-soldered finite model. -/
structure ThermodynamicState where
  deltaMu : ℂ
  beta : ℂ

/-- A minimal local vielbein shadow: the time component and its square `g₀₀`. -/
structure LocalVielbein where
  timeScale : ℂ
  g00 : ℂ
  g00_eq_timeScale_sq : g00 = timeScale ^ 2

/-- Chemical-potential shift on a Pauli-soldered four-momentum:
`E ↦ E - δμ`. -/
def chemicalShiftMomentum (P : FourMomentum) (δμ : ℂ) : FourMomentum where
  E := P.E - δμ
  px := P.px
  py := P.py
  pz := P.pz

/-- The local metric/vielbein shadow induced by a chemical-potential shift. -/
def chemicalLocalVielbein (δμ : ℂ) : LocalVielbein where
  timeScale := 1 - δμ
  g00 := (1 - δμ) ^ 2
  g00_eq_timeScale_sq := rfl

/-- The shifted Minkowski quadric is the original quadric plus the exact
chemical-potential deformation term. -/
theorem minkowskiSq_chemicalShiftMomentum
    (P : FourMomentum) (δμ : ℂ) :
    minkowskiSq (chemicalShiftMomentum P δμ) =
      minkowskiSq P + (δμ ^ 2 - 2 * δμ * P.E) := by
  cases P with
  | mk E px py pz =>
    simp [chemicalShiftMomentum, minkowskiSq]
    ring

/-- The Pauli determinant of the shifted momentum has the same deformation term,
because `det(P·σ)` is the Minkowski quadric. -/
theorem det_pauliMomentum_chemicalShiftMomentum
    (P : FourMomentum) (δμ : ℂ) :
    (pauliMomentum (chemicalShiftMomentum P δμ)).det =
      minkowskiSq P + (δμ ^ 2 - 2 * δμ * P.E) := by
  rw [det_pauliMomentum, minkowskiSq_chemicalShiftMomentum]

/-- The induced local `g₀₀` shadow is the square of the shifted time scale. -/
theorem chemicalLocalVielbein_g00 (δμ : ℂ) :
    (chemicalLocalVielbein δμ).g00 = (1 - δμ) ^ 2 := rfl

/-- The local inverse temperature adjusted by the chemical potential time scale
(a Tolman--Ehrenfest analogue). -/
def localBeta (state : ThermodynamicState) : ℂ :=
  state.beta * (chemicalLocalVielbein state.deltaMu).timeScale

/-- The exact finite algebraic identity mirroring the Tolman--Ehrenfest form. -/
theorem tolman_ehrenfest_analogue (state : ThermodynamicState) :
    localBeta state = state.beta * (1 - state.deltaMu) := rfl

/-- The chemical shift appears in the squared local `g₀₀` component. -/
theorem g00_interprets_chemical_potential (δμ : ℂ) :
    (chemicalLocalVielbein δμ).g00 = (1 - δμ) ^ 2 := rfl

/-- An algebraic cancellation identity relating the shifted energy to `δμ`. -/
theorem einstein_macroscopic_limit_analogue (P : FourMomentum) (δμ : ℂ) :
    (chemicalShiftMomentum P δμ).E + δμ = P.E := by
  dsimp [chemicalShiftMomentum]
  ring

/-- The metric deformation is exact at TKK grade zero (time scale component). -/
theorem tkk_grade_zero_metric_deformation (δμ : ℂ) :
    (chemicalLocalVielbein δμ).timeScale + δμ = 1 := by
  dsimp [chemicalLocalVielbein]
  ring

/-- Synthesis of the finite algebraic determinant shift, local `g₀₀` square,
matrix light-cone facts, and chemical-shift cancellation identities. -/
theorem chemical_potential_metric_synthesis
    (P : FourMomentum) (state : ThermodynamicState) :
    (pauliMomentum (chemicalShiftMomentum P state.deltaMu)).det =
      minkowskiSq P + (state.deltaMu ^ 2 - 2 * state.deltaMu * P.E) ∧
    (chemicalLocalVielbein state.deltaMu).g00 =
      (1 - state.deltaMu) ^ 2 ∧
    MatrixLightCone E00 ∧
    IsAssociativeTripotent E00 ∧
    localBeta state = state.beta * (1 - state.deltaMu) ∧
    (chemicalLocalVielbein state.deltaMu).g00 = (1 - state.deltaMu) ^ 2 ∧
    (chemicalShiftMomentum P state.deltaMu).E + state.deltaMu = P.E ∧
    (chemicalLocalVielbein state.deltaMu).timeScale + state.deltaMu = 1 := by
  constructor
  · exact det_pauliMomentum_chemicalShiftMomentum P state.deltaMu
  constructor
  · exact chemicalLocalVielbein_g00 state.deltaMu
  constructor
  · exact E00_lightCone
  constructor
  · exact E00_tripotent
  constructor
  · exact tolman_ehrenfest_analogue state
  constructor
  · exact g00_interprets_chemical_potential state.deltaMu
  constructor
  · exact einstein_macroscopic_limit_analogue P state.deltaMu
  · exact tkk_grade_zero_metric_deformation state.deltaMu

end ChemicalPotentialMetricBridge

end noncomputable section
