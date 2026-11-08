import InfoGeometry.Physics.FermionicAndreevReflection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.BlackHoleUnitarityBridge

/-!
# Andreev Horizon Unitarity Bridge

#### BUCKET 1: CLOSED FINITE THEOREMS

- `andreevTwin_sq`
- `andreevTwin_normSq`
- `andreevTwin_fourth`
- `hawking_is_andreev_reflection`
- `concreteAndreevHorizonSMatrix_unitarity`
- `concreteAndreevHorizon_information_preservation`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

- `horizon_information_preservation_from_trace_zero`

#### BUCKET 3: OPEN CLOSURE DEBT

- Construct a physical event-horizon scattering model from geometric hypotheses.
- Prove that such a model is equivalent to a superconducting Andreev boundary.
- Relate the finite condensate marker below to a genuine BEC/Cooper-pair field.
- Connect boundary Majorana zero modes to a certified de Rham Betti computation.

This module records the finite algebraic core of the Andreev-horizon analogy.
The map `(e, h) ↦ (-h, e)` is the same two-coordinate particle-hole rotation
used by the finite BdG/Andreev witness.  It squares to `-id`, has fourth power
`id`, and matches the concrete `2 × 2` Möbius centralizer readout.

No theorem here proves Hawking radiation, black-hole unitarity, or a literal
superconducting horizon.  Those remain geometric/physical closure debt.
-/

namespace InfoGeometry.Projective.AndreevHorizonUnitarity

open InfoGeometry.Physics.FermionicAndreevReflection
open InfoGeometry.Projective.Closure
open InfoGeometry.Projective.Unitarity

/-- Finite infalling boundary quasiparticle state. -/
abbrev InfallingParticle : Type :=
  BdGQuasiparticle

/-- The Andreev-reflected particle-hole twin. -/
def AndreevTwin (state : InfallingParticle) : InfallingParticle :=
  andreevReflection state

/-- A finite scalar marker for the condensate channel. -/
def CooperPairCondensate (state : InfallingParticle) : ℝ :=
  state.e + state.h

/-- Finite boundary scattering readout: reflected twin plus condensate marker. -/
structure BoundaryScatteringReadout where
  reflectedTwin : InfallingParticle
  condensateMarker : ℝ

/-- Finite Andreev boundary-scattering readout. -/
def BoundaryScattering (state : InfallingParticle) : BoundaryScatteringReadout where
  reflectedTwin := AndreevTwin state
  condensateMarker := CooperPairCondensate state

/-- The Andreev twin squares to the central fermionic phase `-1`. -/
theorem andreevTwin_sq (state : InfallingParticle) :
    AndreevTwin (AndreevTwin state) = -state :=
  andreevReflection_sq state

/-- The finite Andreev twin preserves the electron/hole squared amplitude. -/
theorem andreevTwin_normSq (state : InfallingParticle) :
    amplitudeNormSq (AndreevTwin state) = amplitudeNormSq state :=
  andreevReflection_normSq state

/-- The Andreev twin has fourth power identity. -/
theorem andreevTwin_fourth (state : InfallingParticle) :
    AndreevTwin (AndreevTwin (AndreevTwin (AndreevTwin state))) = state :=
  andreevReflection_fourth state

/--
Finite readout form of the slogan "Hawking radiation is Andreev reflection".

This proves only that the finite boundary scattering packet records the
Andreev-reflected twin and the condensate marker by definition.
-/
theorem hawking_is_andreev_reflection (state : InfallingParticle) :
    (BoundaryScattering state).reflectedTwin = AndreevTwin state ∧
      (BoundaryScattering state).condensateMarker = CooperPairCondensate state := by
  constructor <;> rfl

/-- Concrete `2 × 2` projective horizon S-matrix from the Möbius closure. -/
def concreteAndreevHorizonSMatrix : HorizonSMatrix 2 where
  closure := mobiusClosure2
  unitarity := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [mobiusClosure2, mobiusParity2, Matrix.mul_apply]

/-- The concrete Andreev horizon S-matrix is a real isometry. -/
theorem concreteAndreevHorizonSMatrix_unitarity :
    concreteAndreevHorizonSMatrix.closure.moebiusParity.transpose *
        concreteAndreevHorizonSMatrix.closure.moebiusParity =
      concreteAndreevHorizonSMatrix.closure.I :=
  concreteAndreevHorizonSMatrix.unitarity

/-- Conditional information-preservation readback from trace-zero plus isometry. -/
theorem horizon_information_preservation_from_trace_zero
    {n : ℕ} (S : HorizonSMatrix n)
    (hTrace : Matrix.trace S.closure.moebiusParity = 0) :
    (S.closure.moebiusParity.transpose * S.closure.moebiusParity = S.closure.I) ∧
      S.closure.gromovWittenIndex = 0 :=
  information_preservation n S hTrace

/-- Concrete finite information-preservation readback for the `2 × 2` model. -/
theorem concreteAndreevHorizon_information_preservation :
    (concreteAndreevHorizonSMatrix.closure.moebiusParity.transpose *
        concreteAndreevHorizonSMatrix.closure.moebiusParity =
      concreteAndreevHorizonSMatrix.closure.I) ∧
      concreteAndreevHorizonSMatrix.closure.gromovWittenIndex = 0 := by
  exact horizon_information_preservation_from_trace_zero
    concreteAndreevHorizonSMatrix
    mobiusParity2_trace

end InfoGeometry.Projective.AndreevHorizonUnitarity
