import InfoGeometry.Canonical.BogoliubovProjectorFlux
import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorDictionary

Operator-only dictionary normalizing the root doubled-carrier language.

This module introduces no new owner semantics. It only aligns notation with the
already-owned canonical surfaces:

- `u₊, u₋` as spectral-sector components (`P₊u`, `P₋u`),
- `Q₊, Q₋` as the off-diagonal chiral arrows (`P₋JP₊`, `P₊JP₋`),
- `K` as the internal phase axis (`K = J ∘ ε = complex_i`),
- `Φ(H)` as the phase-axis commutator observable `[H, K]`,
- `𝓕±(T)` as sector-exchange observables `[T, P±]`.
-/

namespace OperatorDictionary

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Canonical.ChiralHodgeDecomposition

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Dictionary entry: `u₊ := P₊u`. -/
@[rep_depth krein]
noncomputable def uPlusComponent (u : H₂) : H₂ :=
  spectralPlusProj (E := E) u

/-- Dictionary entry: `u₋ := P₋u`. -/
@[rep_depth krein]
noncomputable def uMinusComponent (u : H₂) : H₂ :=
  spectralMinusProj (E := E) u

/-- The doubled state decomposes exactly as `u = u₊ + u₋`. -/
@[rep_depth krein]
theorem u_eq_uPlusComponent_add_uMinusComponent (u : H₂) :
    u = uPlusComponent (E := E) u + uMinusComponent (E := E) u := by
  simpa [uPlusComponent, uMinusComponent] using
    spectral_decomposition (E := E) u

/-- Dictionary entry: `Q₊ := P₋JP₊`. -/
@[rep_depth krein]
noncomputable abbrev Qplus : EndH := rootDiracPlus (E := E)

/-- Dictionary entry: `Q₋ := P₊JP₋`. -/
@[rep_depth krein]
noncomputable abbrev Qminus : EndH := rootDiracMinus (E := E)

omit [CompleteSpace E] in
/-- Root odd lane split: `J = Q₊ + Q₋`. -/
@[rep_depth krein]
theorem modular_j_eq_Qplus_add_Qminus :
    modular_j (E := E) = Qplus (E := E) + Qminus (E := E) := by
  simpa [Qplus, Qminus, rootDiracOddLane] using
    rootDiracOddLane_eq_chiral_sum (E := E)

/-- Dictionary entry: `K := J ∘ ε`. -/
@[rep_depth krein]
noncomputable def phaseAxisK : EndH :=
  (modular_j (E := E)).comp (spectral_epsilon (E := E))

omit [CompleteSpace E] in
/-- Canonical split identity: `K = J ∘ ε`. -/
@[rep_depth krein]
theorem phaseAxisK_eq_modular_j_comp_spectral_epsilon :
    phaseAxisK (E := E)
      = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by
  rfl

/-- Canonical split identity: `J ∘ ε = -ε ∘ J`. -/
@[rep_depth krein]
theorem modular_j_comp_spectral_epsilon_eq_neg_spectral_epsilon_comp_modular_j :
    (modular_j (E := E)).comp (spectral_epsilon (E := E))
      = -((spectral_epsilon (E := E)).comp (modular_j (E := E))) := by
  simpa using modular_j_spectral_epsilon_anticommute (E := E)

/-- Canonical split identity: `K² = -Id`. -/
@[rep_depth krein]
theorem phaseAxisK_sq_eq_neg_id :
    (phaseAxisK (E := E)).comp (phaseAxisK (E := E))
      = -(ContinuousLinearMap.id ℝ H₂) := by
  simp [phaseAxisK]

/-- Hilbert-inner skew rule for the internal phase axis `K`. -/
@[rep_depth krein]
theorem phaseAxisK_inner_skew (u v : H₂) :
    ⟪phaseAxisK (E := E) u, v⟫_ℝ = -⟪u, phaseAxisK (E := E) v⟫_ℝ := by
  let _ : CompleteSpace E := inferInstance
  unfold phaseAxisK
  exact TomitaTakesaki.complex_i_inner_skew (E := E) u v

/-- Krein-sign rule for the internal phase axis `K`. -/
@[rep_depth krein]
theorem phaseAxisK_kreinInner_comp (u v : H₂) :
    KreinSpace.kreinInner (H := H₂) (phaseAxisK (E := E) u) (phaseAxisK (E := E) v)
      = -KreinSpace.kreinInner (H := H₂) u v := by
  simpa [phaseAxisK] using TomitaTakesaki.modularComplexI_kreinInner_comp (E := E) u v

/-- Dictionary entry: `Φ(H) := [H, K]`. -/
@[rep_depth transport]
noncomputable def phaseAxisObservable (H : EndH) : EndH :=
  transportCommutator (E := E) H (phaseAxisK (E := E))

/-- `Φ(H)` is exactly the owner phase-axis force. -/
@[rep_depth transport]
theorem phaseAxisObservable_eq_phaseAxisForce (H : EndH) :
    phaseAxisObservable (E := E) H = phaseAxisForce (E := E) H := by
  simpa [phaseAxisObservable, phaseAxisK] using
    phaseAxisForce_eq_transportCommutator_complex_i (E := E) H

/-- Dictionary entry: `𝓕₊(T) := [T, P₊]`. -/
@[rep_depth transport]
noncomputable def sectorExchangeObservablePlus (T : EndH) : EndH :=
  transportCommutator (E := E) T (spectralPlusProj (E := E))

/-- Dictionary entry: `𝓕₋(T) := [T, P₋]`. -/
@[rep_depth transport]
noncomputable def sectorExchangeObservableMinus (T : EndH) : EndH :=
  transportCommutator (E := E) T (spectralMinusProj (E := E))

omit [CompleteSpace E] in
/--
The existing projector-flux owner uses `[P₊, T]`; this is the negative of
the dictionary orientation `[T, P₊]`.
-/
@[rep_depth transport]
theorem plusProjectorFlux_eq_neg_sectorExchangeObservablePlus (T : EndH) :
    plusProjectorFlux (E := E) T = -(sectorExchangeObservablePlus (E := E) T) := by
  unfold plusProjectorFlux sectorExchangeObservablePlus transportCommutator
  abel

omit [CompleteSpace E] in
/--
The existing projector-flux owner uses `[P₋, T]`; this is the negative of
the dictionary orientation `[T, P₋]`.
-/
@[rep_depth transport]
theorem minusProjectorFlux_eq_neg_sectorExchangeObservableMinus (T : EndH) :
    minusProjectorFlux (E := E) T = -(sectorExchangeObservableMinus (E := E) T) := by
  unfold minusProjectorFlux sectorExchangeObservableMinus transportCommutator
  abel

end Core

end OperatorDictionary
