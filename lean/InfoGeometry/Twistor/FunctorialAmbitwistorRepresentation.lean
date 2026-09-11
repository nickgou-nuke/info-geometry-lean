import InfoGeometry.Twistor.FiniteAmbitwistorParaKahler
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Bridge.OperatorPauliLubanskiLift
import InfoGeometry.Physics.FourVectorPauliCasimirBridge

/-!
# Finite ambitwistor representation bridge

This file is a thin interface between the two finite functors.  Incidence,
para-Kähler polarization, Heisenberg readout, Jones spin projection, and the
Pauli--Lubanski/Casimir calculation remain owned by their respective modules.
No analytic twistor sheaf, BRST complex, or Poincaré representation is
introduced here.
-/

namespace InfoGeometry.Twistor.FunctorialAmbitwistorRepresentation

open InfoGeometry.Twistor.FiniteAmbitwistorParaKahler
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Physics.FourVectorPauliCasimirBridge
open InfoGeometry.Bridge.OperatorPauliLubanskiLift
open InfoGeometry.Physics.PauliLubanskiFiniteBridge

abbrev IncidenceCarrier := DualTwistor4 × Twistor4
abbrev BoundaryCarrier := AmbitwistorBoundary
abbrev LorentzDatum := InfoGeometry.Physics.PauliLubanskiFiniteBridge.LorentzBivectorDatum

def incident (p : IncidenceCarrier) : Prop := IsAmbitwistor p.1 p.2

theorem incident_scale (p : IncidenceCarrier) (h : incident p)
    (c₁ c₂ : ℂ) :
    incident (scaleTwistor c₁ p.1, scaleTwistor c₂ p.2) := by
  exact isAmbitwistor_rescaling h c₁ c₂

theorem incident_readout_nilpotent (Z W : AmbitwistorVector)
    (h : ∑ i : Fin 4, Z i * W i = 0) :
    (ambitwistorRankOne Z W).comp (ambitwistorRankOne Z W) = 0 := by
  apply isAmbitwistor_rankOne_nilpotent Z W
  calc
    (∑ i : Fin 4, W i * Z i) = ∑ i : Fin 4, Z i * W i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := h

theorem pauli_lubanski_orthogonal (D : LorentzDatum) :
    InfoGeometry.Physics.LorentzBoostMinkowski.minkowskiPair
      D.momentum (pauliLubanski D) = 0 :=
  orthogonal D

theorem rest_frame_casimir (m s : ℝ)
    (J K : InfoGeometry.Physics.PauliLubanskiFiniteBridge.SpatialVector)
    (hJ : InfoGeometry.Physics.ZornMatrixSU3.dotProduct J J = s * (s + 1)) :
    InfoGeometry.Physics.LorentzBoostMinkowski.minkowskiPair
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩)
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩) =
      -m ^ 2 * s * (s + 1) :=
  rest_frame_massive_casimir m s J K hJ

theorem Jones_helicity_involution :
    helicityProjection * helicityProjection = 1 :=
  helicityProjection_sq

end InfoGeometry.Twistor.FunctorialAmbitwistorRepresentation
