import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import InfoGeometry.Physics.CuntzDeformedSuperPoincare
import InfoGeometry.Physics.LorentzChiralCuntzBridge
import Mathlib.Tactic

/-!
# Complexified Poincaré semidirect product and Cuntz transport

This file provides the finite semidirect product layer for the complexified
Poincaré group acting on soldered four-momenta, and the Lorentz transport
of the Cuntz-deformed super-Poincaré operator relation.
-/

noncomputable section

namespace InfoGeometry.Physics.ChiralPoincareSemidirect

open Matrix
open scoped BigOperators
open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Physics.CuntzDeformedSuperPoincare
open InfoGeometry.Physics.LorentzChiralCuntzBridge

/-- Complexified Poincaré semidirect element: Lorentz part (SL(2,ℂ)) and translation (FourMomentum). -/
structure ChiralPoincareElement where
  lorentz : SL2C
  translation : FourMomentum

/-- Composition in the complexified Poincaré semidirect product. -/
def chiralPoincareComp (G H : ChiralPoincareElement) : ChiralPoincareElement :=
  ⟨G.lorentz * H.lorentz, addFourMomentum G.translation (spinLorentzAction G.lorentz H.translation)⟩

/-- Action of a Poincaré element on a four-momentum. -/
def chiralPoincareAct (G : ChiralPoincareElement) (P : FourMomentum) : FourMomentum :=
  addFourMomentum (spinLorentzAction G.lorentz P) G.translation

/-- The Poincaré action respects composition. -/
theorem chiralPoincareAct_comp (G H : ChiralPoincareElement) (P : FourMomentum) :
    chiralPoincareAct (chiralPoincareComp G H) P = chiralPoincareAct G (chiralPoincareAct H P) := by
  have h₁ : pauliMomentum (chiralPoincareAct (chiralPoincareComp G H) P) = pauliMomentum (chiralPoincareAct G (chiralPoincareAct H P)) := by
    simp only [chiralPoincareAct, chiralPoincareComp, pauliMomentum_add]
    have hspin : ∀ (g : SL2C) (Q : FourMomentum),
        pauliMomentum (spinLorentzAction g Q) = chiralConjAct g (pauliMomentum Q) := by
      intro g Q
      rw [spinLorentzAction, pauliMomentum_fourMomentumOfMatrix]
    have houter := hspin G.lorentz (addFourMomentum (spinLorentzAction H.lorentz P) H.translation)
    rw [houter, pauliMomentum_add, hspin]
    rw [hspin, hspin]
    rw [chiralConjAct_add, chiralConjAct_mul]
    simp [Matrix.mul_assoc, add_assoc, add_comm, add_left_comm]
  -- Use extensionality via pauliMomentum
  have h₂ : chiralPoincareAct (chiralPoincareComp G H) P = chiralPoincareAct G (chiralPoincareAct H P) := by
    apply InfoGeometry.Physics.LorentzChiralCuntzBridge.fourMomentum_ext_of_pauliMomentum_eq
    exact h₁
  exact h₂

/-- The Lorentz transport of the Cuntz-deformed super-Poincaré relation. -/
def transportedRelation (L R : ChiralPoincareSouriauBridge.M2C) (S : CuntzDeformedSuperPoincare.ChiralOperatorPresentation) : Prop :=
  CuntzDeformedSuperPoincare.spinTransport L R S.antiQQbar = (2 : ℂ) • CuntzDeformedSuperPoincare.spinTransport L R S.Pspinor

/-- The Lorentz transport of the Cuntz-deformed relation holds for `SL(2,ℂ)` spin matrices. -/
theorem sl2c_transportedRelation_holds (g : SL2C)
    (S : CuntzDeformedSuperPoincare.ChiralOperatorPresentation)
    :
    transportedRelation (spinMatrix g) (spinMatrix g⁻¹) S := by
  exact CuntzDeformedSuperPoincare.transportedRelation_holds
    (spinMatrix g) (spinMatrix g⁻¹) S

end InfoGeometry.Physics.ChiralPoincareSemidirect
