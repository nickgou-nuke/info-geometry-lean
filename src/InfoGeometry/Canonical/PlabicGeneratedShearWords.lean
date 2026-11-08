/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KantorTanakaFiveGradedMetriplecticZornPoset

/-!
# Generated heterogeneous Peirce-shear words and twisted-star inversion

The imported CPT owner proves inversion for an arbitrary list once each gate
is supplied with both inverse equations. This module derives those equations
for every gate in a heterogeneous list of upper/lower Peirce shears, assuming
each edge seed is self-adjoint and commutes with the sheet-swap involution.
The result is an associative-ring theorem, not a physical unitarity claim.
-/

namespace InfoGeometry.Canonical.PlabicGeneratedShearWords

open InfoGeometry.Canonical.KantorTanakaFiveGradedMetriplecticZornPoset.PlabicTwistedPinCPT
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- A directed elementary Plabic shear, with `true` selecting the upper
Peirce corner and `false` the lower corner. -/
def plabicShearGate {B : Type*} [Ring B] (P : B) (edge : Bool × B) : B :=
  match edge with
  | (true, X) => 1 + conePlus P X
  | (false, X) => 1 + coneMinus P X

/-- Product of a finite edge list in its displayed order, using the owner's
right-fold convention. -/
def plabicShearWord {B : Type*} [Ring B] (P : B) (edges : List (Bool × B)) : B :=
  plabicWord (edges.map (plabicShearGate P))

/-- Each elementary gate built from a symmetric, swap-commuting seed has the
two-sided inverse prescribed by the owner's twisted-star CPT map. -/
theorem plabicShearGate_cpt_inverse
    {B : Type*} [Ring B] [StarRing B] {P Phi1 X : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_star : star Phi1 = Phi1)
    (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (hX_star : star X = X) (hPhi_X : Phi1 * X = X * Phi1)
    (upper : Bool) :
    plabicShearGate P (upper, X) *
        thetaCPT P Phi1 (plabicShearGate P (upper, X)) = 1 ∧
      thetaCPT P Phi1 (plabicShearGate P (upper, X)) *
        plabicShearGate P (upper, X) = 1 := by
  have hPN3 := stage_PN3_twisted_pin_cpt_anti_automorphism_and_edge_negation
    hP hP_star hPhi_sq hPhi_star hPhi_P hX_star hPhi_X 0 0 0
  rcases hPN3 with ⟨_, ⟨⟨_, hThetaOne⟩, ⟨_, ⟨hThetaPlus, hThetaMinus⟩⟩⟩⟩
  cases upper
  · dsimp [plabicShearGate]
    have hGate : thetaCPT P Phi1 (1 + coneMinus P X) = 1 - coneMinus P X := by
      rw [thetaCPT_add, hThetaOne, hThetaMinus]
      abel
    refine ⟨?_, ?_⟩ <;> rw [hGate] <;> peirce_nf hP
  · dsimp [plabicShearGate]
    have hGate : thetaCPT P Phi1 (1 + conePlus P X) = 1 - conePlus P X := by
      rw [thetaCPT_add, hThetaOne, hThetaPlus]
      abel
    refine ⟨?_, ?_⟩ <;> rw [hGate] <;> peirce_nf hP

/-- A finite heterogeneous word of Peirce shears is two-sided CPT-invertible
when every edge seed is self-adjoint and commutes with the bipartite swap.
Unlike `plabicWord_cpt_unitary`, the gate inverse hypotheses are derived here
from the individual edge data rather than supplied as assumptions. -/
theorem plabicShearWord_cpt_unitary
    {B : Type*} [Ring B] [StarRing B] {P Phi1 : B}
    (hP : P * P = P) (hP_star : star P = P)
    (hPhi_sq : Phi1 * Phi1 = 1) (hPhi_star : star Phi1 = Phi1)
    (hPhi_P : Phi1 * P = (1 - P) * Phi1)
    (edges : List (Bool × B))
    (hSeeds : ∀ upper X, (upper, X) ∈ edges →
      star X = X ∧ Phi1 * X = X * Phi1) :
    plabicShearWord P edges * thetaCPT P Phi1 (plabicShearWord P edges) = 1 ∧
      thetaCPT P Phi1 (plabicShearWord P edges) * plabicShearWord P edges = 1 := by
  have hJ1_sq : pinJ1 P Phi1 * pinJ1 P Phi1 = -1 :=
    (stage_PN1_bipartite_vertices_and_twisted_pin_clifford_generators
      hP hP_star hPhi_sq hPhi_star hPhi_P).2.2.2.1
  have hGateInv : ∀ edge ∈ edges,
      plabicShearGate P edge * thetaCPT P Phi1 (plabicShearGate P edge) = 1 ∧
        thetaCPT P Phi1 (plabicShearGate P edge) * plabicShearGate P edge = 1 := by
    intro edge hedge
    rcases edge with ⟨upper, X⟩
    obtain ⟨hX_star, hPhi_X⟩ := hSeeds upper X hedge
    exact plabicShearGate_cpt_inverse hP hP_star hPhi_sq hPhi_star hPhi_P
      hX_star hPhi_X upper
  have hMappedInv : ∀ g ∈ edges.map (plabicShearGate P),
      g * thetaCPT P Phi1 g = 1 ∧ thetaCPT P Phi1 g * g = 1 := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨edge, hedge, hEq⟩
    rw [← hEq]
    exact hGateInv edge hedge
  unfold plabicShearWord
  exact plabicWord_cpt_unitary hJ1_sq (edges.map (plabicShearGate P)) hMappedInv

end InfoGeometry.Canonical.PlabicGeneratedShearWords
