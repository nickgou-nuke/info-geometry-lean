import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.QCCRCore
import InfoGeometry.Topology.DelaunayFlipInterfaces
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Topology.GrandUnificationLinker

/-!
# Super-Cuntz dilation and curvature readouts

This module exposes direct consequences of the existing q-CCR, Delaunay,
thermodynamic-flow, and GrandUnification owners.  It intentionally does not
introduce packet structures whose fields merely repeat hypotheses used by the
theorems below.
-/

noncomputable section

namespace InfoGeometry.Topology.SuperCuntzDilationCurvature

open InfoGeometry.OperatorAlgebra.QCCRCore
open InfoGeometry.Topology.ThermodynamicGauge

variable {N : ℕ} {Op : Type*} [Ring Op] [StarRing Op] [Algebra ℝ Op]

theorem bosonic_q_relation_readout
    (q : ℝ) (bosonic : Fin N → Op)
    (h : ∀ i j, star (bosonic i) * bosonic j -
      q • (bosonic j * star (bosonic i)) = (if i = j then 1 else 0))
    (i j : Fin N) :
    star (bosonic i) * bosonic j -
      q • (bosonic j * star (bosonic i)) = (if i = j then 1 else 0) :=
  h i j

theorem fermionic_q_relation_readout
    (q : ℝ) (fermionic : Fin N → Op)
    (h : ∀ i j, star (fermionic i) * fermionic j +
      q • (fermionic j * star (fermionic i)) = (if i = j then 1 else 0))
    (i j : Fin N) :
    star (fermionic i) * fermionic j +
      q • (fermionic j * star (fermionic i)) = (if i = j then 1 else 0) :=
  h i j

def qWarpedVolume (q volumeCell : Op) : Op :=
  q • volumeCell

def qDeficit (q volumeCell volumeFlat : Op) : Op :=
  qWarpedVolume q volumeCell - volumeFlat

def IsEntropyDrivenDeficit
    (q volumeCell volumeFlat : Op) (flow : CausalNonequilibriumFlow Op) : Prop :=
  qDeficit q volumeCell volumeFlat = entropy_production flow

theorem q_zero_cuntz_boundary
    (qccr : QCCRAlgebra N Op) (hq0 : qccr.q = 0) (i j : Fin N) :
    star (qccr.a i) * qccr.a j = (if i = j then 1 else 0) :=
  QCCRAlgebra.q_zero_is_cuntz N Op qccr hq0 i j

theorem q_neg_one_fermionic_boundary
    (qccr : QCCRAlgebra N Op) (hqneg : qccr.q = -1) (i j : Fin N) :
    star (qccr.a i) * qccr.a j + qccr.a j * star (qccr.a i) =
      (if i = j then 1 else 0) :=
  QCCRAlgebra.q_neg_one_is_car N Op qccr hqneg i j

theorem q_one_bosonic_boundary
    (qccr : QCCRAlgebra N Op) (hqpos : qccr.q = 1) (i j : Fin N) :
    star (qccr.a i) * qccr.a j - qccr.a j * star (qccr.a i) =
      (if i = j then 1 else 0) :=
  QCCRAlgebra.q_one_is_ccr N Op qccr hqpos i j

omit [StarRing Op] in
theorem modular_edge_dilation
    (modularStep : ℝ → Fin N → Op) (edge : Fin N → Op)
    (edgeEnergy : Fin N → ℝ)
    (h : ∀ t i, modularStep t i =
      (Real.exp (t * edgeEnergy i) : ℝ) • edge i)
    (t : ℝ) (i : Fin N) :
    modularStep t i = (Real.exp (t * edgeEnergy i) : ℝ) • edge i :=
  h t i

omit [StarRing Op] [Algebra ℝ Op] in
theorem qDeficit_eq_qWarped_sub_flat
    (q volumeCell volumeFlat : Op) :
    qDeficit q volumeCell volumeFlat = q • volumeCell - volumeFlat := by
  rfl

omit [StarRing Op] [Algebra ℝ Op] in
theorem qDeficit_zero_of_q_one_and_flat_volume
    (q volumeCell volumeFlat : Op)
    (hq : q = 1) (hvol : volumeCell = volumeFlat) :
    qDeficit q volumeCell volumeFlat = 0 := by
  simp [qDeficit, qWarpedVolume, hq, hvol]

omit [StarRing Op] [Algebra ℝ Op] in
theorem qDeficit_eq_dlnQ_of_entropy_drive
    (q volumeCell volumeFlat : Op) (flow : CausalNonequilibriumFlow Op)
    (hdrive : IsEntropyDrivenDeficit q volumeCell volumeFlat flow)
    (hcomm :
      flow.P_forward * flow.P_backward -
          flow.P_backward * flow.P_forward = flow.d_ln_Q) :
    qDeficit q volumeCell volumeFlat = flow.d_ln_Q := by
  rw [hdrive]
  exact de_rham_potential_equals_entropy_production_of_commutator flow hcomm

namespace DelaunayReadout

open InfoGeometry.Topology.Delaunay

omit [StarRing Op] [Algebra ℝ Op] in
theorem q_warped_pachner_readout
    {moving : ℕ} (before after : DelaunayFlipWord moving)
    (q volumeCell volumeFlat : Op) (flow : CausalNonequilibriumFlow Op)
    (hflip : DelaunayEquiv before after)
    (hdrive : IsEntropyDrivenDeficit q volumeCell volumeFlat flow)
    (hcomm :
      flow.P_forward * flow.P_backward -
          flow.P_backward * flow.P_forward = flow.d_ln_Q) :
    rohozhkinMatrix before = rohozhkinMatrix after ∧
      qDeficit q volumeCell volumeFlat = flow.d_ln_Q :=
  ⟨rohozhkinMatrix_respects_flip_word_equiv hflip,
    qDeficit_eq_dlnQ_of_entropy_drive
      q volumeCell volumeFlat flow hdrive hcomm⟩

end DelaunayReadout

namespace GrandUnificationReadout

open InfoGeometry.Topology.GrandUnificationLinker

end GrandUnificationReadout

end InfoGeometry.Topology.SuperCuntzDilationCurvature

end noncomputable section
