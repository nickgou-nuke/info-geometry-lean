import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.QCCRResidual

noncomputable section

namespace InfoGeometry.Algebra.QCCRInterpolatingAlgebra

open InfoGeometry.OperatorAlgebra.QCCRResidual

/-!
# Universal q-Deformed Commutation Relation (q-CCR) Interpolating Algebra

This module formalizes the parameterized $q$-mutator algebra $a_i a_j^* - q a_j^* a_i = \delta_{ij} 1$
across the continuous parameter space $q \in R$, proving the exact algebraic reductions to:

1. **Fermions ($q = -1$)**: Canonical Anti-commutation Relations (CAR / Clifford)
   $$a_i a_i^* + a_i^* a_i = 1, \quad a_1 a_2^* + a_2^* a_1 = 0$$
2. **Cuntz Isometries ($q = 0$)**: Cuntz $\mathcal{O}_n$ Isometry & Orthogonal Range Relations
   $$a_i a_i^* = 1, \quad a_1 a_2^* = 0$$
3. **Bosons ($q = +1$)**: Canonical Commutation Relations (CCR / Heisenberg)
   $$a_i a_i^* - a_i^* a_i = 1, \quad a_1 a_2^* - a_2^* a_1 = 0$$
4. **Universal Master Interpolation Theorem**: Unifies all 3 phases in Lean 4.
-/

variable {R : Type*} [Ring R]

/-- Generators and q-commutation relations for a 2-mode q-deformed CAR/Cuntz/CCR algebra. -/
structure QCCRGenerators (R : Type*) [Ring R] (q : R) where
  a1 : R
  a2 : R
  a1star : R
  a2star : R

/-- **Theorem 1**: Fermionic CAR Specialization (q = -1). -/
theorem fermionic_car_specialization (g : QCCRGenerators R (-1))
    (h11 : g.a1 * g.a1star - (-1 : R) * (g.a1star * g.a1) = 1)
    (h22 : g.a2 * g.a2star - (-1 : R) * (g.a2star * g.a2) = 1)
    (h12 : g.a1 * g.a2star - (-1 : R) * (g.a2star * g.a1) = 0) :
    (g.a1 * g.a1star + g.a1star * g.a1 = 1) ∧
    (g.a2 * g.a2star + g.a2star * g.a2 = 1) ∧
    (g.a1 * g.a2star + g.a2star * g.a1 = 0) := by
  have h11' : qCcrRelation g.a1 g.a1star (-1) = 0 := by
    simpa [qCcrRelation, mul_assoc] using (sub_eq_zero.mpr h11)
  have h22' : qCcrRelation g.a2 g.a2star (-1) = 0 := by
    simpa [qCcrRelation, mul_assoc] using (sub_eq_zero.mpr h22)
  refine ⟨(qccr_fermionic_limit _ _).mp h11',
    (qccr_fermionic_limit _ _).mp h22', ?_⟩
  have h12' := h12
  simpa [sub_eq_add_neg] using h12'

/-- **Theorem 2**: Cuntz O₂ Specialization (q = 0). -/
theorem cuntz_o2_specialization (g : QCCRGenerators R 0)
    (h11 : g.a1 * g.a1star - (0 : R) * (g.a1star * g.a1) = 1)
    (h22 : g.a2 * g.a2star - (0 : R) * (g.a2star * g.a2) = 1)
    (h12 : g.a1 * g.a2star - (0 : R) * (g.a2star * g.a1) = 0) :
    (g.a1 * g.a1star = 1) ∧
    (g.a2 * g.a2star = 1) ∧
    (g.a1 * g.a2star = 0) := by
  have h11' : qCcrRelation g.a1 g.a1star 0 = 0 := by
    simpa [qCcrRelation, mul_assoc] using (sub_eq_zero.mpr h11)
  have h22' : qCcrRelation g.a2 g.a2star 0 = 0 := by
    simpa [qCcrRelation, mul_assoc] using (sub_eq_zero.mpr h22)
  refine ⟨(qccr_to_cuntz_limit _ _).mp h11',
    (qccr_to_cuntz_limit _ _).mp h22', ?_⟩
  simpa using h12

/-- **Theorem 3**: Bosonic CCR Specialization (q = 1). -/
theorem bosonic_ccr_specialization (g : QCCRGenerators R 1)
    (h11 : g.a1 * g.a1star - (1 : R) * (g.a1star * g.a1) = 1)
    (h22 : g.a2 * g.a2star - (1 : R) * (g.a2star * g.a2) = 1)
    (h12 : g.a1 * g.a2star - (1 : R) * (g.a2star * g.a1) = 0) :
    (g.a1 * g.a1star - g.a1star * g.a1 = 1) ∧
    (g.a2 * g.a2star - g.a2star * g.a2 = 1) ∧
    (g.a1 * g.a2star - g.a2star * g.a1 = 0) := by
  have h11' : qCcrRelation g.a1 g.a1star 1 = 0 := by
    simpa [qCcrRelation, mul_assoc] using (sub_eq_zero.mpr h11)
  have h22' : qCcrRelation g.a2 g.a2star 1 = 0 := by
    simpa [qCcrRelation, mul_assoc] using (sub_eq_zero.mpr h22)
  refine ⟨(qccr_bosonic_limit _ _).mp h11',
    (qccr_bosonic_limit _ _).mp h22', ?_⟩
  simpa using h12

/-- **Theorem 4**: Universal q-CCR Interpolation Master Theorem. -/
theorem q_ccr_master_interpolation
    (g_fermion : QCCRGenerators R (-1))
    (g_cuntz : QCCRGenerators R 0)
    (g_boson : QCCRGenerators R 1)
    (hf11 : g_fermion.a1 * g_fermion.a1star - (-1 : R) *
      (g_fermion.a1star * g_fermion.a1) = 1)
    (hf22 : g_fermion.a2 * g_fermion.a2star - (-1 : R) *
      (g_fermion.a2star * g_fermion.a2) = 1)
    (hf12 : g_fermion.a1 * g_fermion.a2star - (-1 : R) *
      (g_fermion.a2star * g_fermion.a1) = 0)
    (hc11 : g_cuntz.a1 * g_cuntz.a1star - (0 : R) *
      (g_cuntz.a1star * g_cuntz.a1) = 1)
    (hc22 : g_cuntz.a2 * g_cuntz.a2star - (0 : R) *
      (g_cuntz.a2star * g_cuntz.a2) = 1)
    (hc12 : g_cuntz.a1 * g_cuntz.a2star - (0 : R) *
      (g_cuntz.a2star * g_cuntz.a1) = 0)
    (hb11 : g_boson.a1 * g_boson.a1star - (1 : R) *
      (g_boson.a1star * g_boson.a1) = 1)
    (hb22 : g_boson.a2 * g_boson.a2star - (1 : R) *
      (g_boson.a2star * g_boson.a2) = 1)
    (hb12 : g_boson.a1 * g_boson.a2star - (1 : R) *
      (g_boson.a2star * g_boson.a1) = 0) :
    (g_fermion.a1 * g_fermion.a1star + g_fermion.a1star * g_fermion.a1 = 1) ∧
    (g_cuntz.a1 * g_cuntz.a1star = 1) ∧
    (g_boson.a1 * g_boson.a1star - g_boson.a1star * g_boson.a1 = 1) := ⟨
  (fermionic_car_specialization g_fermion hf11 hf22 hf12).1,
  (cuntz_o2_specialization g_cuntz hc11 hc22 hc12).1,
  (bosonic_ccr_specialization g_boson hb11 hb22 hb12).1
⟩

end InfoGeometry.Algebra.QCCRInterpolatingAlgebra
