/- SPDX-License-Identifier: Apache-2.0 -/

/-
# Indexed algebraic Arnold--KZ complex

This module is purely finite and algebraic.  It defines the injective
configuration carrier Conf n, the algebraic d log one-forms, indexed
infinitesimal braid residues, and the finite sum over all ordered triples.

No filters, colimits, topology, differentiability, or analytic continuation
are used.
-/

import InfoGeometry.Canonical.ArnoldCohenBCFWBridge
import InfoGeometry.Canonical.KZLogarithmicConnection

noncomputable section

namespace InfoGeometry.Canonical.IndexedArnoldKZComplex

open BigOperators
open InfoGeometry.Canonical.ArnoldCohenBCFWBridge
open InfoGeometry.Canonical.KZLogarithmicConnection

/-- Ordered configurations of n distinct points over a field. -/
def Conf (n : ℕ) (K : Type u) [Field K] : Type u :=
  {z : Fin n → K // Function.Injective z}

/-- The tangent-vector carrier used by the finite algebraic form model. -/
abbrev Tangent (n : ℕ) (K : Type*) :=
  Fin n → K

/-- The scalar coefficient of the logarithmic form d log (z_i-z_j). -/
def dlogCoefficient
    {n : ℕ} {K : Type*} [Field K]
    (z : Conf n K) (i j : Fin n) : K :=
  1 / (z.1 i - z.1 j)

/-- The algebraic Arnold one-form evaluated on a tangent carrier element. -/
def dlogForm
    {n : ℕ} {K : Type*} [Field K]
    (z : Conf n K) (dz : Fin n → K)
    (i j : Fin n) : K :=
  dlogCoefficient z i j • (dz i - dz j)

/-- Pairwise distinctness gives a nonzero logarithmic denominator. -/
theorem dlog_denominator_ne_zero
    {n : ℕ} {K : Type*} [Field K]
    (z : Conf n K) {i j : Fin n} (hij : i ≠ j) :
    z.1 i - z.1 j ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  exact hij (z.2 h)

/-- The Euler partial-fraction identity for three distinct configuration
indices. -/
theorem dlog_partial_fraction
    {n : ℕ} {K : Type*} [Field K]
    (z : Conf n K) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    dlogCoefficient z i j * dlogCoefficient z j k +
      dlogCoefficient z j k * dlogCoefficient z k i +
      dlogCoefficient z k i * dlogCoefficient z i j = 0 := by
  unfold dlogCoefficient
  have hij' := dlog_denominator_ne_zero z hij
  have hjk' := dlog_denominator_ne_zero z hjk
  have hik' := dlog_denominator_ne_zero z hik
  have hki' : z.1 k - z.1 i ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hik (z.2 h.symm)
  field_simp [hij', hjk', hik', hki']
  ring

/-- Finite-index Arnold relation for any alternating wedge carrier. -/
theorem finite_arnold_relation
    {n : ℕ} {K : Type*} [Field K]
    {M : Type*} [AddCommGroup M] [Module K M]
    (alg : ExteriorFormAlgebra (R := K) M)
    (c : Fin n → Fin n → K)
    (dz : Fin n → M)
    {i j k : Fin n}
    (hpartial :
      c i j * c j k + c j k * c k i + c k i * c i j = 0) :
    alg.wedge (c i j • (dz i - dz j))
        (c j k • (dz j - dz k)) +
      alg.wedge (c j k • (dz j - dz k))
        (c k i • (dz k - dz i)) +
      alg.wedge (c k i • (dz k - dz i))
        (c i j • (dz i - dz j)) = 0 := by
  rw [wedge_smul_left, wedge_smul_right, ← smul_assoc, smul_eq_mul]
  rw [wedge_smul_left, wedge_smul_right, ← smul_assoc, smul_eq_mul]
  rw [wedge_smul_left, wedge_smul_right, ← smul_assoc, smul_eq_mul]
  have hsub_l := wedge_sub_left alg
  have hsub_r := wedge_sub_right alg
  have halt := alg.wedge_alternating
  have hanti := alg.wedge_anticomm
  have ht :
      alg.wedge (dz i - dz j) (dz j - dz k) =
        alg.wedge (dz i) (dz j) -
          alg.wedge (dz i) (dz k) +
            alg.wedge (dz j) (dz k) := by
    rw [hsub_l, hsub_r, hsub_r, halt (dz j)]
    abel
  have hu :
      alg.wedge (dz j - dz k) (dz k - dz i) =
        alg.wedge (dz i) (dz j) -
          alg.wedge (dz i) (dz k) +
            alg.wedge (dz j) (dz k) := by
    rw [hsub_l, hsub_r, hsub_r, halt (dz k),
      hanti (dz j) (dz i), hanti (dz k) (dz i)]
    abel
  have hv :
      alg.wedge (dz k - dz i) (dz i - dz j) =
        alg.wedge (dz i) (dz j) -
          alg.wedge (dz i) (dz k) +
            alg.wedge (dz j) (dz k) := by
    rw [hsub_l, hsub_r, hsub_r, halt (dz i),
      hanti (dz k) (dz i), hanti (dz k) (dz j)]
    abel
  rw [ht, hu, hv]
  let Δ :=
    alg.wedge (dz i) (dz j) -
      alg.wedge (dz i) (dz k) +
        alg.wedge (dz j) (dz k)
  change (c i j * c j k) • Δ +
      (c j k * c k i) • Δ +
      (c k i * c i j) • Δ = 0
  rw [← add_smul, ← add_smul, hpartial, zero_smul]

/-- Arnold's d log relation on Conf n. -/
theorem dlog_arnold_relation
    {n : ℕ} {K : Type*} [Field K]
    {M : Type*} [AddCommGroup M] [Module K M]
    (alg : ExteriorFormAlgebra (R := K) M)
    (z : Conf n K) (dz : Fin n → M)
    {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    alg.wedge (dlogCoefficient z i j • (dz i - dz j))
        (dlogCoefficient z j k • (dz j - dz k)) +
      alg.wedge (dlogCoefficient z j k • (dz j - dz k))
        (dlogCoefficient z k i • (dz k - dz i)) +
      alg.wedge (dlogCoefficient z k i • (dz k - dz i))
        (dlogCoefficient z i j • (dz i - dz j)) = 0 := by
  apply finite_arnold_relation alg
    (fun a b => dlogCoefficient z a b) dz
      (dlog_partial_fraction z hij hjk hik)

/-- Indexed infinitesimal braid residue data. -/
structure InfinitesimalBraidResidues
    (n : ℕ) (A : Type*) [Ring A] where
  residue : Fin n → Fin n → A
  symmetric : ∀ i j, residue i j = residue j i
  disjoint_commute :
    ∀ i j k l,
      i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      bracket (residue i j) (residue k l) = 0
  cyclic_commute :
    ∀ i j k,
      i ≠ j → j ≠ k → i ≠ k →
      bracket (residue i j) (residue j k) =
        bracket (residue j k) (residue k i) ∧
      bracket (residue j k) (residue k i) =
        bracket (residue k i) (residue i j)

/-- The three-point KZ curvature term at a finite triple. -/
def tripleCurvature
    {n : ℕ} {K : Type*} [Field K]
    (alg : ExteriorFormAlgebra (R := K) K)
    (z : Conf n K) (dz : Fin n → K)
    (R : InfinitesimalBraidResidues n K)
    (i j k : Fin n) : K :=
  alg.wedge (dlogForm z dz i j) (dlogForm z dz j k) *
      bracket (R.residue i j) (R.residue j k) +
    alg.wedge (dlogForm z dz j k) (dlogForm z dz k i) *
      bracket (R.residue j k) (R.residue k i) +
    alg.wedge (dlogForm z dz k i) (dlogForm z dz i j) *
      bracket (R.residue k i) (R.residue i j)

/-- Every admissible triple has zero KZ curvature. -/
theorem tripleCurvature_zero
    {n : ℕ} {K : Type*} [Field K]
    (alg : ExteriorFormAlgebra (R := K) K)
    (z : Conf n K) (dz : Fin n → K)
    (R : InfinitesimalBraidResidues n K)
    {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    tripleCurvature alg z dz R i j k = 0 := by
  unfold tripleCurvature
  have hArnold := dlog_arnold_relation alg z dz hij hjk hik
  simp only [dlogForm] at hArnold ⊢
  have h1 := (R.cyclic_commute i j k hij hjk hik).1
  have h2 := (R.cyclic_commute i j k hij hjk hik).2
  rw [h1, h2, ← add_mul, ← add_mul, hArnold, zero_mul]

/-- The complete ordered sum over all finite triples.  Repeated-index terms are
defined as zero, so the sum is exactly over admissible triples. -/
def totalTripleCurvature
    {n : ℕ} {K : Type*} [Field K]
    (alg : ExteriorFormAlgebra (R := K) K)
    (z : Conf n K) (dz : Fin n → K)
    (R : InfinitesimalBraidResidues n K) : K :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    if h : i ≠ j ∧ j ≠ k ∧ i ≠ k then
      tripleCurvature alg z dz R i j k
    else 0

/-- Complete finite sum-over-all-triples KZ cancellation. -/
theorem totalTripleCurvature_zero
    {n : ℕ} {K : Type*} [Field K]
    (alg : ExteriorFormAlgebra (R := K) K)
    (z : Conf n K) (dz : Fin n → K)
    (R : InfinitesimalBraidResidues n K) :
    totalTripleCurvature alg z dz R = 0 := by
  classical
  unfold totalTripleCurvature
  refine Finset.sum_eq_zero (fun i hi => ?_)
  refine Finset.sum_eq_zero (fun j hj => ?_)
  refine Finset.sum_eq_zero (fun k hk => ?_)
  split
  · rename_i h
    exact tripleCurvature_zero alg z dz R h.1 h.2.1 h.2.2
  · rfl

/-- Disjoint residue terms vanish pointwise, supplying the other summand in
the standard KZ curvature decomposition. -/
theorem disjoint_curvature_zero
    {n : ℕ} {K : Type*} [Field K]
    (R : InfinitesimalBraidResidues n K)
    {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) :
    bracket (R.residue i j) (R.residue k l) = 0 :=
  R.disjoint_commute i j k l hij hkl hik hil hjk hjl

end InfoGeometry.Canonical.IndexedArnoldKZComplex
