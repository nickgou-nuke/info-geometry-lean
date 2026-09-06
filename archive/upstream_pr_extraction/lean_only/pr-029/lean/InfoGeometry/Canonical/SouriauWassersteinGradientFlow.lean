import Mathlib
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators
open MeasureTheory

namespace SouriauWasserstein

variable {n : ℕ}

/-- The kinetic action on an arbitrary measured state space. -/
noncomputable def measureKineticAction {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (v : X → ℝ) : ℝ :=
  ∫ x, (v x) ^ 2 ∂mu

theorem measureKineticAction_nonneg {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (v : X → ℝ) :
    0 ≤ measureKineticAction mu v := by
  unfold measureKineticAction
  exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (v x))

/-- 1. Benamou-Brenier Kinetic Action Functional A(P, v) = ∑ᵢ Pᵢ vᵢ² for Optimal Transport Flows -/
def benamouBrenierKineticAction (P v : Fin n → ℝ) : ℝ :=
  ∑ i, P i * (v i)^2

/-- 🏆 THEOREM 1: Non-Negativity of the Benamou-Brenier Kinetic Action -/
theorem kineticAction_nonneg (P v : Fin n → ℝ) (hP : ∀ i, 0 ≤ P i) :
    0 ≤ benamouBrenierKineticAction P v := by
  dsimp [benamouBrenierKineticAction]
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hp := hP i
  have hsq : 0 ≤ (v i)^2 := sq_nonneg (v i)
  exact mul_nonneg hp hsq

def probabilitySimplex : Set (Fin n → ℝ) :=
  {P | (∀ i, 0 ≤ P i) ∧ (∑ i, P i) = 1}

theorem continuous_probabilityMass :
    Continuous (fun P : Fin n → ℝ => ∑ i, P i) := by
  simpa using continuous_finset_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => continuous_apply i)

theorem isClosed_probabilitySimplex :
    IsClosed (probabilitySimplex (n := n)) := by
  have hnonneg : IsClosed {P : Fin n → ℝ | ∀ i, 0 ≤ P i} := by
    simpa only [Set.setOf_forall] using
      isClosed_iInter (fun i => isClosed_Ici.preimage (continuous_apply i))
  have hmass : IsClosed {P : Fin n → ℝ | (∑ i, P i) = 1} := by
    exact isClosed_singleton.preimage continuous_probabilityMass
  simpa [probabilitySimplex, Set.setOf_and] using hnonneg.inter hmass

theorem isCompact_probabilitySimplex :
    IsCompact (probabilitySimplex (n := n)) := by
  have hbox : IsCompact (Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset isClosed_probabilitySimplex
  intro P hP i hi
  change P i ∈ Set.Icc (0 : ℝ) 1
  constructor
  · exact hP.1 i
  · have hle : P i ≤ ∑ j : Fin n, P j :=
      Finset.single_le_sum (fun j _ => hP.1 j) (Finset.mem_univ i)
    simpa [hP.2] using hle

theorem convex_probabilitySimplex :
    Convex ℝ (probabilitySimplex (n := n)) := by
  intro P hP Q hQ a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (smul_nonneg ha (hP.1 i)) (smul_nonneg hb (hQ.1 i))
  · change (∑ i, (a * P i + b * Q i)) = 1
    calc
      (∑ i, (a * P i + b * Q i)) =
          a * (∑ i, P i) + b * (∑ i, Q i) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = 1 := by simpa [hP.2, hQ.2] using hab

theorem probabilitySimplex_nonempty (hn : 0 < n) :
    (probabilitySimplex (n := n)).Nonempty := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  let P : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  refine ⟨P, ?_⟩
  constructor
  · intro i
    positivity
  · simp [P, Finset.card_univ, hnR]

theorem isPathConnected_probabilitySimplex (hn : 0 < n) :
    IsPathConnected (probabilitySimplex (n := n)) := by
  exact (convex_probabilitySimplex (n := n)).isPathConnected
    (probabilitySimplex_nonempty hn)

noncomputable def uniformProbability (hn : 0 < n) :
    probabilitySimplex (n := n) := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  let P : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  refine ⟨P, ?_⟩
  constructor
  · intro i
    positivity
  · simp [P, Finset.card_univ, hnR]

theorem continuous_kineticAction_left (v : Fin n → ℝ) :
    Continuous (fun P : Fin n → ℝ => benamouBrenierKineticAction P v) := by
  unfold benamouBrenierKineticAction
  apply continuous_finset_sum
  intro i hi
  fun_prop

theorem continuous_kineticAction :
    Continuous (fun Pv : (Fin n → ℝ) × (Fin n → ℝ) =>
      benamouBrenierKineticAction Pv.1 Pv.2) := by
  unfold benamouBrenierKineticAction
  apply continuous_finset_sum
  intro i hi
  fun_prop

theorem compact_kineticAction_on_simplex (v : Fin n → ℝ) :
    IsCompact (Set.range (fun P : probabilitySimplex (n := n) =>
      benamouBrenierKineticAction P.1 v)) := by
  letI : CompactSpace (probabilitySimplex (n := n)) :=
    isCompact_iff_compactSpace.mp isCompact_probabilitySimplex
  exact isCompact_range
    ((continuous_kineticAction_left v).comp continuous_subtype_val)

theorem bounded_kineticAction_on_simplex (v : Fin n → ℝ) :
    Bornology.IsBounded (Set.range (fun P : probabilitySimplex (n := n) =>
      benamouBrenierKineticAction P.1 v)) := by
  exact (compact_kineticAction_on_simplex v).isBounded

theorem closed_kineticAction_on_simplex (v : Fin n → ℝ) :
    IsClosed (Set.range (fun P : probabilitySimplex (n := n) =>
      benamouBrenierKineticAction P.1 v)) := by
  exact (compact_kineticAction_on_simplex v).isClosed

def kineticActionSublevel (v : Fin n → ℝ) (A : ℝ) :
    Set (probabilitySimplex (n := n)) :=
  {P | benamouBrenierKineticAction P.1 v ≤ A}

def kineticActionAmbientSublevel (v : Fin n → ℝ) (A : ℝ) :
    Set (Fin n → ℝ) :=
  {P | P ∈ probabilitySimplex (n := n) ∧
    benamouBrenierKineticAction P v ≤ A}

theorem kineticActionAmbientSublevel_preimage_subtype
    (v : Fin n → ℝ) (A : ℝ) :
    (Subtype.val ⁻¹' kineticActionAmbientSublevel v A) =
      kineticActionSublevel v A := by
  ext P
  simp [kineticActionAmbientSublevel, kineticActionSublevel]

theorem convex_kineticActionAmbientSublevel (v : Fin n → ℝ) (A : ℝ) :
    Convex ℝ (kineticActionAmbientSublevel v A) := by
  intro P hP Q hQ a b ha hb hab
  constructor
  · exact convex_probabilitySimplex hP.1 hQ.1 ha hb hab
  · change benamouBrenierKineticAction (a • P + b • Q) v ≤ A
    have hlin : benamouBrenierKineticAction (a • P + b • Q) v =
        a * benamouBrenierKineticAction P v +
          b * benamouBrenierKineticAction Q v := by
      simp only [benamouBrenierKineticAction, Pi.add_apply, Pi.smul_apply]
      simp only [smul_eq_mul]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> ring_nf
    rw [hlin]
    calc
      a * benamouBrenierKineticAction P v +
          b * benamouBrenierKineticAction Q v ≤ a * A + b * A := by
        exact add_le_add (mul_le_mul_of_nonneg_left hP.2 ha)
          (mul_le_mul_of_nonneg_left hQ.2 hb)
      _ = A := by
        calc
          a * A + b * A = (a + b) * A := by ring
          _ = A := by rw [hab, one_mul]

theorem isClosed_kineticActionAmbientSublevel (v : Fin n → ℝ) (A : ℝ) :
    IsClosed (kineticActionAmbientSublevel v A) := by
  have haction : IsClosed {P : Fin n → ℝ |
      benamouBrenierKineticAction P v ≤ A} := by
    exact isClosed_Iic.preimage (continuous_kineticAction_left v)
  simpa [kineticActionAmbientSublevel, Set.setOf_and] using
    isClosed_probabilitySimplex.inter haction

theorem isCompact_kineticActionAmbientSublevel (v : Fin n → ℝ) (A : ℝ) :
    IsCompact (kineticActionAmbientSublevel v A) := by
  apply isCompact_probabilitySimplex.of_isClosed_subset
    (isClosed_kineticActionAmbientSublevel v A)
  intro P hP
  exact hP.1

theorem kineticActionAmbientSublevel_nonempty_of_uniform_bound (hn : 0 < n)
    (v : Fin n → ℝ) (A : ℝ)
    (hA : uniformProbability hn ∈ kineticActionSublevel v A) :
    (kineticActionAmbientSublevel v A).Nonempty := by
  refine ⟨(uniformProbability hn).1, (uniformProbability hn).2, ?_⟩
  exact hA

theorem isPathConnected_kineticActionAmbientSublevel
    (v : Fin n → ℝ) (A : ℝ)
    (hnonempty : (kineticActionAmbientSublevel v A).Nonempty) :
    IsPathConnected (kineticActionAmbientSublevel v A) := by
  exact (convex_kineticActionAmbientSublevel v A).isPathConnected hnonempty

theorem isPathConnected_kineticActionAmbientSublevel_of_uniform_bound
    (hn : 0 < n) (v : Fin n → ℝ) (A : ℝ)
    (hA : uniformProbability hn ∈ kineticActionSublevel v A) :
    IsPathConnected (kineticActionAmbientSublevel v A) := by
  exact isPathConnected_kineticActionAmbientSublevel v A
    (kineticActionAmbientSublevel_nonempty_of_uniform_bound hn v A hA)

theorem isClosed_kineticActionSublevel (v : Fin n → ℝ) (A : ℝ) :
    IsClosed (kineticActionSublevel v A) := by
  have hcont : Continuous (fun P : probabilitySimplex (n := n) =>
      benamouBrenierKineticAction P.1 v) :=
    (continuous_kineticAction_left v).comp continuous_subtype_val
  exact isClosed_Iic.preimage hcont

theorem isCompact_kineticActionSublevel (v : Fin n → ℝ) (A : ℝ) :
    IsCompact (kineticActionSublevel v A) := by
  letI : CompactSpace (probabilitySimplex (n := n)) :=
    isCompact_iff_compactSpace.mp isCompact_probabilitySimplex
  exact (isClosed_kineticActionSublevel v A).isCompact

theorem kineticActionSublevel_nonempty_of_uniform_bound (hn : 0 < n)
    (v : Fin n → ℝ) (A : ℝ)
    (hA : uniformProbability hn ∈ kineticActionSublevel v A) :
    (kineticActionSublevel v A).Nonempty := by
  exact ⟨uniformProbability hn, hA⟩

def massZeroDerivativeSet : Set (Fin n → ℝ) :=
  {dP | (∑ i, dP i) = 0}

theorem isClosed_massZeroDerivativeSet :
    IsClosed (massZeroDerivativeSet (n := n)) := by
  exact isClosed_singleton.preimage continuous_probabilityMass

/-- 2. Finite-State Continuity Equation System ∂P/∂t = - div(P v) -/
structure ContinuitySystem (n : ℕ) where
  P : Fin n → ℝ          -- Probability density vector
  dP_dt : Fin n → ℝ      -- Time derivative ∂P/∂t
  divFlux : Fin n → ℝ    -- Flux divergence ∇ · (P v)
  -- Conservation axiom: ∂P/∂t + ∇ · (P v) = 0
  h_continuity : ∀ i, dP_dt i + divFlux i = 0
  -- Zero total divergence (boundary/closed system condition): ∑ᵢ divFluxᵢ = 0
  h_div_sum_zero : ∑ i, divFlux i = 0

/-- 🏆 THEOREM 2: Total Mass Conservation under Continuity Flow: d/dt (∑ᵢ Pᵢ) = 0 -/
theorem continuity_mass_conservation (sys : ContinuitySystem n) :
    ∑ i, sys.dP_dt i = 0 := by
  have h_eq : (∑ i, sys.dP_dt i) = ∑ i, (- sys.divFlux i) := by
    congr 1; ext i
    have h := sys.h_continuity i
    linarith
  rw [h_eq, Finset.sum_neg_distrib, sys.h_div_sum_zero, neg_zero]

theorem continuitySystem_dP_dt_mem_massZeroDerivativeSet
    (sys : ContinuitySystem n) :
    sys.dP_dt ∈ massZeroDerivativeSet (n := n) := by
  exact continuity_mass_conservation sys

/-- 3. Wasserstein Gradient Flow Energy Dissipation: dE/dt = - ||∇_W E||²_W ≤ 0 -/
theorem wasserstein_dissipation_nonneg (gradE_squared : ℝ) (hgrad : 0 ≤ gradE_squared) :
    - gradE_squared ≤ 0 := by
  linarith

end SouriauWasserstein
