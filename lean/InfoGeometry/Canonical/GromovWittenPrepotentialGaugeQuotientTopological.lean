import InfoGeometry.Canonical.GromovWittenPrepotentialGaugeQuotient
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Topology of the finite prepotential gauge quotient

The coefficient tensor carries the induced finite product topology, and the
permutation quotient carries the corresponding quotient topology.  The only
descended observable used here is the finite total coefficient sum.
-/

namespace InfoGeometry.Canonical

open CategoryTheory
open scoped BigOperators

instance prepotentialTopologicalSpace (dim : ℕ) :
    TopologicalSpace (GromovWittenPrepotential dim) :=
  TopologicalSpace.induced
    (fun F : GromovWittenPrepotential dim => F.F3) inferInstance

instance prepotentialGaugeQuotientTopologicalSpace (dim : ℕ) :
    TopologicalSpace (GromovWittenPrepotentialGaugeQuotient dim) :=
  TopologicalSpace.coinduced
    (Quotient.mk (prepotentialGaugeSetoid dim)) inferInstance

def prepotentialGaugeQuotientTopCat (dim : ℕ) :
    TopCat.of (GromovWittenPrepotential dim) ⟶
      TopCat.of (GromovWittenPrepotentialGaugeQuotient dim) :=
  TopCat.ofHom
    { toFun := Quotient.mk (prepotentialGaugeSetoid dim)
      continuous_toFun := continuous_coinduced_rng }

theorem continuous_prepotentialGaugeQuotient_mk (dim : ℕ) :
    Continuous
      (Quotient.mk (prepotentialGaugeSetoid dim) :
        GromovWittenPrepotential dim →
          GromovWittenPrepotentialGaugeQuotient dim) :=
  continuous_coinduced_rng

theorem continuous_totalPrepotentialCoefficient {dim : ℕ} :
    Continuous (totalPrepotentialCoefficient :
      GromovWittenPrepotential dim → ℝ) := by
  unfold totalPrepotentialCoefficient
  apply continuous_finset_sum
  intro t ht
  have hF3 : Continuous (fun F : GromovWittenPrepotential dim => F.F3) :=
    continuous_induced_dom
  have hi : Continuous (fun F : GromovWittenPrepotential dim => F.F3 t.1) :=
    (continuous_apply t.1).comp hF3
  have hij : Continuous
      (fun F : GromovWittenPrepotential dim => F.F3 t.1 t.2.1) :=
    (continuous_apply t.2.1).comp hi
  exact (continuous_apply t.2.2).comp hij

theorem continuous_totalPrepotentialCoefficientOnGaugeQuotient {dim : ℕ} :
    Continuous (totalPrepotentialCoefficientOnGaugeQuotient :
      GromovWittenPrepotentialGaugeQuotient dim → ℝ) := by
  apply (continuous_totalPrepotentialCoefficient (dim := dim)).quotient_lift

theorem totalPrepotentialCoefficientOnGaugeQuotient_levelSet_isClosed
    {dim : ℕ} (c : ℝ) :
    IsClosed {q : GromovWittenPrepotentialGaugeQuotient dim |
      totalPrepotentialCoefficientOnGaugeQuotient q = c} := by
  simpa only [Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({c} : Set ℝ)).preimage
      (continuous_totalPrepotentialCoefficientOnGaugeQuotient (dim := dim))

theorem continuous_prepotentialCoefficientEnergy {dim : ℕ} :
    Continuous (prepotentialCoefficientEnergy :
      GromovWittenPrepotential dim → ℝ) := by
  unfold prepotentialCoefficientEnergy
  apply continuous_finset_sum
  intro t ht
  have hF3 : Continuous (fun F : GromovWittenPrepotential dim => F.F3) :=
    continuous_induced_dom
  have hi : Continuous (fun F : GromovWittenPrepotential dim => F.F3 t.1) :=
    (continuous_apply t.1).comp hF3
  have hij : Continuous
      (fun F : GromovWittenPrepotential dim => F.F3 t.1 t.2.1) :=
    (continuous_apply t.2.1).comp hi
  exact ((continuous_apply t.2.2).comp hij).pow 2

theorem continuous_prepotentialCoefficientEnergyOnGaugeQuotient {dim : ℕ} :
    Continuous (prepotentialCoefficientEnergyOnGaugeQuotient :
      GromovWittenPrepotentialGaugeQuotient dim → ℝ) := by
  apply (continuous_prepotentialCoefficientEnergy (dim := dim)).quotient_lift

theorem prepotentialCoefficientEnergy_nonneg {dim : ℕ}
    (F : GromovWittenPrepotential dim) :
    0 ≤ prepotentialCoefficientEnergy F := by
  unfold prepotentialCoefficientEnergy
  exact Finset.sum_nonneg (fun t ht => sq_nonneg _)

theorem prepotentialCoefficientEnergyOnGaugeQuotient_nonneg {dim : ℕ}
    (q : GromovWittenPrepotentialGaugeQuotient dim) :
    0 ≤ prepotentialCoefficientEnergyOnGaugeQuotient q := by
  refine Quotient.inductionOn q ?_
  intro F
  simpa only [prepotentialCoefficientEnergyOnGaugeQuotient_mk] using
    prepotentialCoefficientEnergy_nonneg F

theorem prepotentialCoefficientEnergyOnGaugeQuotient_sublevel_isClosed
    {dim : ℕ} (c : ℝ) :
    IsClosed {q : GromovWittenPrepotentialGaugeQuotient dim |
      prepotentialCoefficientEnergyOnGaugeQuotient q ≤ c} := by
  change IsClosed
    (prepotentialCoefficientEnergyOnGaugeQuotient ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_prepotentialCoefficientEnergyOnGaugeQuotient (dim := dim))

theorem prepotentialCoefficientEnergyOnGaugeQuotient_unique
    {dim : ℕ}
    (f : GromovWittenPrepotentialGaugeQuotient dim → ℝ)
    (hf : ∀ F : GromovWittenPrepotential dim,
      f (Quotient.mk (prepotentialGaugeSetoid dim) F) =
        prepotentialCoefficientEnergy F) :
    f = prepotentialCoefficientEnergyOnGaugeQuotient := by
  funext q
  refine Quotient.inductionOn q ?_
  intro F
  rw [hf, prepotentialCoefficientEnergyOnGaugeQuotient_mk]

theorem prepotentialCoefficientEnergyOnGaugeQuotient_levelSet_isClosed
    {dim : ℕ} (c : ℝ) :
    IsClosed {q : GromovWittenPrepotentialGaugeQuotient dim |
      prepotentialCoefficientEnergyOnGaugeQuotient q = c} := by
  simpa only [Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({c} : Set ℝ)).preimage
      (continuous_prepotentialCoefficientEnergyOnGaugeQuotient (dim := dim))

end InfoGeometry.Canonical
