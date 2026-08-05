import Mathlib

/-!
# Sinkhorn scaling and Amari-style coordinate factors

This owner records the algebraic identity behind a Sinkhorn row or column
update.  It does not claim KL optimality, an actual `m`-projection, or
convergence of an alternating iteration.  Those require positivity,
nonvanishing marginals, a divergence contract, and an optimization theorem.
-/

namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections

noncomputable section

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev TransportPlan (I J : Type*) := I → J → ℝ

def sinkhornRowUpdate (P : TransportPlan I J) (mu : I → ℝ) :
    TransportPlan I J :=
  fun i j => (mu i / ∑ k : J, P i k) * P i j

def sinkhornColUpdate (P : TransportPlan I J) (nu : J → ℝ) :
    TransportPlan I J :=
  fun i j => (nu j / ∑ k : I, P k j) * P i j

def amariEScaleRow (P : TransportPlan I J) (u : I → ℝ) :
    TransportPlan I J :=
  fun i j => u i * P i j

def amariEScaleCol (P : TransportPlan I J) (v : J → ℝ) :
    TransportPlan I J :=
  fun i j => v j * P i j

def rowConstraintFactor (P : TransportPlan I J) (mu : I → ℝ) : I → ℝ :=
  fun i => mu i / ∑ k : J, P i k

def colConstraintFactor (P : TransportPlan I J) (nu : J → ℝ) : J → ℝ :=
  fun j => nu j / ∑ k : I, P k j

def rowMass (P : TransportPlan I J) (i : I) : ℝ :=
  ∑ j : J, P i j

def colMass (P : TransportPlan I J) (j : J) : ℝ :=
  ∑ i : I, P i j

theorem continuous_rowMass (i : I) :
    Continuous (fun P : TransportPlan I J => rowMass P i) := by
  unfold rowMass
  apply continuous_finset_sum
  intro j hj
  exact (continuous_apply j).comp (continuous_apply i)

theorem continuous_colMass (j : J) :
    Continuous (fun P : TransportPlan I J => colMass P j) := by
  unfold colMass
  apply continuous_finset_sum
  intro i hi
  exact (continuous_apply j).comp (continuous_apply i)

theorem sinkhornRowUpdate_eq_eScale_constraint
    (P : TransportPlan I J) (mu : I → ℝ) :
    sinkhornRowUpdate P mu =
      amariEScaleRow P (rowConstraintFactor P mu) := by
  rfl

theorem sinkhornColUpdate_eq_eScale_constraint
    (P : TransportPlan I J) (nu : J → ℝ) :
    sinkhornColUpdate P nu =
      amariEScaleCol P (colConstraintFactor P nu) := by
  rfl

theorem sinkhornRowUpdate_row_sum
    (P : TransportPlan I J) (mu : I → ℝ) (i : I)
    (hrow : ∑ k : J, P i k ≠ 0) :
    ∑ j : J, sinkhornRowUpdate P mu i j = mu i := by
  unfold sinkhornRowUpdate
  rw [← Finset.mul_sum]
  exact div_mul_cancel₀ _ hrow

theorem sinkhornColUpdate_col_sum
    (P : TransportPlan I J) (nu : J → ℝ) (j : J)
    (hcol : ∑ k : I, P k j ≠ 0) :
    ∑ i : I, sinkhornColUpdate P nu i j = nu j := by
  unfold sinkhornColUpdate
  rw [← Finset.mul_sum]
  exact div_mul_cancel₀ _ hcol

end
end InfoGeometry.Physics.AmariSinkhornAlternatingProjections
