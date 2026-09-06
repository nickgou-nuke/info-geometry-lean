import Mathlib.Tactic

/-!
# Super Partition Ratios and the Berezinian

Finite scalar model for the boson/fermion ratio layer.

For a local prime mode with Boltzmann weight `x`:

* bosonic factor: `1 / (1 - x)`;
* fermionic factor: `1 + x`;
* super-ratio: `(1 + x) / (1 - x)`.

For a diagonal `1|1` supermatrix with even block `a` and odd block `b`, the
Berezinian is `a / b`.  Thus the local super partition ratio is the
Berezinian of the diagonal supermatrix with even entry `1 + x` and odd entry
`1 - x`.

The Cayley expression appears as the same scalar ratio.  With
`x = exp (ε * y)`, this is the finite exponential chart
`(1 + exp(εy)) / (1 - exp(εy))`.
-/

noncomputable section

def bosonicLocalFactor (x : ℝ) : ℝ :=
  (1 - x)⁻¹

def fermionicLocalFactor (x : ℝ) : ℝ :=
  1 + x

def superPartitionRatio (x : ℝ) : ℝ :=
  fermionicLocalFactor x / (1 - x)

def diagonalBerezinian (even odd : ℝ) : ℝ :=
  even / odd

def cayleyPartition (x : ℝ) : ℝ :=
  (1 + x) / (1 - x)

def exponentialCayleyPartition (ε y : ℝ) : ℝ :=
  cayleyPartition (Real.exp (ε * y))

theorem superPartitionRatio_eq_cayley (x : ℝ) :
    superPartitionRatio x = cayleyPartition x := by
  simp [superPartitionRatio, cayleyPartition, fermionicLocalFactor]

theorem superPartitionRatio_eq_berezinian (x : ℝ) :
    superPartitionRatio x = diagonalBerezinian (1 + x) (1 - x) := by
  simp [superPartitionRatio, diagonalBerezinian, fermionicLocalFactor]

theorem local_super_product {x : ℝ} (hx : x ≠ 1) :
    fermionicLocalFactor x * bosonicLocalFactor x = superPartitionRatio x := by
  have _ : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  simp [fermionicLocalFactor, bosonicLocalFactor, superPartitionRatio,
    div_eq_mul_inv]

theorem cayleyPartition_inversion {x : ℝ} (hx_one : x ≠ 1) (hx_neg : x ≠ -1) :
    cayleyPartition (-x) = (cayleyPartition x)⁻¹ := by
  unfold cayleyPartition
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx_one)
  have h2 : 1 + x ≠ 0 := by
    intro h
    apply hx_neg
    linarith
  have h3 : 1 - -x ≠ 0 := by
    intro h
    apply hx_neg
    linarith
  field_simp [h1, h2, h3]
  ring

theorem exponentialCayleyPartition_eq_berezinian (ε y : ℝ) :
    exponentialCayleyPartition ε y =
      diagonalBerezinian (1 + Real.exp (ε * y)) (1 - Real.exp (ε * y)) := by
  simp [exponentialCayleyPartition, cayleyPartition, diagonalBerezinian]

theorem exponential_chart_zero :
    Real.exp (0 : ℝ) = 1 := by
  simp

/-- Consolidated finite super-ratio/Berezinian package. -/
theorem super_partition_berezinian_synthesis :
    (∀ x, superPartitionRatio x = cayleyPartition x) ∧
    (∀ x, superPartitionRatio x = diagonalBerezinian (1 + x) (1 - x)) ∧
    (∀ x, x ≠ 1 → fermionicLocalFactor x * bosonicLocalFactor x =
      superPartitionRatio x) ∧
    (∀ ε y, exponentialCayleyPartition ε y =
      diagonalBerezinian (1 + Real.exp (ε * y)) (1 - Real.exp (ε * y))) ∧
    Real.exp (0 : ℝ) = 1 := by
  exact ⟨superPartitionRatio_eq_cayley, superPartitionRatio_eq_berezinian,
    fun x hx => local_super_product hx, exponentialCayleyPartition_eq_berezinian,
    exponential_chart_zero⟩

end noncomputable section
