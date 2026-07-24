import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.NormalizedLogDetTower

Finite determinant-normalization lemma for the binary tensor tower.

If the stage embedding doubles the matrix size and squares the determinant,

  det(A ⊗ I₂) = det(A)^2,

then the normalized logarithmic determinant is invariant:

  (1 / 2^(N+1)) log(det(A)^2)
    =
  (1 / 2^N) log(det(A)).

This is the finite scalar core behind the stabilized determinant/Fuglede-Kadison
trace-log intuition.

No tensor API.
No operator-algebra claim.
No wrappers.
All statements below are fully proved.
-/

namespace InfoGeometry.Canonical.NormalizedLogDetTower

/--
General scalar normalization step.

If a determinant-like positive scalar `detNew` is the square of `detOld`,
and the dimension normalization doubles from `d` to `2*d`, then the normalized
log determinant is unchanged.
-/
theorem normalizedLogDet_stable_of_square
    {d detOld detNew : ℝ}
    (hd : d ≠ 0)
    (hdetOld : 0 < detOld)
    (hdetNew : detNew = detOld ^ 2) :
    (1 / ((2 : ℝ) * d)) * Real.log detNew
      =
    (1 / d) * Real.log detOld := by
  subst detNew

  have hlog : Real.log (detOld ^ 2) = (2 : ℝ) * Real.log detOld := by
    have hne : detOld ≠ 0 := ne_of_gt hdetOld
    rw [show detOld ^ 2 = detOld * detOld by ring]
    rw [Real.log_mul hne hne]
    ring

  rw [hlog]
  field_simp [hd]

/--
Binary tensor-tower normalization step.

At stage `N`, the dimension is `2^N`.  After tensoring by `I₂`, the dimension
is `2^(N+1)` and the determinant squares.

This proves the exact stabilization identity:

  2^-(N+1) log(det²) = 2^-N log(det).
-/
theorem normalizedLogDet_binaryTower_step
    (N : Nat)
    {detA : ℝ}
    (hdetA : 0 < detA) :
    (1 / ((2 : ℝ) ^ (N + 1))) * Real.log (detA ^ 2)
      =
    (1 / ((2 : ℝ) ^ N)) * Real.log detA := by
  have hpowN : ((2 : ℝ) ^ N) ≠ 0 :=
    pow_ne_zero N (by norm_num : (2 : ℝ) ≠ 0)

  have hlog : Real.log (detA ^ 2) = (2 : ℝ) * Real.log detA := by
    have hne : detA ≠ 0 := ne_of_gt hdetA
    rw [show detA ^ 2 = detA * detA by ring]
    rw [Real.log_mul hne hne]
    ring

  rw [hlog]
  rw [pow_succ]
  field_simp [hpowN]

/--
Named form for the tensor embedding `A ↦ A ⊗ I₂`.

The theorem assumes only the determinant-squaring fact.  It does not construct
Kronecker products.
-/
theorem normalizedLogDet_tensorId2_step
    (N : Nat)
    {detA detTensor : ℝ}
    (hdetA : 0 < detA)
    (hdetTensor : detTensor = detA ^ 2) :
    (1 / ((2 : ℝ) ^ (N + 1))) * Real.log detTensor
      =
    (1 / ((2 : ℝ) ^ N)) * Real.log detA := by
  rw [hdetTensor]
  exact normalizedLogDet_binaryTower_step N hdetA

/--
Equivalent additive form.

The logarithmic determinant increment caused by tensoring with `I₂` is exactly
balanced by the doubled normalization.
-/
theorem normalizedLogDet_increment_cancelled
    (N : Nat)
    {detA : ℝ}
    (hdetA : 0 < detA) :
    (1 / ((2 : ℝ) ^ (N + 1))) *
        (Real.log (detA ^ 2) - (2 : ℝ) * Real.log detA)
      =
    0 := by
  have hne : detA ≠ 0 := ne_of_gt hdetA
  have hlog : Real.log (detA ^ 2) = (2 : ℝ) * Real.log detA := by
    rw [show detA ^ 2 = detA * detA by ring]
    rw [Real.log_mul hne hne]
    ring
  rw [hlog]
  ring

end InfoGeometry.Canonical.NormalizedLogDetTower
