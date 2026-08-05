import InfoGeometry.Clifford.Cl55WittPinKernelEvidence

namespace InfoGeometry.Clifford.Clifford55

/-!
# Signature boundary of Mathlib's native `pinGroup Q55`

Mathlib's native `pinGroup` includes the `unitary` condition.  With the
present Clifford involution, a positive Witt vector has Clifford square `+1`
but star-square norm `-1`, so it is not an element of this native subgroup.
This is an explicit boundary: the subgroup currently used is not yet a proof
of the full real `Pin(5,5)`.
-/

theorem positiveVector_not_mem_pinGroup
    (v : V55) (hv : Q55 v = 1) :
    ι55 v ∉ Pin55 := by
  intro h
  have hunit :
      star (ι55 v) * ι55 v = 1 :=
    pinGroup.star_mul_self_of_mem h
  rw [CliffordAlgebra.star_ι] at hunit
  have hsq :
      ι55 v * ι55 v = algebraMap ℝ Cl55 (Q55 v) := by
    exact CliffordAlgebra.ι_sq_scalar Q55 v
  rw [neg_mul, hsq, hv] at hunit
  have hscalar : (-1 : ℝ) = 1 :=
    by
      apply (algebraMap ℝ Cl55).injective
      simpa only [map_neg, map_one] using hunit
  norm_num at hscalar

theorem ePos_not_mem_pinGroup (i : Fin 5) :
    ι55 (e_pos i) ∉ Pin55 := by
  exact positiveVector_not_mem_pinGroup (e_pos i) (Q55_e_pos i)

end InfoGeometry.Clifford.Clifford55
