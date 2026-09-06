import InfoGeometry.Clifford.Clifford55

namespace InfoGeometry.Clifford.Clifford55

/-!
# Signature boundary of Mathlib's native `pinGroup Q55`

Mathlib's native `pinGroup` includes the `unitary` condition.  For a vector
generator, membership in this native subgroup forces the Clifford norm equation
`Q55 v = -1`.  Positive Witt vectors have `Q55 v = 1`, so they lie outside
this subgroup.  The converse is supplied downstream by
`Cl55WittPinVectorLocus`; this file keeps only the upstream necessary
condition.  It does not identify the subgroup with an independently
constructed real `Pin(5,5)`.
-/

theorem star_ι55_mul_ι55 (v : V55) :
    star (ι55 v) * ι55 v =
      algebraMap ℝ Cl55 (-Q55 v) := by
  rw [CliffordAlgebra.star_ι, neg_mul,
    CliffordAlgebra.ι_sq_scalar, map_neg]

theorem vector_mem_pinGroup_forces_Q_eq_neg_one
    (v : V55) (hv : ι55 v ∈ Pin55) :
    Q55 v = -1 := by
  have hunit :
      star (ι55 v) * ι55 v = 1 :=
    pinGroup.star_mul_self_of_mem hv
  rw [star_ι55_mul_ι55 v] at hunit
  apply (algebraMap ℝ Cl55).injective
  simpa only [map_neg, map_one, neg_neg] using
    congrArg (fun z : Cl55 => -z) hunit

theorem positiveVector_not_mem_pinGroup
    (v : V55) (hv : Q55 v = 1) :
    ι55 v ∉ Pin55 := by
  intro h
  have hq := vector_mem_pinGroup_forces_Q_eq_neg_one v h
  rw [hv] at hq
  norm_num at hq

theorem ePos_not_mem_pinGroup (i : Fin 5) :
    ι55 (e_pos i) ∉ Pin55 := by
  exact e_pos_not_mem_pin55 i

end InfoGeometry.Clifford.Clifford55
