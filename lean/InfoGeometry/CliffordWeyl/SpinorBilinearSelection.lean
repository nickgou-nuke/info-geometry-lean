import InfoGeometry.CliffordWeyl.ChiralIdeals

namespace InfoGeometry.CliffordWeyl.SpinorBilinearSelection

open InfoGeometry.OperatorAlgebra

variable {Carrier : Type*} [Ring Carrier] [Algebra ℝ Carrier]
variable (chirality : ChiralInvolution Carrier)

theorem scalar_selection (metric : Carrier)
    (metricOdd : metric * chirality.chi = -(chirality.chi * metric)) :
    chirality.Pleft * metric * chirality.Pleft = 0 ∧
      chirality.Pleft * metric * chirality.Pright = chirality.Pleft * metric := by
  refine ⟨(diagonal_corners_zero chirality metric metricOdd).1, ?_⟩
  rw [Pleft_mul_swap chirality metric metricOdd, mul_assoc, chirality.Pright_idem]

theorem vector_selection (metric vector : Carrier)
    (metricOdd : metric * chirality.chi = -(chirality.chi * metric))
    (vectorOdd : vector * chirality.chi = -(chirality.chi * vector)) :
    chirality.Pleft * (metric * vector) * chirality.Pright = 0 ∧
      chirality.Pright * (metric * vector) * chirality.Pleft = 0 ∧
      chirality.Pleft * (metric * vector) * chirality.Pleft =
        (metric * vector) * chirality.Pleft := by
  have even := product_commutes_of_anticommutes chirality metric vector metricOdd vectorOdd
  obtain ⟨leftZero, rightZero⟩ := cross_corners_zero chirality (metric * vector) even
  refine ⟨leftZero, rightZero, ?_⟩
  rw [(commute_Pleft chirality (metric * vector) even).eq,
    mul_assoc, chirality.Pleft_idem]

theorem scalar_cross_corner_ne_zero (metric : Carrier)
    (metricOdd : metric * chirality.chi = -(chirality.chi * metric))
    (metricSquare : metric * metric = 1)
    (sectorNonzero : chirality.Pleft ≠ 0) :
    chirality.Pleft * metric * chirality.Pright ≠ 0 := by
  rw [(scalar_selection chirality metric metricOdd).2]
  intro vanishes
  apply sectorNonzero
  calc
    chirality.Pleft = (chirality.Pleft * metric) * metric := by
      rw [mul_assoc, metricSquare, mul_one]
    _ = 0 := by rw [vanishes, zero_mul]

end InfoGeometry.CliffordWeyl.SpinorBilinearSelection
