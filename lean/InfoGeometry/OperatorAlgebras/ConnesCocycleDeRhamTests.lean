import InfoGeometry.OperatorAlgebras.ConnesCocycleDeRham

namespace InfoGeometry.OperatorAlgebras.ConnesCocycleDeRhamTests

open InfoGeometry.OperatorAlgebras.ConnesCocycleDeRham

-- Test 1: Maurer-Cartan form constancy
theorem test_maurer_cartan_const (c t : ℝ) :
    let u := Real.exp (c * t)
    let du_dt := c * Real.exp (c * t)
    (1 / u) * du_dt = c :=
  maurer_cartan_one_parameter_group c t

-- Test 2: Araki relative entropy decomposition
theorem test_araki_decomposition (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    araki_relative_entropy p = Real.log 2 + negentropy p :=
  araki_relative_entropy_decomposition p hp0 hp1

-- Test 3: Vanishing at p = 1/2
theorem test_araki_at_half :
    araki_relative_entropy (1 / 2) = 0 :=
  araki_relative_entropy_at_half

-- Test 4: Fisher metric ceiling
theorem test_fisher_bound (p : ℝ) :
    relative_entropy_fisher_metric p ≤ 1 / 4 :=
  relative_entropy_curvature_bound p

-- Test 5: Fisher metric at p = 1/2
theorem test_fisher_at_half :
    relative_entropy_fisher_metric (1 / 2) = 1 / 4 :=
  relative_entropy_curvature_max

#print axioms test_maurer_cartan_const
#print axioms test_araki_decomposition
#print axioms test_araki_at_half
#print axioms test_fisher_bound
#print axioms test_fisher_at_half

end InfoGeometry.OperatorAlgebras.ConnesCocycleDeRhamTests
