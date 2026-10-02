import InfoGeometry.Thermodynamics.MassieuPlanckArithmetics

namespace InfoGeometry.Thermodynamics.MassieuPlanckArithmeticsTests

open InfoGeometry.Thermodynamics.MassieuPlanckArithmetics

-- Test 1: Poset chain
theorem test_poset_chain :
    precedes Archetype.massieuPotential Archetype.primeMode ∧
    precedes Archetype.massieuPotential Archetype.negentropy ∧
    precedes Archetype.negentropy Archetype.fisherCurvature ∧
    precedes Archetype.fisherCurvature Archetype.seamVertex :=
  causal_chain

-- Test 2: Prime Massieu is Polylog1
theorem test_prime_massieu (x : ℝ) :
    primeMassieu x = polylog1 x :=
  primeMassieu_eq_polylog1 x

-- Test 3: Logit Negentropy Legendre duality
theorem test_logit_negentropy (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p * Real.log (p / (1 - p)) - Real.log (1 / (1 - p)) =
      p * Real.log p + (1 - p) * Real.log (1 - p) :=
  logit_negentropy p hp hp1

-- Test 4: Partition function positivity
theorem test_massieuZ_pos (θ : ℝ) :
    0 < massieuZ θ :=
  massieuZ_pos θ

-- Test 5: Softmax expectation at zero
theorem test_softmax_zero :
    softmax 0 = 1 / 2 :=
  softmax_zero

-- Test 6: Fisher curvature at zero
theorem test_fisher_curvature_at_zero :
    fisherCurvature 0 = 1 / 4 :=
  fisher_curvature_at_zero

-- Test 7: Fisher curvature ceiling
theorem test_fisher_curvature_ceiling (p : ℝ) :
    p * (1 - p) ≤ 1 / 4 :=
  fisher_curvature_le_quarter p

-- Test 8: Negentropy at half
theorem test_negentropy_at_half :
    (1 / 2 : ℝ) * Real.log (1 / 2) +
      (1 - (1 / 2 : ℝ)) * Real.log (1 - (1 / 2 : ℝ)) =
      -Real.log 2 :=
  negentropy_at_half

#print axioms test_poset_chain
#print axioms test_prime_massieu
#print axioms test_logit_negentropy
#print axioms test_massieuZ_pos
#print axioms test_softmax_zero
#print axioms test_fisher_curvature_at_zero
#print axioms test_fisher_curvature_ceiling
#print axioms test_negentropy_at_half

end InfoGeometry.Thermodynamics.MassieuPlanckArithmeticsTests
