import InfoGeometry.HodgeCohomology.KreinHodgeObstruction

namespace InfoGeometry.HodgeCohomology.KreinHodgeDiracBounded.Tests

open InfoGeometry.Krein
open KreinSpace
open KreinHodgeObstruction

noncomputable section

example : kreinInner (to_doubled 0 1 : Plane) (to_doubled 0 1) = -1 := by
  rw [krein_inner_prod_l2]
  norm_num

example (state : Plane) :
    kreinInner ((nullDirac * kreinAdjoint nullDirac +
      kreinAdjoint nullDirac * nullDirac) state) state =
    kreinInner ((nullDirac + kreinAdjoint nullDirac) state)
      ((nullDirac + kreinAdjoint nullDirac) state) :=
  krein_hodge_energy nullDirac nullDirac_square state

example :
    LinearMap.ker ((jCLM (H := Plane)).toLinearMap * (jCLM (H := Plane)).toLinearMap) =
      LinearMap.ker (jCLM (H := Plane)).toLinearMap := by
  apply krein_square_kernel_eq_of_commutes_symmetry
  · change kreinAdjoint (jCLM (H := Plane)) = jCLM
    simp [kreinAdjoint]
  · rfl

#print axioms kreinBilin_nondegenerate
#print axioms kreinAdjoint_eq_of_pairing
#print axioms krein_codifferential_square_zero
#print axioms krein_hodge_factorization
#print axioms krein_hodge_self_adjoint
#print axioms krein_hodge_energy
#print axioms krein_square_kernel_eq_of_commutes_symmetry
#print axioms krein_hodge_kernel_eq_of_commutes_symmetry
#print axioms nullDirac_krein_adjoint
#print axioms nullDirac_kernel_counterexample
#print axioms nullDirac_range_eq_kernel
#print axioms nullComplex_exact
#print axioms nullComplex_homology_zero
#print axioms nonzero_exact_closed_coclosed_harmonic

end

end InfoGeometry.HodgeCohomology.KreinHodgeDiracBounded.Tests
