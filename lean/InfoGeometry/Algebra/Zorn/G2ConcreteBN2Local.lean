import InfoGeometry.Algebra.Zorn.G2BNBruhatFramework

namespace InfoGeometry.Algebra.Zorn.G2ConcreteBN2Local

open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/- CAS certificate: CONJ_PC_1_EXP = [1,0,1,1,0,1]. -/
theorem swap01_conj_pc0 :
    swap01Aut⁻¹ * pcGenerator 0 * swap01Aut =
    G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => true
        | 1 => false
        | 2 => true
        | 3 => true
        | 4 => false
        | 5 => true) := by
  have h_inv : swap01Aut⁻¹ = swap01Aut := by
    apply inv_eq_of_mul_eq_one_left
    exact swap01Aut_sq
  rw [h_inv]
  apply automorphism_ext_of_basis
  intro i
  dsimp [G2TwoSylowSubgroup.pcWord, G2TwoSylowSubgroup.pcTerm,
    G2TwoSylowPCAutomorphisms.pcGenerator]
  repeat rw [G2TwoSylowSubgroup.aut_mul_apply]
  change swap01Fun (pc1Fun (swap01Fun (basis8 i))) =
    pc6Fun (pc4Fun (pc3Fun (pc1Fun (basis8 i))))
  fin_cases i <;>
    dsimp [swap01Fun, pc1Fun, pc3Fun, pc4Fun, pc6Fun, basis8] <;>
    rfl

end InfoGeometry.Algebra.Zorn.G2ConcreteBN2Local
