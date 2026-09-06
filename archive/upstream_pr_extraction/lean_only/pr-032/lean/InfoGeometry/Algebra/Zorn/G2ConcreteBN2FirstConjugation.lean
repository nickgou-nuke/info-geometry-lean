import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup

namespace InfoGeometry.Algebra.Zorn.G2ConcreteBN2FirstConjugation

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

/- CAS certificate: SymPy and GAP, using the explicit Lean carrier matrices,
   give the word [0,0,1,0,1,1]. -/
theorem swap01_conj_pc0 :
    swap01Aut⁻¹ * pcGenerator 0 * swap01Aut =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => false | 2 => true
        | 3 => false | 4 => true | 5 => true) := by
  have h_inv : swap01Aut⁻¹ = swap01Aut := by
    rw [inv_eq_iff_mul_eq_one]
    exact swap01Aut_sq
  rw [h_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      G2TwoSylowPCAutomorphisms.pc1Aut, involutiveEquiv,
      pc1Fun, pc3Fun, pc5Fun, basis8, ePlus, eMinus, up0, up1, up2,
      pc6Fun, down0, down1, down2]

/- CAS certificate: SymPy/GAP word [1,0,0,0,1,1]. -/
theorem swap01_conj_pc2 :
    swap01Aut⁻¹ * pcGenerator 2 * swap01Aut =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => true | 1 => false | 2 => false
        | 3 => false | 4 => true | 5 => true) := by
  have h_inv : swap01Aut⁻¹ = swap01Aut := by
    rw [inv_eq_iff_mul_eq_one]
    exact swap01Aut_sq
  rw [h_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      G2TwoSylowPCAutomorphisms.pc3Aut,
      G2TwoSylowPCAutomorphisms.pc3Equiv,
      pc1Fun, pc3Fun, pc5Fun, basis8, ePlus, eMinus, up0, up1, up2,
      pc6Fun, down0, down1, down2]

/- CAS certificate: SymPy/GAP word [0,0,0,0,0,1]. -/
theorem swap01_conj_pc3 :
    swap01Aut⁻¹ * pcGenerator 3 * swap01Aut =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => false | 2 => false
        | 3 => false | 4 => false | 5 => true) := by
  have h_inv : swap01Aut⁻¹ = swap01Aut := by
    rw [inv_eq_iff_mul_eq_one]
    exact swap01Aut_sq
  rw [h_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      G2TwoSylowPCAutomorphisms.pc4Aut, involutiveEquiv, pc4Fun, pc6Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

end InfoGeometry.Algebra.Zorn.G2ConcreteBN2FirstConjugation
