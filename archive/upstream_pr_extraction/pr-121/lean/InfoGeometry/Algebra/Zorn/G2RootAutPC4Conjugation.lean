import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment

/-
# PC‑conjugation lemma for the fourth generator

We prove the matrix equality

```lean
autMatrix (c * pc4Aut * c⁻¹) = C5
```
using the already‑available certificates `autMatrix_pc4Aut_eq_C3` and the matrix
representations of `c` and `c⁻¹`.  From this we obtain the group‑level equality
`c * pc4Aut * c⁻¹ = pc6Aut` by `autMatrix_injective`.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootAutPC4Conjugation

open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment

/-- Conjugating `pc4Aut` by `c` yields the matrix `C5`. -/
theorem autMatrix_c_conj_pc4_eq_C5 :
    autMatrix (c * pc4Aut * c⁻¹) = C5 := by
  -- matrix multiplication is reversed for `autMatrix`
  rw [autMatrix_mul, autMatrix_mul]
  rw [autMatrix_pc4Aut_eq_C3]
  rw [autMatrix_c, autMatrix_c_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The group‑level conjugation of `pc4Aut` by `c` gives the generator `pc6Aut`. -/
theorem c_conj_pc4_eq_pc6 :
    c * pc4Aut * c⁻¹ = pc6Aut := by
  apply autMatrix_injective
  rw [autMatrix_c_conj_pc4_eq_C5, autMatrix_pc6Aut_eq_C5]

end InfoGeometry.Algebra.Zorn.G2RootAutPC4Conjugation
