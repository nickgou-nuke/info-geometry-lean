import proofs.HestenesHyperbolicDoubling

/-!
# Two products on the real carrier of `Cl⁺(1,3)`

The ordinary product is the associative Clifford product.  A second product
is transported from the split Cayley--Dickson doubling of the quaternion
rotation algebra.  The products share a carrier but not their algebra laws.
-/

noncomputable section
namespace ClPlus14DualProduct

open HestenesEvenPauliEquiv
open HestenesHyperbolicDoubling
open TwoSheetThreeColorWeyl

abbrev EvenAlgebra := HestenesCl14.ClPlus14
abbrev Sheet := HestenesPauliSheetBridge.Sheet
abbrev SplitDouble := HestenesHyperbolicDoubling.Carrier
abbrev HRot := Quaternion ℝ

def complexParts (r s : ℝ) : ℂ := ⟨r, s⟩

def pauliToDoubleFun (A : Sheet) : SplitDouble :=
  let z0 := pauliCoeff0 A
  let z1 := pauliCoeff1 A
  let z2 := pauliCoeff2 A
  let z3 := pauliCoeff3 A
  (⟨z0.re, z1.re, z2.re, z3.re⟩,
   ⟨z0.im, z1.im, z2.im, z3.im⟩)

def doubleToPauliFun (x : SplitDouble) : Sheet :=
  complexParts x.1.re x.2.re • pauli0 +
    complexParts x.1.imI x.2.imI • pauli1 +
    complexParts x.1.imJ x.2.imJ • pauli2 +
    complexParts x.1.imK x.2.imK • pauli3

def pauliToDouble : Sheet →ₗ[ℝ] SplitDouble where
  toFun := pauliToDoubleFun
  map_add' A B := by
    apply Prod.ext <;> apply QuaternionAlgebra.ext <;>
      simp [pauliToDoubleFun, pauliCoeff0, pauliCoeff1, pauliCoeff2,
        pauliCoeff3] <;> ring
  map_smul' r A := by
    apply Prod.ext <;> apply QuaternionAlgebra.ext <;>
      simp [pauliToDoubleFun, pauliCoeff0, pauliCoeff1, pauliCoeff2,
        pauliCoeff3, Complex.mul_re, Complex.mul_im] <;> ring

def doubleToPauli : SplitDouble →ₗ[ℝ] Sheet where
  toFun := doubleToPauliFun
  map_add' x y := by
    ext i j
    apply Complex.ext <;>
      simp [doubleToPauliFun, complexParts] <;> ring_nf
  map_smul' r x := by
    ext i j
    apply Complex.ext <;>
      simp [doubleToPauliFun, complexParts] <;> ring_nf

theorem pauliToDouble_doubleToPauli (x : SplitDouble) :
    pauliToDouble (doubleToPauli x) = x := by
  rcases x with ⟨a, b⟩
  apply Prod.ext <;> apply QuaternionAlgebra.ext <;>
    simp [pauliToDouble, doubleToPauli, pauliToDoubleFun, doubleToPauliFun,
      complexParts, pauliCoeff0, pauliCoeff1, pauliCoeff2, pauliCoeff3,
      pauli0, pauli1, pauli2, pauli3] <;>
    ring_nf <;> try rw [Complex.I_sq] <;> ring

theorem doubleToPauli_pauliToDouble (A : Sheet) :
    doubleToPauli (pauliToDouble A) = A := by
  ext i j <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [pauliToDouble, doubleToPauli, pauliToDoubleFun, doubleToPauliFun,
      complexParts, pauliCoeff0, pauliCoeff1, pauliCoeff2, pauliCoeff3,
      pauli0, pauli1, pauli2, pauli3] <;> ring_nf

def pauliDoubleLinearEquiv : Sheet ≃ₗ[ℝ] SplitDouble where
  toLinearMap := pauliToDouble
  invFun := doubleToPauli
  left_inv := doubleToPauli_pauliToDouble
  right_inv := pauliToDouble_doubleToPauli

def clPlusDoubleLinearEquiv : EvenAlgebra ≃ₗ[ℝ] SplitDouble :=
  HestenesEvenPauliEquiv.clPlusPauliAlgEquiv.toLinearEquiv.trans
    pauliDoubleLinearEquiv

/-- The split-octonion product transported to the real carrier of
`Cl⁺(1,3)`.  It is deliberately distinct from the existing `Mul` instance. -/
def splitProduct (x y : EvenAlgebra) : EvenAlgebra :=
  clPlusDoubleLinearEquiv.symm
    (clPlusDoubleLinearEquiv x * clPlusDoubleLinearEquiv y)

theorem splitProduct_map (x y : EvenAlgebra) :
    clPlusDoubleLinearEquiv (splitProduct x y) =
      clPlusDoubleLinearEquiv x * clPlusDoubleLinearEquiv y := by
  simp [splitProduct]

theorem splitProduct_left_alternative (x y : EvenAlgebra) :
    splitProduct x (splitProduct x y) =
      splitProduct (splitProduct x x) y := by
  apply clPlusDoubleLinearEquiv.injective
  simp only [splitProduct_map]
  exact HestenesHyperbolicDoubling.left_alternative _ _

theorem splitProduct_right_alternative (x y : EvenAlgebra) :
    splitProduct (splitProduct x y) y =
      splitProduct x (splitProduct y y) := by
  apply clPlusDoubleLinearEquiv.injective
  simp only [splitProduct_map]
  exact HestenesHyperbolicDoubling.right_alternative _ _

def ellCl : EvenAlgebra := clPlusDoubleLinearEquiv.symm ell
def qiCl : EvenAlgebra := clPlusDoubleLinearEquiv.symm (embed qi)
def qjCl : EvenAlgebra := clPlusDoubleLinearEquiv.symm (embed qj)

theorem splitProduct_nonassociative :
    splitProduct (splitProduct ellCl qiCl) qjCl ≠
      splitProduct ellCl (splitProduct qiCl qjCl) := by
  intro h
  have hm := congrArg clPlusDoubleLinearEquiv h
  apply HestenesHyperbolicDoubling.nonassociative_witness
  simpa only [ellCl, qiCl, qjCl, splitProduct_map,
    LinearEquiv.apply_symm_apply] using hm

theorem clifford_product_associative (x y z : EvenAlgebra) :
    (x * y) * z = x * (y * z) := mul_assoc _ _ _

theorem dual_products_are_distinct :
    ∃ x y z : EvenAlgebra,
      (x * y) * z = x * (y * z) ∧
      splitProduct (splitProduct x y) z ≠
        splitProduct x (splitProduct y z) := by
  exact ⟨ellCl, qiCl, qjCl, mul_assoc _ _ _, splitProduct_nonassociative⟩

end ClPlus14DualProduct
end noncomputable section
