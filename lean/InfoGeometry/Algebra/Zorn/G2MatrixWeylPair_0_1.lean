import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment
import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixProductBridge
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv
import InfoGeometry.GroupTheory.DoubleCoset

namespace InfoGeometry.Algebra.Zorn.G2MatrixWeylPair_0_1

open Matrix
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixProductBridge
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.GroupTheory.DoubleCoset

def cMatrix : Matrix (Fin 8) (Fin 8) F2 :=
  cycle012Matrix * swapCartanMatrix

def sMatrix : Matrix (Fin 8) (Fin 8) F2 := swap01Matrix

abbrev LocalWeylG2 := ZMod 6 × Bool

def weylMatrix (p : LocalWeylG2) : Matrix (Fin 8) (Fin 8) F2 :=
  if p.2 then cMatrix ^ p.1.val * sMatrix else cMatrix ^ p.1.val

theorem weylMatrix_zero_false : weylMatrix ((0, false) : LocalWeylG2) = 1 := by
  change (if false then cMatrix ^ (0 : ZMod 6).val * sMatrix else cMatrix ^ (0 : ZMod 6).val) = 1
  have h0 : (0 : ZMod 6).val = 0 := rfl
  rw [h0, pow_zero]
  rfl

theorem weylMatrix_one_false : weylMatrix ((1, false) : LocalWeylG2) = cMatrix := by
  change (if false then cMatrix ^ (1 : ZMod 6).val * sMatrix else cMatrix ^ (1 : ZMod 6).val) = cMatrix
  have h1 : (1 : ZMod 6).val = 1 := rfl
  rw [h1, pow_one]
  rfl

theorem cMatrix_two_two : cMatrix 2 2 = 0 := by
  dsimp [cMatrix, cycle012Matrix, swapCartanMatrix]
  decide

theorem autMatrix_weylNF_zero_false_readback :
    autMatrix (weylNF 0 false) = weylMatrix ((0, false) : LocalWeylG2) := by
  rw [weylNF_zero_false, autMatrix_one]
  exact weylMatrix_zero_false.symm

theorem autMatrix_weylNF_one_false_readback :
    autMatrix (weylNF 1 false) = weylMatrix ((1, false) : LocalWeylG2) := by
  have hweyl : weylNF 1 false = c := by
    change (if false then s * c ^ (1 : ZMod 6).val else c ^ (1 : ZMod 6).val) = c
    have h1 : (1 : ZMod 6).val = 1 := rfl
    rw [h1, pow_one]
    rfl
  rw [hweyl]
  have haut : autMatrix c = cMatrix := InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment.autMatrix_c
  have hmat : weylMatrix ((1, false) : LocalWeylG2) = cMatrix := weylMatrix_one_false
  rw [haut, hmat]

/-- 🏆 THEOREM (Divide-and-Conquer Double Coset Separation):
    The unipotent flow leaves the diagonal entry (2,2) invariant ($M_{2,2} = 1$),
    while the Weyl reflection $c$ moves the basepoint ($c_{2,2} = 0$).
    Thus $U \cdot 1 \cdot U \cap c = \emptyset$ without any brute-force enumeration. -/
theorem matrix_weyl_entry_separation_0_1 (e d : PCExponent) :
    ∃ i j : Fin 8,
      (matrixWord d * weylMatrix ((0, false) : LocalWeylG2) * matrixWord e) i j ≠
        weylMatrix ((1, false) : LocalWeylG2) i j := by
  use 2, 2
  rw [weylMatrix_zero_false, Matrix.mul_one, weylMatrix_one_false]
  rw [matrixWord_mul_matrixWord_bridge]
  rw [matrixWord_entry_two_two (pcCombine e d)]
  rw [cMatrix_two_two]
  decide

theorem autMatrix_weyl_entry_separation_0_1 (e d : PCExponent) :
    ∃ i j : Fin 8,
      (autMatrix (G2TwoSylowSubgroup.pcWord d) *
        autMatrix (weylNF 0 false) *
          autMatrix (G2TwoSylowSubgroup.pcWord e)) i j ≠
        autMatrix (weylNF 1 false) i j := by
  obtain ⟨i, j, h⟩ := matrix_weyl_entry_separation_0_1 e d
  refine ⟨i, j, ?_⟩
  intro h_eq
  apply h
  have h_trans : (autMatrix (G2TwoSylowSubgroup.pcWord d) *
        autMatrix (weylNF 0 false) *
          autMatrix (G2TwoSylowSubgroup.pcWord e)) =
      matrixWord d * weylMatrix ((0, false) : LocalWeylG2) * matrixWord e := by
    rw [autMatrix_pcWord, autMatrix_weylNF_zero_false_readback, autMatrix_pcWord]
  have h_rhs : autMatrix (weylNF 1 false) = weylMatrix ((1, false) : LocalWeylG2) :=
    autMatrix_weylNF_one_false_readback
  have h_lhs : (autMatrix (G2TwoSylowSubgroup.pcWord d) *
        autMatrix (weylNF 0 false) *
          autMatrix (G2TwoSylowSubgroup.pcWord e)) i j =
      (matrixWord d * weylMatrix ((0, false) : LocalWeylG2) * matrixWord e) i j := by
    rw [h_trans]
  have h_rhsi : autMatrix (weylNF 1 false) i j = weylMatrix ((1, false) : LocalWeylG2) i j := by
    rw [h_rhs]
  rw [h_lhs, h_rhsi] at h_eq
  exact h_eq

theorem autMatrix_normalized_weyl_separation_0_1
    (a d : PCExponent) :
    autMatrix (weylNF 1 false) ≠
    autMatrix (G2TwoSylowSubgroup.pcWord a *
        weylNF 0 false * G2TwoSylowSubgroup.pcWord d) := by
  intro h
  obtain ⟨i, j, hsep⟩ := autMatrix_weyl_entry_separation_0_1 a d
  apply hsep
  have h_prod : autMatrix (G2TwoSylowSubgroup.pcWord a * weylNF 0 false * G2TwoSylowSubgroup.pcWord d) =
      autMatrix (G2TwoSylowSubgroup.pcWord d) *
        autMatrix (weylNF 0 false) *
          autMatrix (G2TwoSylowSubgroup.pcWord a) := by
    rw [autMatrix_mul, autMatrix_mul, Matrix.mul_assoc]
  have h_all : autMatrix (weylNF 1 false) =
      autMatrix (G2TwoSylowSubgroup.pcWord d) *
        autMatrix (weylNF 0 false) *
          autMatrix (G2TwoSylowSubgroup.pcWord a) := by
    rw [h, h_prod]
  have h_entry : autMatrix (weylNF 1 false) i j =
      (autMatrix (G2TwoSylowSubgroup.pcWord d) *
        autMatrix (weylNF 0 false) *
          autMatrix (G2TwoSylowSubgroup.pcWord a)) i j := by
    rw [h_all]
  exact h_entry.symm

/-- 🏆 THEOREM: The Weyl generator $c$ is strictly outside the unipotent Sylow subgroup $U$.
    This is an $O(1)$ invariant proof using the isotropic flag entry $M_{2,2} = 1 \ne 0 = c_{2,2}$. -/
theorem c_not_mem_unipotentSubgroup : c ∉ unipotentSubgroup := by
  intro hc
  let z : unipotentSubgroup := ⟨c, hc⟩
  let e :=
    InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv.pcWordEquivUnipotent.symm z
  have he : InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv.pcWordSubtype e = z := by
    exact InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv.pcWordEquivUnipotent.apply_symm_apply z
  have he' : G2TwoSylowSubgroup.pcWord e = c := congrArg Subtype.val he
  have haut : autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 = autMatrix c 2 2 := by
    rw [he']
  rw [autMatrix_pcWord, matrixWord_entry_two_two e] at haut
  rw [InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment.autMatrix_c] at haut
  revert haut
  decide

/-- 🏆 THEOREM (Full Divide-and-Conquer Double Coset Disjointness):
    $U \cdot 1 \cdot U \cap U \cdot c \cdot U = \emptyset$.
    The geometric matrix theory is localized strictly to $c \notin U$, while the double-coset
    separation is discharged by the generic abstract subgroup theorem `disjoint_doubleCoset_one_of_not_mem`. -/
theorem doubleCoset_one_c_disjoint :
    Disjoint (doubleCoset unipotentSubgroup 1 unipotentSubgroup)
             (doubleCoset unipotentSubgroup c unipotentSubgroup) :=
  disjoint_doubleCoset_one_of_not_mem unipotentSubgroup c c_not_mem_unipotentSubgroup

end InfoGeometry.Algebra.Zorn.G2MatrixWeylPair_0_1
