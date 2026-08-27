import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment

namespace InfoGeometry.Algebra.Zorn.G2MatrixWeylPair_0_1

open Matrix
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def cMatrix : Matrix (Fin 8) (Fin 8) F2 :=
  cycle012Matrix * swapCartanMatrix

def sMatrix : Matrix (Fin 8) (Fin 8) F2 := swap01Matrix

abbrev LocalWeylG2 := ZMod 6 × Bool

def weylMatrix (p : LocalWeylG2) : Matrix (Fin 8) (Fin 8) F2 :=
  if p.2 then cMatrix ^ p.1.val * sMatrix else cMatrix ^ p.1.val

theorem autMatrix_weylNF_zero_false_readback :
    autMatrix (weylNF 0 false) = weylMatrix ((0, false) : LocalWeylG2) := by
  rw [weylNF_zero_false, autMatrix_one]
  simp [weylMatrix]

theorem autMatrix_weylNF_one_false_readback :
    autMatrix (weylNF 1 false) = weylMatrix ((1, false) : LocalWeylG2) := by
  have h1 : (1 : ZMod 6).val = 1 := rfl
  have hweyl : weylNF 1 false = c := by
    change (if false then s * c ^ (1 : ZMod 6).val else c ^ (1 : ZMod 6).val) = c
    rw [h1, pow_one]
    rfl
  rw [hweyl]
  have haut : autMatrix c = cMatrix := InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment.autMatrix_c
  have hmat : weylMatrix ((1, false) : LocalWeylG2) = cMatrix := by
    change (if false then cMatrix ^ (1 : ZMod 6).val * sMatrix else cMatrix ^ (1 : ZMod 6).val) = cMatrix
    rw [h1, pow_one]
    rfl
  rw [haut, hmat]

theorem matrix_weyl_entry_separation_0_1 (e d : PCExponent) :
    ∃ i j : Fin 8,
      (matrixWord d * weylMatrix ((0, false) : LocalWeylG2) * matrixWord e) i j ≠
        weylMatrix ((1, false) : LocalWeylG2) i j := by
  fin_cases e <;> fin_cases d <;> decide

theorem autMatrix_weyl_entry_separation_0_1 (e d : PCExponent) :
    ∃ i j : Fin 8,
      (autMatrix (G2TwoSylowSubgroup.pcWord d) *
        autMatrix (weylNF 0 false) *
          autMatrix (G2TwoSylowSubgroup.pcWord e)) i j ≠
        autMatrix (weylNF 1 false) i j := by
  obtain ⟨i, j, h⟩ := matrix_weyl_entry_separation_0_1 e d
  refine ⟨i, j, ?_⟩
  rw [autMatrix_pcWord, autMatrix_weylNF_zero_false_readback,
    autMatrix_pcWord, autMatrix_weylNF_one_false_readback]
  exact h

theorem autMatrix_normalized_weyl_separation_0_1
    (a d : PCExponent) :
    autMatrix (weylNF 1 false) ≠
      autMatrix (G2TwoSylowSubgroup.pcWord a *
        weylNF 0 false * G2TwoSylowSubgroup.pcWord d) := by
  intro h
  rw [autMatrix_mul, autMatrix_mul] at h
  rw [autMatrix_pcWord, autMatrix_weylNF_zero_false_readback,
    autMatrix_pcWord, autMatrix_weylNF_one_false_readback] at h
  exact (autMatrix_weyl_entry_separation_0_1 a d) h.symm

end InfoGeometry.Algebra.Zorn.G2MatrixWeylPair_0_1
