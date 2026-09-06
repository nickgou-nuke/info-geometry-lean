import InfoGeometry.Clifford.FanoOctonionParavector

/-!
# A native quaternionic slice of the Fano paravector carrier

The full Fano paravector carrier is octonionic and therefore not associative.
This owner records only the three-generator slice used by the Hestenes
quaternionic dictionary.  The product is the existing native paravector
product; no associative algebra structure is added to the octonion carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesQuaternionCore

open InfoGeometry.Clifford.FanoOctonionParavector
open InfoGeometry.Clifford.OctonionParavectorBridge

def q1 : OctonionCarrier := imaginary e0
def q2 : OctonionCarrier := imaginary e1
def q3 : OctonionCarrier := imaginary e2

@[simp] theorem q1_sq : paravectorMul fanoOctonionParavectorData q1 q1 = scalar (-1 : ℝ) := by
  simpa [q1] using imaginary_e0_sq

@[simp] theorem q1_mul_q2 : paravectorMul fanoOctonionParavectorData q1 q2 = q3 := by
  simpa [q1, q2, q3] using imaginary_e0_mul_e1

@[simp] theorem q2_mul_q1 : paravectorMul fanoOctonionParavectorData q2 q1 = -q3 := by
  apply Prod.ext
  · norm_num [q1, q2, q3, paravectorMul, imaginary,
      fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
      e0, e1, e2, Fin.sum_univ_seven]
  · funext k
    fin_cases k <;>
      norm_num [q1, q2, q3, paravectorMul, imaginary,
        fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
        e0, e1, e2]

@[simp] theorem q2_sq : paravectorMul fanoOctonionParavectorData q2 q2 = scalar (-1 : ℝ) := by
  apply Prod.ext
  · norm_num [q2, paravectorMul, imaginary, scalar,
      fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
      e1, Fin.sum_univ_seven]
  · ext k
    fin_cases k <;>
      norm_num [q2, paravectorMul, imaginary, scalar,
        fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw, e1]

@[simp] theorem q3_sq : paravectorMul fanoOctonionParavectorData q3 q3 = scalar (-1 : ℝ) := by
  apply Prod.ext
  · norm_num [q3, paravectorMul, imaginary, scalar,
      fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
      e2, Fin.sum_univ_seven]
  · ext k
    fin_cases k <;>
      norm_num [q3, paravectorMul, imaginary, scalar,
        fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw, e2]

@[simp] theorem q2_mul_q3 : paravectorMul fanoOctonionParavectorData q2 q3 = q1 := by
  apply Prod.ext
  · norm_num [q1, q2, q3, paravectorMul, imaginary,
      fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
      e0, e1, e2, Fin.sum_univ_seven]
  · ext k
    fin_cases k <;>
      norm_num [q1, q2, q3, paravectorMul, imaginary,
        fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
        e0, e1, e2]

@[simp] theorem q3_mul_q2 : paravectorMul fanoOctonionParavectorData q3 q2 = -q1 := by
  apply Prod.ext
  · norm_num [q1, q2, q3, paravectorMul, imaginary,
      fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
      e0, e1, e2, Fin.sum_univ_seven]
  · ext k
    fin_cases k <;>
      norm_num [q1, q2, q3, paravectorMul, imaginary,
        fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
        e0, e1, e2]

@[simp] theorem q3_mul_q1 : paravectorMul fanoOctonionParavectorData q3 q1 = q2 := by
  apply Prod.ext
  · norm_num [q1, q2, q3, paravectorMul, imaginary,
      fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
      e0, e1, e2, Fin.sum_univ_seven]
  · ext k
    fin_cases k <;>
      norm_num [q1, q2, q3, paravectorMul, imaginary,
        fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
        e0, e1, e2]

@[simp] theorem q1_mul_q3 : paravectorMul fanoOctonionParavectorData q1 q3 = -q2 := by
  apply Prod.ext
  · norm_num [q1, q2, q3, paravectorMul, imaginary,
      fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
      e0, e1, e2, Fin.sum_univ_seven]
  · funext k
    fin_cases k <;>
      norm_num [q1, q2, q3, paravectorMul, imaginary,
        fanoOctonionParavectorData, dot7, fanoCross, fanoCrossRaw,
        e0, e1, e2]

end InfoGeometry.Canonical.HestenesQuaternionCore
