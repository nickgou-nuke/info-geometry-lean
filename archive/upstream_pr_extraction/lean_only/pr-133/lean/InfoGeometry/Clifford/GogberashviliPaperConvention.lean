import InfoGeometry.Clifford.GogberashviliSplitOctonionBasis

/-!
# Equation (6) in the 2024 split-octonionic Dirac paper

The 2024 paper uses the opposite sign for the symbols called `jₙ` from the
older Gogberashvili--Sakhelashvili owner already present in this repository.
The definitions below are therefore a genuine convention translation:
`paperJ n = J n`, `paperj n = -j n`, and `paperI = I`.
-/

namespace InfoGeometry.Clifford.GogberashviliPaperConvention

open InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

def paperJ (n : Fin 3) : ZornCell ℝ := J n
def paperj (n : Fin 3) : ZornCell ℝ := negZ (j n)
def paperI : ZornCell ℝ := I

theorem paperJ_mul_paperJ (m n : Fin 3) :
    paperJ m * paperJ n =
      (if m = n then (1 : ℝ) else 0) • oneZ +
        sumFin3 (fun k => (eps3 m n k : ℝ) • paperj k) := by
  fin_cases m <;> fin_cases n
  all_goals
    change mulZ (J _) (J _) = _
    unfold paperj J j eps3 sumFin3
    apply zorn_ext <;>
      dsimp only [zero_val, addZ_val, smulZ_val,
        InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.smulZ,
        InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.addZ, zeroZ, oneZ,
        ZornCell.mulZ, negZ] <;> norm_num

set_option maxHeartbeats 800000 in
theorem paperj_mul_paperj (m n : Fin 3) :
    paperj m * paperj n =
      -(if m = n then (1 : ℝ) else 0) • oneZ +
        sumFin3 (fun k => (eps3 m n k : ℝ) • paperj k) := by
  fin_cases m <;> fin_cases n
  all_goals
    change mulZ (negZ (j _)) (negZ (j _)) = _
    unfold paperj eps3 sumFin3 j
    apply zorn_ext <;>
      dsimp only [zero_val, addZ_val, smulZ_val,
        InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.smulZ,
        InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.addZ, zeroZ, oneZ,
        ZornCell.mulZ, negZ] <;> norm_num

theorem paperj_mul_paperI (n : Fin 3) :
    paperj n * paperI = paperJ n := by
  fin_cases n
  all_goals
    change mulZ (negZ (j _)) I = J _
    unfold j I J
    apply zorn_ext <;> dsimp only [ZornCell.mulZ, negZ] <;> norm_num

theorem paperJ_mul_paperI (n : Fin 3) :
    paperJ n * paperI = paperj n := by
  fin_cases n
  all_goals
    change mulZ (J _) I = negZ (j _)
    unfold j I J
    apply zorn_ext <;> dsimp only [ZornCell.mulZ, negZ] <;> norm_num

theorem paper_equation_six :
    (∀ m n : Fin 3,
      paperJ m * paperJ n =
        (if m = n then (1 : ℝ) else 0) • oneZ +
          sumFin3 (fun k => (eps3 m n k : ℝ) • paperj k)) ∧
    (∀ m n : Fin 3,
      paperj m * paperj n =
        -(if m = n then (1 : ℝ) else 0) • oneZ +
          sumFin3 (fun k => (eps3 m n k : ℝ) • paperj k)) ∧
    (∀ n : Fin 3, paperj n * paperI = paperJ n) := by
  exact ⟨paperJ_mul_paperJ, paperj_mul_paperj, paperj_mul_paperI⟩

end InfoGeometry.Clifford.GogberashviliPaperConvention
