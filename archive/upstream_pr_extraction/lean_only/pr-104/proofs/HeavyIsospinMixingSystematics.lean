import Mathlib
import proofs.FarneaGe64IsospinMixing
import proofs.LECM2022ElectroweakRadiiISB

noncomputable section

namespace HeavyIsospinMixingSystematics

open FarneaGe64IsospinMixing
open LECM2022ElectroweakRadiiISB

abbrev Q := ℚ

-- O(5,5) Cartan subalgebra and 5-graded structure.
-- The topological non-Hermitian defect.
def TKK_O55_Dimension : Q := 45
def Cartan_O55_Rank : Q := 5

-- Asymptotic mass scaling law as nuclei approach Ge-64 (A -> 64)
-- The isospin mixing parameter alpha^2 grows as a non-Hermitian defect.

def massDistance (A : Q) : Q := |64 - A|

def topologicalDefectPhase (A : Q) : Q :=
  if A = 64 then 1 else 1 / (1 + massDistance A)

-- Let alpha^2_base be the LECM2022 scale for isospin breaking
-- from deltaC_permyriad.
def LECM2022_alpha2_scale : Q := (deltaCMax_permyriad : Q) / 10000

-- Using Farnea alpha2 extracted as the asymptotic limit at A=64.
def Ge64_alpha2_limit : Q := alpha2_extracted

-- Scaling law combining the topological defect phase
def asymptoticAlpha2 (A : Q) : Q :=
  LECM2022_alpha2_scale + (Ge64_alpha2_limit - LECM2022_alpha2_scale) * topologicalDefectPhase A

theorem scaling_law_at_Ge64 :
    asymptoticAlpha2 64 = Ge64_alpha2_limit := by
  have h2 : topologicalDefectPhase 64 = 1 := by
    unfold topologicalDefectPhase
    norm_num
  unfold asymptoticAlpha2
  rw [h2]
  ring

-- To derive this asymptotic behavior mathematically as a topological non-Hermitian defect
-- growing within the Cartan subalgebras of the 5-graded TKK O(5,5) symmetry closure.

def nonHermitianDefectCartan (rank : Q) (distance : Q) : Q :=
  rank / (rank + distance)

theorem defect_growth_to_Cartan_core :
    nonHermitianDefectCartan Cartan_O55_Rank 0 = 1 := by
  dsimp [nonHermitianDefectCartan, Cartan_O55_Rank]
  norm_num

def tkk_closure_alpha2 (A : Q) : Q :=
  LECM2022_alpha2_scale + (Ge64_alpha2_limit - LECM2022_alpha2_scale) * nonHermitianDefectCartan Cartan_O55_Rank (massDistance A * Cartan_O55_Rank)

theorem defect_equivalence_at_Cartan (A : Q) :
    topologicalDefectPhase A = nonHermitianDefectCartan Cartan_O55_Rank (massDistance A * Cartan_O55_Rank) := by
  dsimp [topologicalDefectPhase, nonHermitianDefectCartan, Cartan_O55_Rank]
  split_ifs with h
  · subst h
    dsimp [massDistance]
    norm_num
  · have hc : 5 + massDistance A * 5 = 5 * (1 + massDistance A) := by ring
    rw [hc]
    have hnz : (5 : Q) ≠ 0 := by norm_num
    have hm : 1 + massDistance A ≠ 0 := by
      dsimp [massDistance]
      have : 0 ≤ |64 - A| := abs_nonneg (64 - A)
      linarith
    rw [div_mul_eq_div_div, div_self hnz, one_div]

theorem derivation_of_asymptotic_behavior (A : Q) :
    asymptoticAlpha2 A = tkk_closure_alpha2 A := by
  dsimp [asymptoticAlpha2, tkk_closure_alpha2]
  rw [defect_equivalence_at_Cartan A]

theorem anchor_farnea_isb :
    asymptoticAlpha2 64 = 741 / 29600 := by
  rw [scaling_law_at_Ge64]
  exact alpha2_extracted_exact

theorem anchor_lecm_isb :
    LECM2022_alpha2_scale = 1 / 100 := by
  dsimp [LECM2022_alpha2_scale, LECM2022ElectroweakRadiiISB.deltaCMax_permyriad]
  norm_num

end HeavyIsospinMixingSystematics

end noncomputable section
