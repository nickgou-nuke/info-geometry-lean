import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace InfoGeometry.Geometry

inductive MobiusClass where
  | elliptic
  | parabolic
  | hyperbolic
  | loxodromic
  deriving DecidableEq, Repr

abbrev SigmaPair := ℚ × ℚ

def classifySigma (s : SigmaPair) : MobiusClass :=
  if s.2 = 0 then
    if s.1 = 4 then MobiusClass.parabolic
    else if s.1 < 4 then MobiusClass.elliptic
    else MobiusClass.hyperbolic
  else
    MobiusClass.loxodromic

def hyperSigma : SigmaPair := (25 / 4, 0)
def paraSigma : SigmaPair := (4, 0)
def ellSigma : SigmaPair := (0, 0)
def loxSigma : SigmaPair := (3, 4)

def gaussianSquare (a b : ℚ) : SigmaPair := (a * a - b * b, 2 * a * b)

theorem hyper_sigma_readback : hyperSigma = (((5 : ℚ) / 2) * ((5 : ℚ) / 2), 0) := by
  norm_num [hyperSigma]

theorem para_sigma_readback : paraSigma = (((2 : ℚ) * 2), 0) := by
  norm_num [paraSigma]

theorem ell_sigma_readback : ellSigma = (0, 0) := by
  norm_num [ellSigma]

theorem lox_sigma_readback : gaussianSquare 2 1 = loxSigma := by
  norm_num [gaussianSquare, loxSigma]

theorem hyper_classification : classifySigma hyperSigma = MobiusClass.hyperbolic := by
  norm_num [classifySigma, hyperSigma, MobiusClass.hyperbolic]

theorem para_classification : classifySigma paraSigma = MobiusClass.parabolic := by
  norm_num [classifySigma, paraSigma, MobiusClass.parabolic]

theorem ell_classification : classifySigma ellSigma = MobiusClass.elliptic := by
  norm_num [classifySigma, ellSigma, MobiusClass.elliptic]

theorem lox_classification : classifySigma loxSigma = MobiusClass.loxodromic := by
  norm_num [classifySigma, loxSigma, MobiusClass.loxodromic]

/-- The Gaussian-square readback lands in the loxodromic class. -/
theorem gaussianSquare_two_one_classification :
    classifySigma (gaussianSquare 2 1) = MobiusClass.loxodromic := by
  rw [lox_sigma_readback]
  exact lox_classification

/-- Any real trace-squared parameter above `4` is classified as hyperbolic. -/
theorem classifySigma_hyperbolic_of_gt_four {s : SigmaPair}
    (hs2 : s.2 = 0) (hs1 : 4 < s.1) :
    classifySigma s = MobiusClass.hyperbolic := by
  have hne : s.1 ≠ 4 := by linarith
  have hlt : ¬ s.1 < 4 := by linarith
  simp [classifySigma, hs2, hne, hlt]

/-- Any nonzero secondary coordinate is classified as loxodromic. -/
theorem classifySigma_loxodromic_of_second_ne_zero {s : SigmaPair}
    (hs2 : s.2 ≠ 0) :
    classifySigma s = MobiusClass.loxodromic := by
  simp [classifySigma, hs2]

/-- A zero-secondary parameter with trace-squared below `4` is elliptic. -/
theorem classifySigma_elliptic_of_lt_four {s : SigmaPair}
    (hs2 : s.2 = 0) (hs1 : s.1 < 4) :
    classifySigma s = MobiusClass.elliptic := by
  have hne : s.1 ≠ 4 := by linarith
  simp [classifySigma, hs2, hs1, hne]

/-- The parabolic class constructor is distinct from the elliptic constructor. -/
theorem MobiusClass.parabolic_ne_elliptic :
    MobiusClass.parabolic ≠ MobiusClass.elliptic := by
  decide

/-- The elliptic class constructor is distinct from the parabolic constructor. -/
theorem MobiusClass.elliptic_ne_parabolic :
    MobiusClass.elliptic ≠ MobiusClass.parabolic := by
  decide

/-- A real trace-squared parameter exactly equal to `4` is classified as parabolic. -/
theorem classifySigma_parabolic_of_eq_four {s : SigmaPair}
    (hs2 : s.2 = 0) (hs1 : s.1 = 4) :
    classifySigma s = MobiusClass.parabolic := by
  simp [classifySigma, hs2, hs1]

/-- The parabolic boundary value `4` cannot satisfy the elliptic strict bound `< 4`. -/
theorem not_lt_four_of_eq_four {r : ℚ} (hr : r = 4) :
    ¬ r < 4 := by
  intro hlt
  linarith

/-- A real trace-squared parameter exactly equal to `4` is not classified as elliptic. -/
theorem classifySigma_not_elliptic_of_parabolic_sigma {s : SigmaPair}
    (hs2 : s.2 = 0) (hs1 : s.1 = 4) :
    classifySigma s ≠ MobiusClass.elliptic := by
  rw [classifySigma_parabolic_of_eq_four hs2 hs1]
  exact MobiusClass.parabolic_ne_elliptic

/-- The distinguished parabolic sample is not classified as elliptic. -/
theorem para_not_elliptic :
    classifySigma paraSigma ≠ MobiusClass.elliptic := by
  rw [para_classification]
  exact MobiusClass.parabolic_ne_elliptic

/-- A parabolic classifier readback excludes an elliptic classifier readback. -/
theorem classifySigma_not_elliptic_of_eq_parabolic {s : SigmaPair}
    (hp : classifySigma s = MobiusClass.parabolic) :
    classifySigma s ≠ MobiusClass.elliptic := by
  intro he
  rw [he] at hp
  exact MobiusClass.elliptic_ne_parabolic hp

end InfoGeometry.Geometry
