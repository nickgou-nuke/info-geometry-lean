import InfoGeometry.Geometry.RealDoubleWittNPReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Geometry.RealDoubleWittNP

noncomputable section

def wittBoost (t : ℝ) : Plane →ₗ[ℝ] Plane :=
  { toFun := fun x =>
      ![
        Real.exp t * ((x 0 + x 1) / 2) + Real.exp (-t) * ((x 0 - x 1) / 2),
        Real.exp t * ((x 0 + x 1) / 2) - Real.exp (-t) * ((x 0 - x 1) / 2)]
    map_add' := by
      intro x y
      funext i
      fin_cases i <;> simp <;> ring
    map_smul' := by
      intro a x
      funext i
      fin_cases i <;> simp <;> ring }

theorem wittBoost_cPlus (t : ℝ) :
    wittBoost t cPlus = Real.exp t • cPlus := by
  funext i
  fin_cases i <;> simp [wittBoost, cPlus]

theorem wittBoost_cMinus (t : ℝ) :
    wittBoost t cMinus = Real.exp (-t) • cMinus := by
  funext i
  fin_cases i <;> simp [wittBoost, cMinus]

theorem wittBoost_ePlus (t : ℝ) :
    wittBoost t ePlus = Real.exp t • ePlus := by
  exact wittBoost_cPlus t

theorem wittBoost_eMinus (t : ℝ) :
    wittBoost t eMinus = Real.exp (-t) • eMinus := by
  exact wittBoost_cMinus t

theorem wittBoost_preserves_plane_form (t : ℝ) (x y : Plane) :
    -(wittBoost t x 0) * (wittBoost t y 0) +
        (wittBoost t x 1) * (wittBoost t y 1) =
      -(x 0) * (y 0) + (x 1) * (y 1) := by
  simp [wittBoost]
  have h : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  linear_combination h * (-(x 0) * (y 0) + (x 1) * (y 1))

def entropyFlow (t : ℝ) : Carrier →ₗ[ℝ] Carrier :=
  { toFun := fun x => (x.1, wittBoost t x.2)
    map_add' := by
      intro x y
      change (x.1 + y.1, wittBoost t (x.2 + y.2)) =
        (x.1, wittBoost t x.2) + (y.1, wittBoost t y.2)
      rw [(wittBoost t).map_add]
      rfl
    map_smul' := by
      intro a x
      change (a • x.1, wittBoost t (a • x.2)) =
        (a • x.1, a • wittBoost t x.2)
      rw [(wittBoost t).map_smul] }

@[simp] theorem entropyFlow_apply (t : ℝ) (x : Carrier) :
    entropyFlow t x = (x.1, wittBoost t x.2) := rfl

theorem entropyFlow_cPlus (t : ℝ) :
    entropyFlow t cPlusLift = cPlusLift := by
  simp [entropyFlow, cPlusLift]

theorem entropyFlow_cMinus (t : ℝ) :
    entropyFlow t cMinusLift = cMinusLift := by
  simp [entropyFlow, cMinusLift]

theorem entropyFlow_ePlus (t : ℝ) :
    entropyFlow t ePlusLift =
      (Real.exp t) • ePlusLift := by
  simp [entropyFlow, ePlusLift, wittBoost_ePlus]

theorem entropyFlow_eMinus (t : ℝ) :
    entropyFlow t eMinusLift =
      (Real.exp (-t)) • eMinusLift := by
  simp [entropyFlow, eMinusLift, wittBoost_eMinus]

theorem entropyFlow_preserves_causalForm (t : ℝ) (x y : Carrier) :
    causalForm (entropyFlow t x) (entropyFlow t y) = causalForm x y := by
  rcases x with ⟨xc, xe⟩
  rcases y with ⟨yc, ye⟩
  change causalForm (xc, wittBoost t xe) (yc, wittBoost t ye) =
    causalForm (xc, xe) (yc, ye)
  simp only [causalForm]
  have hE := wittBoost_preserves_plane_form t xe ye
  linarith

end

end InfoGeometry.Geometry.RealDoubleWittNP
