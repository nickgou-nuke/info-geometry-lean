import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import InfoGeometry.Clifford.SplitQ44
import InfoGeometry.Clifford.Cl44Witt
import InfoGeometry.Canonical.TopologicalKMSFlow

/-!
# Tomita-Takesaki Involutions

This file constructs the $\mathbb{Z}_2^3$ physical involutions ($\Gamma_R, \Gamma_\chi, \Gamma_N$) 
and proves the fundamental Tomita-Takesaki modular conjugation identity natively
for the 55-dimensional split representation.
-/

namespace InfoGeometry.Canonical.TomitaTakesakiInvolutions

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Canonical.TopologicalKMSFlow
open CliffordAlgebra

def GammaNFun (x : Fin 8 → ℝ) : Fin 8 → ℝ
  | 0 => x 0
  | 1 => x 1
  | 2 => x 2
  | 3 => x 3
  | 4 => -x 4
  | 5 => -x 5
  | 6 => -x 6
  | 7 => -x 7

lemma GammaNFun_add (x y : Fin 8 → ℝ) : GammaNFun (x + y) = GammaNFun x + GammaNFun y := by
  ext j; fin_cases j <;> simp [GammaNFun, Pi.add_apply] <;> ring

lemma GammaNFun_smul (c : ℝ) (x : Fin 8 → ℝ) : GammaNFun (c • x) = c • GammaNFun x := by
  ext j; fin_cases j <;> simp [GammaNFun, Pi.smul_apply]

theorem GammaNFun_preserves_Q (x : Fin 8 → ℝ) : splitQ44 (GammaNFun x) = splitQ44 x := by
  simp [splitQ44_apply, GammaNFun]

noncomputable def GammaNIsometry : QuadraticMap.IsometryEquiv splitQ44 splitQ44 where
  toFun := GammaNFun
  invFun := GammaNFun
  map_add' := GammaNFun_add
  map_smul' := GammaNFun_smul
  left_inv x := by ext j; fin_cases j <;> simp [GammaNFun]
  right_inv x := by ext j; fin_cases j <;> simp [GammaNFun]
  map_app' x := GammaNFun_preserves_Q x

/-- Charge Conjugation (Gamma_N) as an algebra automorphism. -/
noncomputable def GammaN : Cl44 ≃ₐ[ℝ] Cl44 :=
  CliffordAlgebra.equivOfIsometry GammaNIsometry

def GammaChiFun (x : Fin 8 → ℝ) : Fin 8 → ℝ
  | 0 => x 1
  | 1 => x 0
  | 2 => x 3
  | 3 => x 2
  | 4 => x 5
  | 5 => x 4
  | 6 => x 7
  | 7 => x 6

lemma GammaChiFun_add (x y : Fin 8 → ℝ) : GammaChiFun (x + y) = GammaChiFun x + GammaChiFun y := by
  ext j; fin_cases j <;> simp [GammaChiFun, Pi.add_apply]

lemma GammaChiFun_smul (c : ℝ) (x : Fin 8 → ℝ) : GammaChiFun (c • x) = c • GammaChiFun x := by
  ext j; fin_cases j <;> simp [GammaChiFun, Pi.smul_apply]

theorem GammaChiFun_preserves_Q (x : Fin 8 → ℝ) : splitQ44 (GammaChiFun x) = splitQ44 x := by
  simp [splitQ44_apply, GammaChiFun]
  ring

noncomputable def GammaChiIsometry : QuadraticMap.IsometryEquiv splitQ44 splitQ44 where
  toFun := GammaChiFun
  invFun := GammaChiFun
  map_add' := GammaChiFun_add
  map_smul' := GammaChiFun_smul
  left_inv x := by ext j; fin_cases j <;> simp [GammaChiFun]
  right_inv x := by ext j; fin_cases j <;> simp [GammaChiFun]
  map_app' x := GammaChiFun_preserves_Q x

/-- Chiral Conjugation (Gamma_chi) as an algebra automorphism. -/
noncomputable def GammaChi : Cl44 ≃ₐ[ℝ] Cl44 :=
  CliffordAlgebra.equivOfIsometry GammaChiIsometry

/-- Time Reversal (Gamma_R) as the canonical anti-automorphism. -/
noncomputable def GammaR : Cl44 →ₗ[ℝ] Cl44 :=
  reverse

/-- The Tomita-Takesaki Modular Conjugation J.
It is an anti-linear operator (represented over R as an anti-automorphism)
composed of Time Reversal and Charge Conjugation. -/
noncomputable def J_Tomita : Cl44 →ₗ[ℝ] Cl44 :=
  GammaR.comp GammaN.toLinearMap

variable (E μ : Fin 4 → ℝ)

/-- J on the generators behaves exactly to reverse the modular flow. -/
theorem J_Tomita_reverses_flow (t : ℝ) (x : Fin 8 → ℝ) :
    J_Tomita (modularFlow E μ t (J_Tomita (ι splitQ44 x))) =
    modularFlow E μ (-t) (ι splitQ44 x) := by
  -- Since ι x is a vector, GammaN maps it to ι (GammaNFun x), and reverse preserves it.
  have h1 : ∀ v, J_Tomita (ι splitQ44 v) = ι splitQ44 (GammaNFun v) := by
    intro v
    change reverse (GammaN (ι splitQ44 v)) = ι splitQ44 (GammaNFun v)
    have hh : GammaN (ι splitQ44 v) = ι splitQ44 (GammaNFun v) := by
      change CliffordAlgebra.map GammaNIsometry.toIsometry (ι splitQ44 v) = ι splitQ44 (GammaNFun v)
      rw [CliffordAlgebra.map_apply_ι]
      rfl
    rw [hh]
    exact reverse_ι _
  rw [h1 x]
  -- Now modularFlow maps this to ι (boostFun t (GammaNFun x))
  have h2 : modularFlow E μ t (ι splitQ44 (GammaNFun x)) = ι splitQ44 (boostFun E μ t (GammaNFun x)) := by
    change CliffordAlgebra.map (boostIsometryEquiv E μ t).toIsometry (ι splitQ44 (GammaNFun x)) = _
    rw [CliffordAlgebra.map_apply_ι]
    rfl
  rw [h2]
  -- And J_Tomita on this is ι (GammaNFun (boostFun t (GammaNFun x)))
  rw [h1]
  have h3 : modularFlow E μ (-t) (ι splitQ44 x) = ι splitQ44 (boostFun E μ (-t) x) := by
    change CliffordAlgebra.map (boostIsometryEquiv E μ (-t)).toIsometry (ι splitQ44 x) = _
    rw [CliffordAlgebra.map_apply_ι]
    rfl
  rw [h3]
  -- So we just need to show that GammaNFun ∘ boostFun t ∘ GammaNFun = boostFun (-t)
  congr 1
  ext j
  fin_cases j <;> simp [GammaNFun, boostFun, Real.cosh_neg, Real.sinh_neg] <;> ring

end InfoGeometry.Canonical.TomitaTakesakiInvolutions
