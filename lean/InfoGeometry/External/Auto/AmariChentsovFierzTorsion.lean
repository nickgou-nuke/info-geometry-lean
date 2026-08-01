import Mathlib.Tactic

/-!
# Amari--Chentsov cubic coefficient and 2x2 skew matrix

This file proves finite algebraic identities for a one-dimensional cubic jet
and the associated 2x2 real skew-symmetric matrix.

The symbols keep the domain vocabulary used by downstream imports, but the
checked content is only polynomial splitting, coefficient projection, a
left-right cubic difference, and elementary matrix trace/transpose facts.
-/

noncomputable section

namespace AmariChentsovFierzTorsion

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- A finite two-coefficient jet through cubic order.
`dikinMetric` is the quadratic coefficient and `amariCubic` is the cubic
Amari--Chentsov/skewness coefficient. -/
abbrev ModularBregmanJet := ℝ × ℝ

namespace ModularBregmanJet

abbrev dikinMetric (J : ModularBregmanJet) : ℝ := J.1

abbrev amariCubic (J : ModularBregmanJet) : ℝ := J.2

end ModularBregmanJet

/-- Cubic polynomial through third order:
`ψ(ε)=g ε²/2 + C ε³/6`. -/
def potential (J : ModularBregmanJet) (ε : ℝ) : ℝ :=
  (J.dikinMetric / 2) * ε ^ 2 + (J.amariCubic / 6) * ε ^ 3

/-- The quadratic term of the finite jet. -/
def dikinQuadratic (J : ModularBregmanJet) (ε : ℝ) : ℝ :=
  (J.dikinMetric / 2) * ε ^ 2

/-- The cubic term of the finite jet. -/
def poissonCubicTail (J : ModularBregmanJet) (ε : ℝ) : ℝ :=
  (J.amariCubic / 6) * ε ^ 3

/-- Exact split of the cubic polynomial into its quadratic and cubic terms. -/
theorem potential_eq_dikin_plus_tail (J : ModularBregmanJet) (ε : ℝ) :
    potential J ε = dikinQuadratic J ε + poissonCubicTail J ε := by
  rfl

/-- The recorded quadratic coefficient. -/
def secondJetAtZero (J : ModularBregmanJet) : ℝ := J.dikinMetric

/-- The recorded cubic coefficient. -/
def thirdJetAtZero (J : ModularBregmanJet) : ℝ := J.amariCubic

/-- The second-jet projection returns the stored quadratic coefficient. -/
theorem secondJet_eq_dikin (J : ModularBregmanJet) :
    secondJetAtZero J = J.dikinMetric := rfl

/-- The third-jet projection returns the stored cubic coefficient. -/
theorem thirdJet_eq_amari (J : ModularBregmanJet) :
    thirdJetAtZero J = J.amariCubic := rfl

/-- A pair of finite cubic jets. -/
abbrev ChiralCubicLift := ModularBregmanJet × ModularBregmanJet

namespace ChiralCubicLift

abbrev left (L : ChiralCubicLift) : ModularBregmanJet := L.1

abbrev right (L : ChiralCubicLift) : ModularBregmanJet := L.2

end ChiralCubicLift

/-- Difference between the right and left cubic coefficients. -/
def cubicTorsion (L : ChiralCubicLift) : ℝ :=
  thirdJetAtZero L.right - thirdJetAtZero L.left

/-- Equivalent expression as the difference of the stored cubic coefficients. -/
theorem cubicTorsion_eq_amari_mismatch (L : ChiralCubicLift) :
    cubicTorsion L = L.right.amariCubic - L.left.amariCubic := rfl

/-- The cubic difference vanishes when the stored cubic coefficients agree. -/
theorem cubicTorsion_eq_zero_of_balanced (L : ChiralCubicLift)
    (h : L.right.amariCubic = L.left.amariCubic) : cubicTorsion L = 0 := by
  simp [cubicTorsion, thirdJetAtZero, h]

/-- The 2x2 skew matrix determined by a scalar parameter. -/
def jonesFierzTorsionMatrix (τ : ℝ) : M2R := !![0, τ; -τ, 0]

/-- The 2x2 skew matrix is traceless. -/
theorem jonesFierz_trace_zero (τ : ℝ) : Matrix.trace (jonesFierzTorsionMatrix τ) = 0 := by
  simp [jonesFierzTorsionMatrix, Matrix.trace_fin_two]

/-- The 2x2 skew matrix is antisymmetric. -/
theorem jonesFierz_transpose (τ : ℝ) :
    (jonesFierzTorsionMatrix τ)ᵀ = - jonesFierzTorsionMatrix τ := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [jonesFierzTorsionMatrix]
  · fin_cases j <;> simp [jonesFierzTorsionMatrix]

/-- Matrix action of the 2x2 skew matrix on a vector. -/
def jonesAct (τ : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => ∑ j : Fin 2, jonesFierzTorsionMatrix τ i j * v j

/-- Explicit action: `(v₀,v₁) ↦ (τ v₁, -τ v₀)`. -/
theorem jonesAct_apply (τ : ℝ) (v : Fin 2 → ℝ) :
    jonesAct τ v = fun i => if i = 0 then τ * v 1 else -τ * v 0 := by
  funext i
  fin_cases i <;> simp [jonesAct, jonesFierzTorsionMatrix, Fin.sum_univ_two]

end AmariChentsovFierzTorsion
