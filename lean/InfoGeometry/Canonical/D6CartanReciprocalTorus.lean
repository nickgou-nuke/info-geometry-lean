import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Rank-two Cartan coordinates for the positive reciprocal torus

The determinant-one constraint for the three diagonal reciprocal weights is
written in independent coordinates `(t₁,t₂)`, with `t₃ = -t₁-t₂`.  This is a
coordinate bridge only; no measure-theoretic transform or continuum Bloch
theorem is asserted here.
-/

namespace InfoGeometry.Canonical.D6CartanReciprocalTorus

noncomputable section

abbrev CartanPair := ℝ × ℝ
abbrev TorusTriple := ℝ × ℝ × ℝ

def cartanTorus (t : CartanPair) : TorusTriple :=
  (Real.exp (2 * t.1), Real.exp (2 * t.2), Real.exp (-2 * (t.1 + t.2)))

def torusProduct (z : TorusTriple) : ℝ := z.1 * z.2.1 * z.2.2

def positiveDetOne (z : TorusTriple) : Prop :=
  0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2 ∧ torusProduct z = 1

def cartanTorusComponent (i : Fin 3) (t : CartanPair) : ℝ :=
  match i with
  | 0 => (cartanTorus t).1
  | 1 => (cartanTorus t).2.1
  | 2 => (cartanTorus t).2.2

theorem cartanTorus_pos (t : CartanPair) :
    0 < (cartanTorus t).1 ∧ 0 < (cartanTorus t).2.1 ∧ 0 < (cartanTorus t).2.2 := by
  simp [cartanTorus, Real.exp_pos]

theorem cartanTorus_product (t : CartanPair) :
    (cartanTorus t).1 * (cartanTorus t).2.1 * (cartanTorus t).2.2 = 1 := by
  simp only [cartanTorus]
  rw [← Real.exp_add, ← Real.exp_add]
  ring_nf
  simp

theorem cartanTorus_log (t : CartanPair) (i : Fin 3) :
    Real.log (cartanTorusComponent i t) =
      match i with
      | 0 => 2 * t.1
      | 1 => 2 * t.2
      | 2 => -2 * (t.1 + t.2) := by
  fin_cases i <;> simp [cartanTorusComponent, cartanTorus, Real.log_exp]

theorem cartanTorus_third_coordinate (t : CartanPair) :
    (cartanTorus t).2.2 =
      (cartanTorus t).1⁻¹ * (cartanTorus t).2.1⁻¹ := by
  have h := cartanTorus_product t
  have h₁ : (cartanTorus t).1 ≠ 0 := ne_of_gt (cartanTorus_pos t).1
  have h₂ : (cartanTorus t).2.1 ≠ 0 := ne_of_gt (cartanTorus_pos t).2.1
  field_simp [h₁, h₂]
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

theorem cartanTorus_injective : Function.Injective cartanTorus := by
  intro t u h
  have h₁ : Real.exp (2 * t.1) = Real.exp (2 * u.1) :=
    congrArg Prod.fst h
  have h₂ : Real.exp (2 * t.2) = Real.exp (2 * u.2) :=
    congrArg (fun z : TorusTriple => z.2.1) h
  have ht₁ : t.1 = u.1 := by
    have h' := Real.exp_injective h₁
    linarith
  have ht₂ : t.2 = u.2 := by
    have h' := Real.exp_injective h₂
    linarith
  exact Prod.ext ht₁ ht₂

theorem cartanTorus_surjective_positiveDetOne
    (z : TorusTriple) (hz : positiveDetOne z) :
    ∃ t : CartanPair, cartanTorus t = z := by
  let t : CartanPair := (Real.log z.1 / 2, Real.log z.2.1 / 2)
  have hz₁ : 0 < z.1 := hz.1
  have hz₂ : 0 < z.2.1 := hz.2.1
  have hz₃ : 0 < z.2.2 := hz.2.2.1
  have hprod : z.1 * z.2.1 * z.2.2 = 1 := hz.2.2.2
  have hthird : Real.exp (-2 * (t.1 + t.2)) = z.2.2 := by
    dsimp [t]
    have harg : -2 * (Real.log z.1 / 2 + Real.log z.2.1 / 2) =
        -(Real.log z.1 + Real.log z.2.1) := by ring
    rw [harg, Real.exp_neg, Real.exp_add, Real.exp_log hz₁, Real.exp_log hz₂]
    field_simp [ne_of_gt hz₁, ne_of_gt hz₂, ne_of_gt hz₃]
    simpa [torusProduct] using hprod.symm
  refine ⟨t, ?_⟩
  apply Prod.ext
  · have harg : 2 * (Real.log z.1 / 2) = Real.log z.1 := by ring
    simp [cartanTorus, t, harg, Real.exp_log hz₁]
  · apply Prod.ext
    · have harg : 2 * (Real.log z.2.1 / 2) = Real.log z.2.1 := by ring
      simp [cartanTorus, t, harg, Real.exp_log hz₂]
    · exact hthird

end
end InfoGeometry.Canonical.D6CartanReciprocalTorus
