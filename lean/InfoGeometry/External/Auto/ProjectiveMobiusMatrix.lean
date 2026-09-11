import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.KanCayley
import InfoGeometry.External.Auto.ProjectivePenrosePGA

/-!
# Projective Möbius matrix relations

This file packages the matrix-level Möbius action and the basic identities that
classify a `2 × 2` projective map:

* projective rescaling invariance for raw matrix action;
* the determinant formulas for `M - I` and `M + I`;
* the resulting discriminant factorization;
* the scalar Cayley compactification as a projective Möbius special case.

The development is native Lean/mathlib and stays at the level of explicit
finite-dimensional matrix algebra.
-/

noncomputable section

namespace ProjectiveMobiusMatrix

open Matrix
open InfoGeometry.Canonical.Cayley
open scoped Classical

abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ
abbrev SL2ZMod2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

/-- Reduction modulo `2` on the concrete `SL(2)` matrix group over `ℤ`. -/
def reduceMod2 : SL2Z →* SL2ZMod2 :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))

@[simp] theorem reduceMod2_apply (g : SL2Z) :
    (reduceMod2 g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2)) g := rfl

variable {K : Type*} [Field K]

/-- The projective Möbius action of a `2 × 2` matrix on a scalar `z`. -/
def mobiusMatrix (M : Matrix (Fin 2) (Fin 2) K) (z : K) : K :=
  (M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)

/-- The Möbius action is just the coefficient-wise projective formula. -/
theorem mobiusMatrix_apply (M : Matrix (Fin 2) (Fin 2) K) (z : K) :
    mobiusMatrix M z = (M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1) := by
  rfl

/-- The raw projective Möbius action on `Option K`. -/
def mobiusOption (M : Matrix (Fin 2) (Fin 2) K) : Option K → Option K
  | none => none
  | some z =>
      if h : M 1 0 * z + M 1 1 = 0 then none
      else some ((M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1))

@[simp] theorem mobiusOption_none (M : Matrix (Fin 2) (Fin 2) K) :
    mobiusOption M none = none := by
  rfl

@[simp] theorem mobiusOption_some (M : Matrix (Fin 2) (Fin 2) K) (z : K) :
    mobiusOption M (some z) =
      if h : M 1 0 * z + M 1 1 = 0 then none
      else some ((M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)) := by
  rfl

/-- Scalar rescaling by a unit does not change the `Option K` Möbius action at `∞`. -/
theorem mobiusOption_projective_rescale_none {u : Kˣ}
    (M : Matrix (Fin 2) (Fin 2) K) :
    mobiusOption (u • M) none = mobiusOption M none := by
  by_cases h : M 1 0 = 0
  · simp [mobiusOption, h, Matrix.smul_apply]
  · have hu : (u : K) ≠ 0 := Units.ne_zero u
    have hscaled : ¬ ((u : K) * M 1 0 = 0) := by
      intro hs
      rcases mul_eq_zero.mp hs with hu0 | hm0
      · exact hu hu0
      · exact False.elim (h hm0)
    have hconj :
        ¬ ((u : K) * M 1 0 = 0) ∧
          ((u : K) * M 0 0 / ((u : K) * M 1 0)) = M 0 0 / M 1 0 := by
      constructor
      · exact hscaled
      · simpa using (mul_div_mul_left (M 0 0) (M 1 0) hu)
    simpa [mobiusOption, Matrix.smul_apply] using hconj

/-- Scalar rescaling by a unit does not change the `Option K` Möbius action on affine points. -/
theorem mobiusOption_projective_rescale_some {u : Kˣ}
    (M : Matrix (Fin 2) (Fin 2) K) (z : K) :
    mobiusOption (u • M) (some z) = mobiusOption M (some z) := by
  by_cases h : M 1 0 * z + M 1 1 = 0
  · have hfactor :
        ((u : K) * M 1 0) * z + (u : K) * M 1 1 =
          (u : K) * (M 1 0 * z + M 1 1) := by
        ring
    have hzero : ((u : K) * M 1 0) * z + (u : K) * M 1 1 = 0 := by
      simpa [hfactor] using congrArg (fun t : K => (u : K) * t) h
    have hcond : ((u : K) • M) 1 0 * z + ((u : K) • M) 1 1 = 0 := by
      calc
        ((u : K) • M) 1 0 * z + ((u : K) • M) 1 1
            = ((u : K) * M 1 0) * z + (u : K) * M 1 1 := by
                simp [Matrix.smul_apply, mul_assoc]
        _ = 0 := hzero
    have hleft : mobiusOption (u • M) (some z) = none := by
      simpa [mobiusOption, Matrix.smul_apply, hcond] using hcond
    have hright : mobiusOption M (some z) = none := by
      simpa [mobiusOption, h] using h
    calc
      mobiusOption (u • M) (some z) = none := hleft
      _ = none := rfl
      _ = mobiusOption M (some z) := by symm; exact hright
  · have hu : (u : K) ≠ 0 := Units.ne_zero u
    have hnum :
        ((u : K) * M 0 0) * z + (u : K) * M 0 1 =
          (u : K) * (M 0 0 * z + M 0 1) := by
      ring
    have hden :
        ((u : K) * M 1 0) * z + (u : K) * M 1 1 =
          (u : K) * (M 1 0 * z + M 1 1) := by
      ring
    have hden' : (u : K) * (M 1 0 * z + M 1 1) ≠ 0 := mul_ne_zero hu h
    have hdiv :
        ((u : K) * (M 0 0 * z + M 0 1)) / ((u : K) * (M 1 0 * z + M 1 1)) =
          (M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1) := by
      simpa using
        (mul_div_mul_left (M 0 0 * z + M 0 1) (M 1 0 * z + M 1 1) hu)
    have hleft' :
        ¬ u • M 1 0 * z + u • M 1 1 = 0 ∧
          (u • M 0 0 * z + u • M 0 1) /
            (u • M 1 0 * z + u • M 1 1) =
            ((u : K) * (M 0 0 * z + M 0 1)) / ((u : K) * (M 1 0 * z + M 1 1)) := by
      constructor
      · intro hs
        change ((u : K) * M 1 0) * z + (u : K) * M 1 1 = 0 at hs
        have hs' : (u : K) * (M 1 0 * z + M 1 1) = 0 := by
          simpa [mul_add, add_mul, mul_assoc] using hs
        have hz : M 1 0 * z + M 1 1 = 0 := by
          exact (mul_eq_zero.mp hs').resolve_left hu
        exact False.elim (h hz)
      · change (((u : K) * M 0 0) * z + (u : K) * M 0 1) /
          (((u : K) * M 1 0) * z + (u : K) * M 1 1) =
          ((u : K) * (M 0 0 * z + M 0 1)) / ((u : K) * (M 1 0 * z + M 1 1))
        simp [hnum, hden, mul_assoc]
        ring
    have hleft : mobiusOption (u • M) (some z) =
        some (((u : K) * (M 0 0 * z + M 0 1)) /
          ((u : K) * (M 1 0 * z + M 1 1))) := by
      simpa [mobiusOption, Matrix.smul_apply, hnum, hden, hden'] using hleft'
    have hright : mobiusOption M (some z) =
        some ((M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)) := by
      simp [mobiusOption, h]
    calc
      mobiusOption (u • M) (some z) =
          some (((u : K) * (M 0 0 * z + M 0 1)) /
            ((u : K) * (M 1 0 * z + M 1 1))) := hleft
      _ = some ((M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)) := congrArg some hdiv
      _ = mobiusOption M (some z) := by symm; exact hright

/-- Scalar rescaling by a unit does not change the `Option K` Möbius action. -/
theorem mobiusOption_projective_rescale {u : Kˣ}
    (M : Matrix (Fin 2) (Fin 2) K) :
    mobiusOption (u • M) = mobiusOption M := by
  funext z
  cases z with
  | none =>
      exact mobiusOption_projective_rescale_none (u := u) M
  | some x =>
      exact mobiusOption_projective_rescale_some (u := u) M x

/-- The identity matrix acts as the identity on the projective line. -/
theorem mobiusOption_one (z : Option K) :
    mobiusOption (1 : Matrix (Fin 2) (Fin 2) K) z = z := by
  cases z <;> simp [mobiusOption]

/-- Projective rescaling does not change the Möbius action. -/
theorem mobiusMatrix_projective_rescale {lam : K}
    (M : Matrix (Fin 2) (Fin 2) K) (z : K)
    (hlam : lam ≠ 0) (hden : M 1 0 * z + M 1 1 ≠ 0) :
    mobiusMatrix (lam • M) z = mobiusMatrix M z := by
  unfold mobiusMatrix
  simp [Matrix.smul_apply]
  have hden' : lam * (M 1 0 * z + M 1 1) ≠ 0 := mul_ne_zero hlam hden
  field_simp [hlam, hden, hden']

/-- The `2 × 2` trace used in the Möbius discriminant formulas. -/
def trace2 (M : Matrix (Fin 2) (Fin 2) K) : K := M 0 0 + M 1 1

/-- The determinant of `M - I` in trace form. -/
theorem det_sub_one (M : Matrix (Fin 2) (Fin 2) K) :
    (M - (1 : Matrix (Fin 2) (Fin 2) K)).det = M.det - trace2 M + 1 := by
  simp [trace2, Matrix.det_fin_two, Matrix.sub_apply]
  ring

/-- The determinant of `M + I` in trace form. -/
theorem det_add_one (M : Matrix (Fin 2) (Fin 2) K) :
    (M + (1 : Matrix (Fin 2) (Fin 2) K)).det = M.det + trace2 M + 1 := by
  simp [trace2, Matrix.det_fin_two, Matrix.add_apply]
  ring

/-- The product `(M - I).det * (M + I).det` factors through the trace. -/
theorem det_sub_one_mul_det_add_one (M : Matrix (Fin 2) (Fin 2) K) :
    (M - (1 : Matrix (Fin 2) (Fin 2) K)).det * (M + (1 : Matrix (Fin 2) (Fin 2) K)).det =
      (M.det + 1)^2 - trace2 M ^ 2 := by
  rw [det_sub_one, det_add_one]
  ring

/-- The discriminant `tr(M)^2 - 4 det(M)` used to classify projective dynamics. -/
def mobiusDiscriminant (M : Matrix (Fin 2) (Fin 2) K) : K :=
  trace2 M ^ 2 - 4 * M.det

/-- In the `SL(2)` case, `det(M - I) = 2 - tr(M)`. -/
theorem det_sub_one_sl2 (M : Matrix (Fin 2) (Fin 2) K) (hdet : M.det = 1) :
    (M - (1 : Matrix (Fin 2) (Fin 2) K)).det = 2 - trace2 M := by
  rw [det_sub_one, hdet]
  ring

/-- In the `SL(2)` case, `det(M + I) = 2 + tr(M)`. -/
theorem det_add_one_sl2 (M : Matrix (Fin 2) (Fin 2) K) (hdet : M.det = 1) :
    (M + (1 : Matrix (Fin 2) (Fin 2) K)).det = 2 + trace2 M := by
  rw [det_add_one, hdet]
  ring

/-- In the `SL(2)` case, the `M ± I` boundary factor is `4 - tr(M)^2`. -/
theorem det_sub_one_mul_det_add_one_sl2 (M : Matrix (Fin 2) (Fin 2) K)
    (hdet : M.det = 1) :
    (M - (1 : Matrix (Fin 2) (Fin 2) K)).det * (M + (1 : Matrix (Fin 2) (Fin 2) K)).det =
      4 - trace2 M ^ 2 := by
  rw [det_sub_one_mul_det_add_one, hdet]
  ring

/-- The scalar Cayley compactification is the projective Möbius action of
`[[1, -1/2], [1, 1/2]]`. -/
theorem cayleyCompact_eq_projective_mobius (s : ℂ) :
    cayleyCompact s =
      ProjectivePenrosePGA.mobius 1 (-(1 / 2 : ℂ)) 1 (1 / 2 : ℂ) s := by
  unfold cayleyCompact ProjectivePenrosePGA.mobius
  ring_nf

/-- Projective Möbius + Cayley + discriminant synthesis. -/
theorem projective_mobius_matrix_synthesis :
    (∀ {lam : K} (M : Matrix (Fin 2) (Fin 2) K) (z : K),
      lam ≠ 0 → M 1 0 * z + M 1 1 ≠ 0 →
      mobiusMatrix (lam • M) z = mobiusMatrix M z) ∧
    (∀ (M : Matrix (Fin 2) (Fin 2) K),
      mobiusOption M none = none) ∧
    (∀ (M : Matrix (Fin 2) (Fin 2) K) (z : K),
      mobiusOption M (some z) =
        if h : M 1 0 * z + M 1 1 = 0 then none
        else some ((M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1))) ∧
    (∀ (z : Option K),
      mobiusOption (1 : Matrix (Fin 2) (Fin 2) K) z = z) ∧
    (∀ (M : Matrix (Fin 2) (Fin 2) K),
      (M - (1 : Matrix (Fin 2) (Fin 2) K)).det = M.det - trace2 M + 1) ∧
    (∀ (M : Matrix (Fin 2) (Fin 2) K),
      (M + (1 : Matrix (Fin 2) (Fin 2) K)).det = M.det + trace2 M + 1) ∧
    (∀ (M : Matrix (Fin 2) (Fin 2) K),
      (M - (1 : Matrix (Fin 2) (Fin 2) K)).det * (M + (1 : Matrix (Fin 2) (Fin 2) K)).det =
        (M.det + 1)^2 - trace2 M ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro lam M z hlam hden
    exact mobiusMatrix_projective_rescale M z hlam hden
  · intro M
    rfl
  · intro M z
    rfl
  · intro z
    exact mobiusOption_one z
  · intro M
    exact det_sub_one M
  · intro M
    exact det_add_one M
  · intro M
    exact det_sub_one_mul_det_add_one M

end ProjectiveMobiusMatrix
