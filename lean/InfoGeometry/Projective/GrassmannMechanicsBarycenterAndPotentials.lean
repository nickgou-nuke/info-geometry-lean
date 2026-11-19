/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.PluckerRayAxisAndDyname
import InfoGeometry.Projective.ExteriorRegressive
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Grassmann's *Mechanik* (1877) §§1–4: Vector Calculus, Central Forces, Systems & Constraints

This module formalizes Archetypes `GM₁` (`§1`), `GM₂` (`§2`), `GM₃` (`§3`), `GM₄` (`§4`),
and **Bridge VIa** from Hermann Grassmann's *Die Mechanik nach den Principien der
Ausdehnungslehre* (*Mathematische Annalen* 12, 1877, pp. 222–231):

1. **`GM₁` (`§1`, `pp. 222–226`)**: Orthonormal triads (*Normalverein*) and basis expansion,
   noncommutativity of the outer product `[a b]` and cyclic sign law of the triple product
   `[a b c]`, plus coordinate-invariance of the directional gradient `∂f / ∂x` across all
   orthonormal frames (`grassmannGrad_frame_invariant`).
2. **`GM₂` (`§2`, `pp. 226–227`, `Eq. (1)`)**: Ballistic integration of `δ²x = g`, derivation
   of collinearity (`F A B = c • (B - A)`) and action–reaction reciprocity (`F B A = -F A B`)
   of a simple central force from translation + `SO(3)` half-turn congruence symmetry, and
   the explicit **`[countermodel_found]` Ampère current-element witness** (`p. 227*`).
3. **`GM₃` (`§3`, `pp. 227–230`, `Eqs. (2)–(7)`)**: Skew internal force cancellation,
   barycenter acceleration `Eq. (2)` and relative equations `Eq. (3)`, exterior bivector
   and 3D areal momentum conservation `Eqs. (4)–(5)`, vis viva `Eq. (6)`, the *Streben*
   steepest-ascent Cauchy–Schwarz optimality theorem, and radial pair-potential work `Eq. (7)`.
4. **`GM₄` (`§4`, `pp. 230–231`, `Eqs. (8)–(9)`)**: Constraint gradient forces and
   D'Alembert's principle of virtual work `Eq. (9)`.
5. **Bridge VIa (`Grassmann 1877 §3` ↔ `Plücker 1868/1869 Dyname`)**: Maps particle systems to
   Plücker force–moment dynames, shows symmetric central internal forces contribute zero
   wrench, and applies `exists_two_finite_forces_for_dyname` to split any nonzero particle wrench
   into two finite lines of force.
-/

noncomputable section

namespace InfoGeometry.Projective.GrassmannMechanicsBarycenterAndPotentials

open Matrix ExteriorAlgebra
open InfoGeometry.Projective.PluckerAffineScrew
open InfoGeometry.Projective.PluckerRayAxisAndDyname
open InfoGeometry.Projective.KleinQuadric

section Sec1NormalvereinAndGrad

/-- A triad `e : Fin 3 → Vec3` is orthonormal when `e i ⬝ᵥ e j = δ_{ij}` (`§1`, `p. 223`). -/
def IsOrthonormalFrame3 (e : Fin 3 → Vec3) : Prop :=
  ∀ i j : Fin 3, e i ⬝ᵥ e j = if i = j then 1 else 0

/-- Grassmann's *Normalverein* (`§1`, `p. 223`): a positively oriented orthonormal triad. -/
def IsNormalverein (e : Fin 3 → Vec3) : Prop :=
  IsOrthonormalFrame3 e ∧ (Matrix.of e).det = 1

/-- Standard positively oriented orthonormal basis of `ℝ³`. -/
def stdNormalverein : Fin 3 → Vec3
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![0, 0, 1]

theorem stdNormalverein_isNormalverein : IsNormalverein stdNormalverein := by
  refine ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      simp [stdNormalverein, dotProduct, Fin.sum_univ_three]
  · rw [Matrix.det_fin_three]
    simp [stdNormalverein]

private lemma orthonormal_matrix_mul_transpose (e : Fin 3 → Vec3) (he : IsOrthonormalFrame3 e) :
    Matrix.of e * (Matrix.of e)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simpa [Matrix.of_apply, Matrix.transpose_apply, dotProduct] using he i j

/-- Transpose orthogonality of an orthonormal triad matrix (`Mᵀ * M = 1`). -/
theorem orthonormalFrame_transpose_mul (e : Fin 3 → Vec3) (he : IsOrthonormalFrame3 e) :
    (Matrix.of e)ᵀ * Matrix.of e = 1 :=
  mul_eq_one_comm.mp (orthonormal_matrix_mul_transpose e he)

private lemma vec3_dot_self_nonneg (v : Vec3) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct, Fin.sum_univ_three]
  exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)

/-- Expansion of any vector in an orthonormal frame using inner products (`§1`, `p. 224`). -/
theorem orthonormalFrame_expand (e : Fin 3 → Vec3) (he : IsOrthonormalFrame3 e) (v : Vec3) :
    v = ∑ i : Fin 3, (v ⬝ᵥ e i) • e i := by
  have hMTM := orthonormalFrame_transpose_mul e he
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct]
  calc
    v j = ∑ k : Fin 3, v k * (1 : Matrix (Fin 3) (Fin 3) ℝ) k j := by
      rw [Fin.sum_univ_three]
      fin_cases j <;> simp [Matrix.one_apply]
    _ = ∑ k : Fin 3, v k * ((Matrix.of e)ᵀ * Matrix.of e) k j := by rw [hMTM]
    _ = ∑ k : Fin 3, v k * ∑ i : Fin 3, e i k * e i j := by
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    _ = ∑ i : Fin 3, (∑ k : Fin 3, v k * e i k) * e i j := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      ring

/-- Coordinate-vanishing equivalence in any orthonormal frame (`§1`, `p. 224`). -/
theorem orthonormalFrame_linear_eq_zero_iff (e : Fin 3 → Vec3) (he : IsOrthonormalFrame3 e)
    (c : Fin 3 → ℝ) :
    (∑ i : Fin 3, c i • e i = 0) ↔ ∀ i : Fin 3, c i = 0 := by
  constructor
  · intro h i
    have hdot : (∑ j : Fin 3, c j • e j) ⬝ᵥ e i = 0 := by rw [h, zero_dotProduct]
    have hcalc : (∑ j : Fin 3, c j • e j) ⬝ᵥ e i = c i := by
      rw [sum_dotProduct]
      rw [Finset.sum_eq_single i]
      · rw [smul_dotProduct, he i i]
        simp
      · intro j _ hji
        rw [smul_dotProduct, he j i]
        simp [hji]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    exact hcalc.symm.trans hdot
  · intro h
    simp [h]

private lemma ext_ι_self (x : Vec3) :
    ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ x = 0 :=
  ExteriorAlgebra.ι_sq_zero (R := ℝ) x

private lemma ext_ι_anticomm (x y : Vec3) :
    ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ y =
      -(ExteriorAlgebra.ι ℝ y * ExteriorAlgebra.ι ℝ x) := by
  have hsq : ExteriorAlgebra.ι ℝ (x + y) * ExteriorAlgebra.ι ℝ (x + y) = 0 := ext_ι_self (x + y)
  have h1 : ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ x = 0 := ext_ι_self x
  have h2 : ExteriorAlgebra.ι ℝ y * ExteriorAlgebra.ι ℝ y = 0 := ext_ι_self y
  rw [map_add, add_mul, mul_add, mul_add, h1, h2, zero_add, add_zero] at hsq
  exact eq_neg_of_add_eq_zero_left hsq

private def extMatLiftFun : Vec3 →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ where
  toFun u := Matrix.of ![![0, 0, 0, 0], ![u 0, 0, 0, 0], ![u 1, 0, 0, 0], ![0, -u 1, u 0, 0]]
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.of_apply]; try ring)
  map_smul' r u := by
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.of_apply]; try ring)

private def extMatLift : ExteriorAlgebra ℝ Vec3 →ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  ExteriorAlgebra.lift ℝ ⟨extMatLiftFun, fun u => by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [extMatLiftFun, Matrix.mul_apply, Fin.sum_univ_four]; try ring)⟩

theorem extMat_noncomm_exists : ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨extMatLiftFun ![1, 0, 0], extMatLiftFun ![0, 1, 0], ?_⟩
  intro h
  have h30 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 3 0) h
  norm_num [extMatLiftFun, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four] at h30

/-- Noncommutativity witness for Grassmann's outer product `[a b] = -[b a]` (`§1`, `p. 223`). -/
theorem exterior_strecke_noncomm :
    ∃ a b : Vec3,
      ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ b ≠
        ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ a := by
  refine ⟨![1, 0, 0], ![0, 1, 0], ?_⟩
  intro heq
  have hmap := congrArg (fun X => extMatLift X 3 0) heq
  simp only [map_mul, extMatLift, ExteriorAlgebra.lift_ι_apply, extMatLiftFun,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four,
    Fin.isValue] at hmap
  norm_num at hmap

/-- Cyclic and alternating laws of Grassmann's outer triple product `[a b c]` (`§1`, `p. 223`). -/
theorem exterior_spat_cyclic (a b c : Vec3) :
    ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ c =
        ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ c * ExteriorAlgebra.ι ℝ a ∧
      ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ c =
        -(ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ c * ExteriorAlgebra.ι ℝ b) := by
  have hbc : ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ c =
      -(ExteriorAlgebra.ι ℝ c * ExteriorAlgebra.ι ℝ b) := ext_ι_anticomm b c
  have hab : ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ b =
      -(ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ a) := ext_ι_anticomm a b
  have hac : ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ c =
      -(ExteriorAlgebra.ι ℝ c * ExteriorAlgebra.ι ℝ a) := ext_ι_anticomm a c
  constructor
  · calc
      ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ c
          = -(ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ c) := by
            rw [hab, neg_mul]
      _ = -(ExteriorAlgebra.ι ℝ b * (ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ c)) := by
            rw [mul_assoc]
      _ = ExteriorAlgebra.ι ℝ b * (ExteriorAlgebra.ι ℝ c * ExteriorAlgebra.ι ℝ a) := by
            rw [hac, mul_neg, neg_neg]
      _ = ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ c * ExteriorAlgebra.ι ℝ a := by
            rw [← mul_assoc]
  · calc
      ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ c
          = ExteriorAlgebra.ι ℝ a * (ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ c) := mul_assoc _ _ _
      _ = ExteriorAlgebra.ι ℝ a * -(ExteriorAlgebra.ι ℝ c * ExteriorAlgebra.ι ℝ b) := by rw [hbc]
      _ = -(ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ c * ExteriorAlgebra.ι ℝ b) := by
            rw [mul_neg, mul_assoc]

/-- Grassmann's vector partial derivative `∂f/∂x = ∑ (∂f/∂x_i) e_i` wrt an orthonormal frame
(`§1`, `p. 225`). -/
def grassmannGrad (e : Fin 3 → Vec3) (df : Vec3 →ₗ[ℝ] ℝ) : Vec3 :=
  ∑ i : Fin 3, df (e i) • e i

/-- Inner-product pairing `[(∂f/∂x) | dx] = df(dx)` (`§1`, `p. 225`). -/
theorem grassmannGrad_dot (e : Fin 3 → Vec3) (he : IsOrthonormalFrame3 e)
    (df : Vec3 →ₗ[ℝ] ℝ) (dx : Vec3) :
    grassmannGrad e df ⬝ᵥ dx = df dx := by
  have hexp := orthonormalFrame_expand e he dx
  calc
    grassmannGrad e df ⬝ᵥ dx
        = (∑ i : Fin 3, df (e i) • e i) ⬝ᵥ dx := rfl
    _ = ∑ i : Fin 3, df (e i) * (dx ⬝ᵥ e i) := by
      rw [sum_dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_dotProduct, smul_eq_mul, dotProduct_comm (e i) dx]
    _ = ∑ i : Fin 3, (dx ⬝ᵥ e i) * df (e i) := by
      refine Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = df (∑ i : Fin 3, (dx ⬝ᵥ e i) • e i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    _ = df dx := by rw [← hexp]

/-- Fréchet-differential link: `grassmannGrad e df.toLinearMap ⬝ᵥ dx = df dx` for `HasFDerivAt`. -/
theorem grassmannGrad_fderiv_dot {f : Vec3 → ℝ} {df : Vec3 →L[ℝ] ℝ} {x : Vec3}
    (hf : HasFDerivAt f df x) (e : Fin 3 → Vec3) (he : IsOrthonormalFrame3 e) (dx : Vec3) :
    grassmannGrad e df.toLinearMap ⬝ᵥ dx = df dx ∧ HasFDerivAt f df x :=
  ⟨grassmannGrad_dot e he df.toLinearMap dx, hf⟩

/-- Frame-independence of Grassmann's vector partial derivative (`§1`, `pp. 225–226`):
`grassmannGrad ε df = grassmannGrad e df` for any two orthonormal frames `e, ε`. -/
theorem grassmannGrad_frame_invariant (e ε : Fin 3 → Vec3)
    (he : IsOrthonormalFrame3 e) (hε : IsOrthonormalFrame3 ε) (df : Vec3 →ₗ[ℝ] ℝ) :
    grassmannGrad ε df = grassmannGrad e df := by
  have hdiff : grassmannGrad ε df - grassmannGrad e df = 0 := by
    have hsq : (grassmannGrad ε df - grassmannGrad e df) ⬝ᵥ
        (grassmannGrad ε df - grassmannGrad e df) = 0 := by
      rw [sub_dotProduct, grassmannGrad_dot ε hε, grassmannGrad_dot e he, sub_self]
    exact dotProduct_self_eq_zero.mp hsq
  exact sub_eq_zero.mp hdiff

end Sec1NormalvereinAndGrad

section Sec2Grundgesetz

/-- Constant-force ballistic integration of `δ²x = g` (`§2`, `p. 226`, `Eq. (1)`). -/
theorem ballistic_const_force_integration {x v : ℝ → Vec3} {g : Vec3}
    (hx : ∀ t : ℝ, HasDerivAt x (v t) t) (hv : ∀ t : ℝ, HasDerivAt v g t) (t : ℝ) :
    v t = v 0 + t • g ∧ x t = x 0 + t • v 0 + (t ^ 2 / 2) • g := by
  have hv_comp : ∀ (i : Fin 3) (s : ℝ), v s i = v 0 i + s * g i := by
    intro i s
    have hd : ∀ τ : ℝ, HasDerivAt (fun r => v r i - (v 0 i + r * g i)) 0 τ := by
      intro τ
      have h1 : HasDerivAt (fun r => v r i) (g i) τ := (hasDerivAt_pi.mp (hv τ)) i
      have h2 : HasDerivAt (fun r => v 0 i + r * g i) (0 + (1 * g i)) τ :=
        (hasDerivAt_const τ (v 0 i)).add ((hasDerivAt_id τ).mul_const (g i))
      convert h1.sub h2 using 1
      ring
    have hconst := is_const_of_deriv_eq_zero
      (fun τ => (hd τ).differentiableAt) (fun τ => (hd τ).deriv) s 0
    have h0 : v 0 i - (v 0 i + 0 * g i) = 0 := by ring
    linarith [hconst, h0]
  have hv_vec : ∀ s : ℝ, v s = v 0 + s • g := by
    intro s
    ext i
    simp [hv_comp i s]
  have hx_comp : ∀ (i : Fin 3) (s : ℝ), x s i = x 0 i + s * v 0 i + (s ^ 2 / 2) * g i := by
    intro i s
    have hd : ∀ τ : ℝ,
        HasDerivAt (fun r => x r i - (x 0 i + r * v 0 i + (r ^ 2 / 2) * g i)) 0 τ := by
      intro τ
      have h1 : HasDerivAt (fun r => x r i) (v τ i) τ := (hasDerivAt_pi.mp (hx τ)) i
      have hpow : HasDerivAt (fun r : ℝ => r ^ 2 / 2) (τ) τ := by
        simpa [one_mul] using ((hasDerivAt_pow 2 τ).div_const 2)
      have h2 : HasDerivAt (fun r => x 0 i + r * v 0 i + (r ^ 2 / 2) * g i)
          (0 + 1 * v 0 i + τ * g i) τ :=
        ((hasDerivAt_const τ (x 0 i)).add ((hasDerivAt_id τ).mul_const (v 0 i))).add
          (hpow.mul_const (g i))
      have hsub := h1.sub h2
      rw [hv_comp i τ] at hsub
      convert hsub using 1
      ring
    have hconst := is_const_of_deriv_eq_zero
      (fun τ => (hd τ).differentiableAt) (fun τ => (hd τ).deriv) s 0
    have h0 : x 0 i - (x 0 i + 0 * v 0 i + (0 ^ 2 / 2) * g i) = 0 := by ring
    linarith [hconst, h0]
  refine ⟨hv_vec t, ?_⟩
  ext i
  simp [hx_comp i t]

/-- Half-turn rotation matrix `2 u uᵀ - I` about axis `u` (`§2`, `pp. 226–227`). -/
def halfTurnMatrix (u : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => 2 * u i * u j - if i = j then 1 else 0

theorem halfTurnMatrix_orthog (u : Vec3) (hu : u ⬝ᵥ u = 1) :
    (halfTurnMatrix u)ᵀ * halfTurnMatrix u = 1 := by
  have hdot : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hu
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [halfTurnMatrix, Matrix.transpose_apply, Fin.ext_iff]
  · linear_combination (4 * u 0 ^ 2) * hdot
  · linear_combination (4 * u 0 * u 1) * hdot
  · linear_combination (4 * u 0 * u 2) * hdot
  · linear_combination (4 * u 1 * u 0) * hdot
  · linear_combination (4 * u 1 ^ 2) * hdot
  · linear_combination (4 * u 1 * u 2) * hdot
  · linear_combination (4 * u 2 * u 0) * hdot
  · linear_combination (4 * u 2 * u 1) * hdot
  · linear_combination (4 * u 2 ^ 2) * hdot

/-- Determinant `+1` of the half-turn matrix for any unit axis `u` (`SO(3)` membership). -/
theorem halfTurnMatrix_det (u : Vec3) (hu : u ⬝ᵥ u = 1) :
    (halfTurnMatrix u).det = 1 := by
  have hdot : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hu
  rw [Matrix.det_fin_three]
  simp only [halfTurnMatrix, Matrix.of_apply, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  linear_combination (2 : ℝ) * hdot

theorem halfTurnMatrix_mulVec_eq (u v : Vec3) :
    halfTurnMatrix u *ᵥ v = (2 * (u ⬝ᵥ v)) • u - v := by
  ext i
  rw [mulVec, dotProduct, Fin.sum_univ_three]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_three,
    halfTurnMatrix, Matrix.of_apply]
  fin_cases i <;> (simp [Fin.ext_iff]; ring)

theorem halfTurnMatrix_mulVec_self (u : Vec3) (hu : u ⬝ᵥ u = 1) :
    halfTurnMatrix u *ᵥ u = u := by
  rw [halfTurnMatrix_mulVec_eq, hu]
  ext i; simp; ring

theorem halfTurnMatrix_mulVec_orth (u w : Vec3) (hw : u ⬝ᵥ w = 0) :
    halfTurnMatrix u *ᵥ w = -w := by
  rw [halfTurnMatrix_mulVec_eq, hw]
  simp

/-- Noncommutativity witness for `SO(3)` spatial congruences via two axis half-turns. -/
theorem so3_halfTurn_noncomm :
    halfTurnMatrix ![1, 0, 0] * halfTurnMatrix ![3 / 5, 4 / 5, 0] ≠
      halfTurnMatrix ![3 / 5, 4 / 5, 0] * halfTurnMatrix ![1, 0, 0] := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  norm_num [Matrix.mul_apply, halfTurnMatrix, Fin.sum_univ_three] at h01

theorem so3_halfTurn_noncomm_exists :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℝ, A * B ≠ B * A :=
  ⟨halfTurnMatrix ![1, 0, 0], halfTurnMatrix ![3 / 5, 4 / 5, 0], so3_halfTurn_noncomm⟩

private lemma exists_unit_orth (v : Vec3) : ∃ u : Vec3, u ⬝ᵥ u = 1 ∧ u ⬝ᵥ v = 0 := by
  by_cases hv : v 0 = 0 ∧ v 1 = 0
  · refine ⟨![1, 0, 0], ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_three]
    · simp [dotProduct, Fin.sum_univ_three, hv.1, hv.2]
  · let w : Vec3 := ![v 1, -v 0, 0]
    have hwpos : 0 < w ⬝ᵥ w := by
      have hsq : w ⬝ᵥ w = v 1 ^ 2 + v 0 ^ 2 := by
        simp [w, dotProduct, Fin.sum_univ_three]; ring
      rw [hsq]
      rcases not_and_or.mp hv with h0 | h1
      · positivity
      · positivity
    have hnorm : w ⬝ᵥ w ≠ 0 := hwpos.ne'
    let s := Real.sqrt (w ⬝ᵥ w)
    have hspos : 0 < s := Real.sqrt_pos.mpr hwpos
    refine ⟨s⁻¹ • w, ?_, ?_⟩
    · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have hsq : Real.sqrt (w ⬝ᵥ w) ^ 2 = w ⬝ᵥ w := Real.sq_sqrt hwpos.le
      simp only [s]
      field_simp [hspos.ne', hnorm]
      exact hsq.symm
    · rw [smul_dotProduct, smul_eq_mul]
      have hwdot : w ⬝ᵥ v = 0 := by
        simp [w, dotProduct, Fin.sum_univ_three]; ring
      rw [hwdot, mul_zero]

/-- Grassmann's congruence argument (`§2`, `p. 226`): a coincident simple force vanishes
automatically under `SO(3)` equivariance. -/
theorem einfacheKraft_diag_zero (F : Vec3 → Vec3 → Vec3)
    (hso3 : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ), Rᵀ * R = 1 → R.det = 1 →
      ∀ A B, F (R *ᵥ A) (R *ᵥ B) = R *ᵥ F A B) :
    F 0 0 = 0 := by
  rcases exists_unit_orth (F 0 0) with ⟨u, hu, horth⟩
  have hneg : halfTurnMatrix u *ᵥ F 0 0 = -F 0 0 := halfTurnMatrix_mulVec_orth u (F 0 0) horth
  have hinv := hso3 (halfTurnMatrix u) (halfTurnMatrix_orthog u hu)
    (halfTurnMatrix_det u hu) 0 0
  simp only [mulVec_zero] at hinv
  rw [← hinv] at hneg
  have h2 : (2 : ℝ) • F 0 0 = 0 := by
    rw [two_smul]
    calc
      F 0 0 + F 0 0 = F 0 0 + (-F 0 0) := by nth_rw 2 [hneg]
      _ = 0 := add_neg_cancel _
  simpa using congrArg ((1 / 2 : ℝ) • ·) h2

/-- Grassmann's line-of-action theorem (`§2`, `pp. 226–227`): every Euclidean-congruence-covariant
*einfache Kraft* acts strictly along the line joining `A` and `B`. -/
theorem einfacheKraft_collinear (F : Vec3 → Vec3 → Vec3)
    (htrans : ∀ A B t : Vec3, F (A + t) (B + t) = F A B)
    (hso3 : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ), Rᵀ * R = 1 → R.det = 1 →
      ∀ A B, F (R *ᵥ A) (R *ᵥ B) = R *ᵥ F A B)
    (A B : Vec3) :
    ∃ c : ℝ, F A B = c • (B - A) := by
  let d : Vec3 := B - A
  have hFAB : F A B = F 0 d := by
    simpa [d, sub_eq_add_neg] using (htrans A B (-A)).symm
  by_cases hd : d = 0
  · refine ⟨0, ?_⟩
    rw [hFAB, hd, einfacheKraft_diag_zero F hso3, zero_smul]
  · have hdpos : 0 < d ⬝ᵥ d := by
      rcases lt_trichotomy (d ⬝ᵥ d) 0 with hlt | heq | hgt
      · exact False.elim (lt_irrefl _ (hlt.trans_le (vec3_dot_self_nonneg d)))
      · exact False.elim (hd (dotProduct_self_eq_zero.mp heq))
      · exact hgt
    let s := Real.sqrt (d ⬝ᵥ d)
    have hspos : 0 < s := Real.sqrt_pos.mpr hdpos
    let u : Vec3 := s⁻¹ • d
    have hu : u ⬝ᵥ u = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have hsq : Real.sqrt (d ⬝ᵥ d) ^ 2 = d ⬝ᵥ d := Real.sq_sqrt hdpos.le
      simp only [s]
      field_simp [hspos.ne', hdpos.ne']
      exact hsq.symm
    have hRu_d : halfTurnMatrix u *ᵥ d = d := by
      calc
        halfTurnMatrix u *ᵥ d = halfTurnMatrix u *ᵥ (s • u) := by
          simp [u, smul_smul, mul_inv_cancel₀ hspos.ne']
        _ = s • (halfTurnMatrix u *ᵥ u) := mulVec_smul _ _ _
        _ = s • u := by rw [halfTurnMatrix_mulVec_self u hu]
        _ = d := by simp [u, smul_smul, mul_inv_cancel₀ hspos.ne']
    have hfix := hso3 (halfTurnMatrix u) (halfTurnMatrix_orthog u hu)
      (halfTurnMatrix_det u hu) 0 d
    rw [mulVec_zero, hRu_d] at hfix
    rw [halfTurnMatrix_mulVec_eq] at hfix
    have h2 : (2 : ℝ) • F 0 d = (2 * (u ⬝ᵥ F 0 d)) • u := by
      ext i
      have hi := congrFun hfix i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
      linarith
    have hf_u : F 0 d = (u ⬝ᵥ F 0 d) • u := by
      have hhalf := congrArg ((1 / 2 : ℝ) • ·) h2
      simpa [smul_smul] using hhalf
    refine ⟨(u ⬝ᵥ F 0 d) * s⁻¹, ?_⟩
    conv_lhs => rw [hFAB, hf_u]
    simp only [u, d, smul_smul]

/-- Grassmann's action–reaction reciprocity (`§2`, `p. 227`): Euclidean congruence symmetry alone
forces `F B A = - F A B` for equal points of the same physical constitution. -/
theorem einfacheKraft_action_reaction (F : Vec3 → Vec3 → Vec3)
    (htrans : ∀ A B t : Vec3, F (A + t) (B + t) = F A B)
    (hso3 : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ), Rᵀ * R = 1 → R.det = 1 →
      ∀ A B, F (R *ᵥ A) (R *ᵥ B) = R *ᵥ F A B)
    (A B : Vec3) :
    F B A = -F A B := by
  let d : Vec3 := B - A
  have hFAB : F A B = F 0 d := by
    simpa [d, sub_eq_add_neg] using (htrans A B (-A)).symm
  have hFBA : F B A = F 0 (-d) := by
    have hneg : A + (-B) = -d := by simp [d]; abel
    simpa [hneg] using (htrans B A (-B)).symm
  rcases exists_unit_orth d with ⟨n, hn, horth⟩
  have hRnd : halfTurnMatrix n *ᵥ d = -d := halfTurnMatrix_mulVec_orth n d horth
  have hso := hso3 (halfTurnMatrix n) (halfTurnMatrix_orthog n hn)
    (halfTurnMatrix_det n hn) 0 d
  rw [mulVec_zero, hRnd, ← hFAB, ← hFBA] at hso
  rcases einfacheKraft_collinear F htrans hso3 A B with ⟨c, hc⟩
  change halfTurnMatrix n *ᵥ (B - A) = -d at hRnd
  rw [hso, hc, mulVec_smul, hRnd, smul_neg]

/-- Ampère-type current element force law `v₁ × (v₂ × r)` (`§2`, `p. 227*`). -/
def ampereForce (v₁ v₂ r : Vec3) : Vec3 :=
  v₁ ⨯₃ (v₂ ⨯₃ r)

/-- **`[countermodel_found]`** Grassmann's Footnote `*` (`p. 227`): Ampère's electrodynamic force
between current elements fails both collinearity and action–reaction reciprocity. -/
theorem grassmann_footnote_p227_ampere_countermodel :
    let v₁ : Vec3 := ![1, 0, 0]
    let v₂ : Vec3 := ![0, 1, 0]
    let r : Vec3 := ![1, 0, 0]
    (∀ c : ℝ, ampereForce v₁ v₂ r ≠ c • r) ∧
      ampereForce v₁ v₂ r + ampereForce v₂ v₁ (-r) ≠ 0 := by
  dsimp
  have h12 : ampereForce ![1, 0, 0] ![0, 1, 0] ![1, 0, 0] = ![0, 1, 0] := by
    ext i; fin_cases i <;> simp [ampereForce, cross_apply]
  have h21 : ampereForce ![0, 1, 0] ![1, 0, 0] (-![1, 0, 0]) = 0 := by
    ext i; fin_cases i <;> simp [ampereForce, cross_apply]
  constructor
  · intro c hc
    rw [h12] at hc
    have h1 := congrFun hc 1
    norm_num at h1
  · rw [h12, h21, add_zero]
    intro hz
    have h1 := congrFun hz 1
    norm_num at h1

end Sec2Grundgesetz

section Sec3SystemLaws

/-- Pairwise opposite internal forces sum to zero (`§3`, `pp. 227–228`). -/
theorem internal_forces_sum_zero {m : ℕ} (P_int : Fin m → Fin m → Vec3)
    (hskew : ∀ i j, P_int j i = -P_int i j) :
    (∑ i : Fin m, ∑ j : Fin m, P_int i j) = 0 := by
  have htwice :
      (∑ i : Fin m, ∑ j : Fin m, P_int i j) +
        (∑ i : Fin m, ∑ j : Fin m, P_int i j) = 0 := by
    calc
      (∑ i : Fin m, ∑ j : Fin m, P_int i j) +
          (∑ i : Fin m, ∑ j : Fin m, P_int i j)
          = (∑ i : Fin m, ∑ j : Fin m, P_int i j) +
              (∑ i : Fin m, ∑ j : Fin m, P_int j i) := by
            congr 1; exact Finset.sum_comm
      _ = ∑ i : Fin m, ∑ j : Fin m, (P_int i j + P_int j i) := by
            simp_rw [← Finset.sum_add_distrib]
      _ = 0 := by
            refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
            rw [hskew i j, add_neg_cancel]
  have h2 : (2 : ℝ) • (∑ i : Fin m, ∑ j : Fin m, P_int i j) = 0 := by
    rwa [two_smul]
  simpa using congrArg ((1 / 2 : ℝ) • ·) h2

/-- Barycenter `s = (1/m) ∑ x_i` of an equal-mass particle system (`§3`, `p. 228`). -/
def barycenter (m : ℕ) (x : Fin m → Vec3) : Vec3 :=
  (m : ℝ)⁻¹ • ∑ i : Fin m, x i

/-- Relative coordinates `y_i = x_i - s` about the barycenter (`§3`, `p. 228`). -/
def relCoords (m : ℕ) (x : Fin m → Vec3) (i : Fin m) : Vec3 :=
  x i - barycenter m x

theorem sum_relCoords_eq_zero {m : ℕ} (hm : m ≠ 0) (x : Fin m → Vec3) :
    ∑ i : Fin m, relCoords m x i = 0 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [show (∑ i : Fin m, relCoords m x i) =
      (∑ i : Fin m, x i) - (m : ℝ) • barycenter m x by
    simp only [relCoords, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Nat.cast_smul_eq_nsmul]]
  simp [barycenter, smul_smul, hmR]

/-- Center-of-mass equation `δ²s = (1/m) p` (`§3`, `p. 228`, `Eq. (2)`). -/
theorem barycenter_accel_eq {m : ℕ} (p_ext : Fin m → Vec3) (P_int : Fin m → Fin m → Vec3)
    (a : Fin m → Vec3) (hnewton : ∀ i, a i = p_ext i + ∑ j : Fin m, P_int i j)
    (hskew : ∀ i j, P_int j i = -P_int i j) :
    (m : ℝ)⁻¹ • ∑ i : Fin m, a i = (m : ℝ)⁻¹ • ∑ i : Fin m, p_ext i := by
  simp_rw [hnewton, Finset.sum_add_distrib, internal_forces_sum_zero P_int hskew, add_zero]

/-- Relative motion equations `δ²y_i = p_i - (1/m) p` (`§3`, `p. 228`, `Eq. (3)`). -/
theorem relCoord_accel_eq {m : ℕ} (a p_ext : Fin m → Vec3) (P_int : Fin m → Fin m → Vec3)
    (hnewton : ∀ i, a i = p_ext i + ∑ j : Fin m, P_int i j)
    (hskew : ∀ i j, P_int j i = -P_int i j) (i : Fin m) :
    a i - (m : ℝ)⁻¹ • ∑ k : Fin m, a k =
      (p_ext i + ∑ j : Fin m, P_int i j) - (m : ℝ)⁻¹ • ∑ k : Fin m, p_ext k := by
  rw [barycenter_accel_eq p_ext P_int a hnewton hskew, hnewton i]

/-- Grassmann's exterior bivector areal momentum `∑ [x_i δx_i]` (`§3`, `p. 228`, `Eq. (4)`). -/
def arealMomentum {m : ℕ} (x v : Fin m → Vec3) : ExteriorAlgebra ℝ Vec3 :=
  ∑ i : Fin m, ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (v i)

/-- Internal central forces contribute zero bivector torque (`§3`, `p. 228`, `Eq. (4)`). -/
theorem internal_central_torque_bivector_zero {m : ℕ} (x : Fin m → Vec3) (c : Fin m → Fin m → ℝ)
    (hsym : ∀ i j, c j i = c i j) :
    ∑ i : Fin m, ∑ j : Fin m,
        ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (c i j • (x j - x i)) = 0 := by
  have hterm : ∀ i j : Fin m,
      ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (c i j • (x j - x i)) =
        c i j • (ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (x j)) := by
    intro i j
    rw [map_smul, mul_smul_comm, map_sub, mul_sub, ext_ι_self, sub_zero]
  simp_rw [hterm]
  have htwice :
      (∑ i : Fin m, ∑ j : Fin m, c i j • (ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (x j))) +
        (∑ i : Fin m, ∑ j : Fin m, c i j • (ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (x j))) = 0 := by
    calc
      (∑ i : Fin m, ∑ j : Fin m, c i j • (ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (x j))) +
          (∑ i : Fin m, ∑ j : Fin m, c i j • (ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (x j)))
          = (∑ i : Fin m, ∑ j : Fin m, c i j • (ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (x j))) +
              (∑ i : Fin m, ∑ j : Fin m, c j i • (ExteriorAlgebra.ι ℝ (x j) * ExteriorAlgebra.ι ℝ (x i))) := by
            congr 1; exact Finset.sum_comm
      _ = ∑ i : Fin m, ∑ j : Fin m,
            (c i j • (ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (x j)) +
              c j i • (ExteriorAlgebra.ι ℝ (x j) * ExteriorAlgebra.ι ℝ (x i))) := by
            simp_rw [← Finset.sum_add_distrib]
      _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        rw [hsym i j, ext_ι_anticomm (x j) (x i), smul_neg, add_neg_cancel]
  have h2 : (2 : ℝ) • (∑ i : Fin m, ∑ j : Fin m,
      c i j • (ExteriorAlgebra.ι ℝ (x i) * ExteriorAlgebra.ι ℝ (x j))) = 0 := by
    rwa [two_smul]
  simpa [smul_smul] using congrArg ((1 / 2 : ℝ) • ·) h2

/-- Moving-barycenter invariance of exterior areal torque `Eq. (5)` (`§3`, `p. 229`). -/
theorem barycenter_areal_torque_eq_five {m : ℕ} (hm : m ≠ 0) (x p : Fin m → Vec3) :
    ∑ i : Fin m, ExteriorAlgebra.ι ℝ (relCoords m x i) *
        ExteriorAlgebra.ι ℝ (p i - (m : ℝ)⁻¹ • ∑ j : Fin m, p j) =
      ∑ i : Fin m, ExteriorAlgebra.ι ℝ (relCoords m x i) * ExteriorAlgebra.ι ℝ (p i) := by
  have hsub : ∀ i : Fin m,
      ExteriorAlgebra.ι ℝ (relCoords m x i) *
          ExteriorAlgebra.ι ℝ (p i - (m : ℝ)⁻¹ • ∑ j : Fin m, p j) =
        ExteriorAlgebra.ι ℝ (relCoords m x i) * ExteriorAlgebra.ι ℝ (p i) -
          ExteriorAlgebra.ι ℝ (relCoords m x i) *
            ExteriorAlgebra.ι ℝ ((m : ℝ)⁻¹ • ∑ j : Fin m, p j) := by
    intro i
    rw [map_sub, mul_sub]
  simp_rw [hsub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum,
    sum_relCoords_eq_zero hm x, map_zero, zero_mul, sub_zero]

/-- 3D areal momentum `∑ x_i × v_i` satisfies exact derivative conservation when central internal
forces and central origin forces act (`§3`, `p. 228`, `Eq. (4)`). -/
theorem arealMomentum_vec3_hasDerivAt_eq_torque {m : ℕ} (x v a : ℝ → Fin m → Vec3)
    (t : ℝ) (hx : ∀ i, HasDerivAt (fun s => x s i) (v t i) t)
    (hv : ∀ i, HasDerivAt (fun s => v s i) (a t i) t) :
    HasDerivAt (fun s => ∑ i : Fin m, x s i ⨯₃ v s i)
      (∑ i : Fin m, x t i ⨯₃ a t i) t := by
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasDerivAt (fun s => x s i ⨯₃ v s i) (x t i ⨯₃ a t i) t := by
    intro i _
    rw [hasDerivAt_pi]
    intro k
    have hx0 := (hasDerivAt_pi.mp (hx i)) 0
    have hx1 := (hasDerivAt_pi.mp (hx i)) 1
    have hx2 := (hasDerivAt_pi.mp (hx i)) 2
    have hv0 := (hasDerivAt_pi.mp (hv i)) 0
    have hv1 := (hasDerivAt_pi.mp (hv i)) 1
    have hv2 := (hasDerivAt_pi.mp (hv i)) 2
    fin_cases k
    · convert (hx1.mul hv2).sub (hx2.mul hv1) using 1
      · funext s; simp [cross_apply]
      · simp [cross_apply]; ring
    · convert (hx2.mul hv0).sub (hx0.mul hv2) using 1
      · funext s; simp [cross_apply]
      · simp [cross_apply]; ring
    · convert (hx0.mul hv1).sub (hx1.mul hv0) using 1
      · funext s; simp [cross_apply]
      · simp [cross_apply]; ring
  convert HasDerivAt.sum hterm using 1
  funext s
  simp only [Finset.sum_apply]

/-- Internal central forces cancel in the 3D cross-product torque sum. -/
theorem internal_central_cross_torque_zero {m : ℕ} (x : Fin m → Vec3) (c : Fin m → Fin m → ℝ)
    (hsym : ∀ i j, c j i = c i j) :
    ∑ i : Fin m, ∑ j : Fin m, x i ⨯₃ (c i j • (x j - x i)) = 0 := by
  have hterm : ∀ i j : Fin m,
      x i ⨯₃ (c i j • (x j - x i)) = c i j • (x i ⨯₃ x j) := by
    intro i j
    rw [LinearMap.map_smul, map_sub, cross_self, sub_zero]
  simp_rw [hterm]
  have htwice :
      (∑ i : Fin m, ∑ j : Fin m, c i j • (x i ⨯₃ x j)) +
        (∑ i : Fin m, ∑ j : Fin m, c i j • (x i ⨯₃ x j)) = 0 := by
    calc
      (∑ i : Fin m, ∑ j : Fin m, c i j • (x i ⨯₃ x j)) +
          (∑ i : Fin m, ∑ j : Fin m, c i j • (x i ⨯₃ x j))
          = (∑ i : Fin m, ∑ j : Fin m, c i j • (x i ⨯₃ x j)) +
              (∑ i : Fin m, ∑ j : Fin m, c j i • (x j ⨯₃ x i)) := by
            congr 1; exact Finset.sum_comm
      _ = ∑ i : Fin m, ∑ j : Fin m, (c i j • (x i ⨯₃ x j) + c j i • (x j ⨯₃ x i)) := by
            simp_rw [← Finset.sum_add_distrib]
      _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        rw [hsym i j]
        ext k
        fin_cases k <;> simp [cross_apply] <;> ring
  have h2 : (2 : ℝ) • (∑ i : Fin m, ∑ j : Fin m, c i j • (x i ⨯₃ x j)) = 0 := by
    rwa [two_smul]
  simpa using congrArg ((1 / 2 : ℝ) • ·) h2

/-- Vis viva / kinetic-energy work identity `Eq. (6)` (`§3`, `p. 229`):
`δ (1/2 ∑ (δx)²) = ∑ [p | δx]`. -/
theorem vis_viva_eq_six {m : ℕ} (v p : ℝ → Fin m → Vec3) (t : ℝ)
    (hv : ∀ i, HasDerivAt (fun s => v s i) (p t i) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ∑ i : Fin m, v s i ⬝ᵥ v s i)
      (∑ i : Fin m, p t i ⬝ᵥ v t i) t := by
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasDerivAt (fun s => v s i ⬝ᵥ v s i) (2 * (p t i ⬝ᵥ v t i)) t := by
    intro i _
    have h0 := (hasDerivAt_pi.mp (hv i)) 0
    have h1 := (hasDerivAt_pi.mp (hv i)) 1
    have h2 := (hasDerivAt_pi.mp (hv i)) 2
    have hd := ((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)
    convert hd using 1
    · funext s; simp [dotProduct, Fin.sum_univ_three]
    · simp [dotProduct, Fin.sum_univ_three]; ring
  have hsum := (HasDerivAt.sum hterm).const_mul (1 / 2 : ℝ)
  convert hsum using 1
  · funext s
    simp only [Finset.sum_apply]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

/-- Exact Lagrange identity for `Fin 3 → ℝ` giving Cauchy–Schwarz (`§3`, `p. 229`). -/
theorem vec3_cauchy_schwarz (u v : Vec3) :
    (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  have hid : (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 =
      (u 0 * v 1 - u 1 * v 0) ^ 2 + (u 0 * v 2 - u 2 * v 0) ^ 2 +
        (u 1 * v 2 - u 2 * v 1) ^ 2 := by
    simp [dotProduct, Fin.sum_univ_three]
    ring
  nlinarith [sq_nonneg (u 0 * v 1 - u 1 * v 0), sq_nonneg (u 0 * v 2 - u 2 * v 0),
    sq_nonneg (u 1 * v 2 - u 2 * v 1)]

/-- Grassmann's *Streben* steepest-ascent theorem (`§3`, `p. 229`): among displacements of fixed
length `L`, the first-order increment `[∂U/∂x | dx]` is uniquely maximized along `∂U/∂x`. -/
theorem streben_steepest_ascent (g : Vec3) (hg : g ≠ 0) {L : ℝ} (hL : 0 ≤ L) :
    let normg := Real.sqrt (g ⬝ᵥ g)
    let dxOpt : Vec3 := (L / normg) • g
    dxOpt ⬝ᵥ dxOpt = L ^ 2 ∧
      g ⬝ᵥ dxOpt = L * normg ∧
      ∀ dx : Vec3, dx ⬝ᵥ dx = L ^ 2 → g ⬝ᵥ dx ≤ g ⬝ᵥ dxOpt := by
  dsimp
  have hgpos : 0 < g ⬝ᵥ g := by
    rcases lt_or_gt_of_ne (fun h => hg (dotProduct_self_eq_zero.mp h)) with hlt | hgt
    · exact False.elim (lt_irrefl _ (hlt.trans_le (vec3_dot_self_nonneg g)))
    · exact hgt
  have hnorm_pos : 0 < Real.sqrt (g ⬝ᵥ g) := Real.sqrt_pos.mpr hgpos
  have hsq : Real.sqrt (g ⬝ᵥ g) ^ 2 = g ⬝ᵥ g := Real.sq_sqrt hgpos.le
  refine ⟨?_, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp [hnorm_pos.ne']
    nlinarith [hsq]
  · rw [dotProduct_smul, smul_eq_mul]
    field_simp [hnorm_pos.ne']
    nlinarith [hsq]
  · intro dx hdx
    have hcs := vec3_cauchy_schwarz g dx
    rw [hdx] at hcs
    have hopt_eq : g ⬝ᵥ ((L / Real.sqrt (g ⬝ᵥ g)) • g) = L * Real.sqrt (g ⬝ᵥ g) := by
      rw [dotProduct_smul, smul_eq_mul]
      field_simp [hnorm_pos.ne']
      nlinarith [hsq]
    rw [hopt_eq]
    have hsq_eq : (L * Real.sqrt (g ⬝ᵥ g)) ^ 2 = (g ⬝ᵥ g) * L ^ 2 := by
      calc
        (L * Real.sqrt (g ⬝ᵥ g)) ^ 2 = L ^ 2 * Real.sqrt (g ⬝ᵥ g) ^ 2 := by ring
        _ = (g ⬝ᵥ g) * L ^ 2 := by rw [hsq, mul_comm]
    rw [← hsq_eq] at hcs
    exact le_of_sq_le_sq hcs (mul_nonneg hL hnorm_pos.le)

/-- Derivative of Euclidean pair distance `r(t) = √((x₁(t) - x₂(t)) ⬝ᵥ (x₁(t) - x₂(t)))`
and Grassmann's radial potential increment `dU₁₂ = [p₂₁ | dx₁ - dx₂]` (`§3`, `p. 230`, `Eq. (7)`). -/
theorem radial_pair_potential_hasDerivAt {x₁ x₂ v₁ v₂ : ℝ → Vec3}
    {Φ : ℝ → ℝ} {f : ℝ → ℝ} {t : ℝ}
    (hx₁ : HasDerivAt x₁ (v₁ t) t) (hx₂ : HasDerivAt x₂ (v₂ t) t)
    (hsep : x₁ t - x₂ t ≠ 0)
    (hΦ : HasDerivAt Φ (f (Real.sqrt ((x₁ t - x₂ t) ⬝ᵥ (x₁ t - x₂ t))))
      (Real.sqrt ((x₁ t - x₂ t) ⬝ᵥ (x₁ t - x₂ t)))) :
    let r : ℝ → ℝ := fun s => Real.sqrt ((x₁ s - x₂ s) ⬝ᵥ (x₁ s - x₂ s))
    let p₂₁ : Vec3 := ((f (r t)) / r t) • (x₁ t - x₂ t)
    HasDerivAt (fun s => Φ (r s)) (p₂₁ ⬝ᵥ (v₁ t - v₂ t)) t := by
  dsimp
  let d : ℝ → Vec3 := fun s => x₁ s - x₂ s
  have hd : HasDerivAt d (v₁ t - v₂ t) t := hx₁.sub hx₂
  have hsq : HasDerivAt (fun s => d s ⬝ᵥ d s) (2 * (d t ⬝ᵥ (v₁ t - v₂ t))) t := by
    have h0 := (hasDerivAt_pi.mp hd) 0
    have h1 := (hasDerivAt_pi.mp hd) 1
    have h2 := (hasDerivAt_pi.mp hd) 2
    convert ((h0.mul h0).add (h1.mul h1)).add (h2.mul h2) using 1
    · funext s; simp [dotProduct, Fin.sum_univ_three]
    · simp [dotProduct, Fin.sum_univ_three]; ring
  have hdt_ne : d t ⬝ᵥ d t ≠ 0 := fun h => hsep (dotProduct_self_eq_zero.mp h)
  have hr : HasDerivAt (fun s => Real.sqrt (d s ⬝ᵥ d s))
      ((2 * (d t ⬝ᵥ (v₁ t - v₂ t))) / (2 * Real.sqrt (d t ⬝ᵥ d t))) t :=
    hsq.sqrt hdt_ne
  have hrpos : 0 < Real.sqrt (d t ⬝ᵥ d t) := by
    refine Real.sqrt_pos.mpr ?_
    rcases lt_or_gt_of_ne hdt_ne with hlt | hgt
    · exact False.elim (lt_irrefl _ (hlt.trans_le (vec3_dot_self_nonneg (d t))))
    · exact hgt
  have hchain := hΦ.comp t hr
  convert hchain using 1
  · rfl
  · rw [smul_dotProduct, smul_eq_mul]
    dsimp only [d]
    field_simp [hrpos.ne']

end Sec3SystemLaws

section Sec4ConstraintsAndBridgeVIa

/-- Lagrange multiplier equations `δ²x_i = p_i + ∑ α, μ_α (∂L_α/∂x_i)` and
D'Alembert's principle of virtual work `∑ [(δ²x - p) | dx] = 0` (`§4`, `p. 231`, `Eqs. (8)–(9)`). -/
theorem dalembert_virtual_work_eq_zero {m k : ℕ} (a p dx : Fin m → Vec3)
    (gradL : Fin k → Fin m → Vec3) (μ : Fin k → ℝ)
    (heq8 : ∀ i : Fin m, a i = p i + ∑ α : Fin k, μ α • gradL α i)
    (hvirt : ∀ α : Fin k, ∑ i : Fin m, gradL α i ⬝ᵥ dx i = 0) :
    ∑ i : Fin m, (a i - p i) ⬝ᵥ dx i = 0 := by
  have hsub : ∀ i : Fin m, (a i - p i) ⬝ᵥ dx i = ∑ α : Fin k, μ α * (gradL α i ⬝ᵥ dx i) := by
    intro i
    rw [heq8 i, add_sub_cancel_left, sum_dotProduct]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [smul_dotProduct, smul_eq_mul]
  simp_rw [hsub]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [← Finset.mul_sum, hvirt α, mul_zero]

/-- **Bridge VIa**: Maps a particle configuration and force/momentum vectors to Plücker's 6D
line–dyname coordinate vector `(∑ p_i, ∑ x_i × p_i)` (`PluckerRayAxisAndDyname`). -/
def particleSystemDyname {m : ℕ} (x p : Fin m → Vec3) : KleinQuadric.Plucker6 ℝ :=
  plucker6Equiv.symm (directionMomentEquiv.symm (∑ i : Fin m, p i, ∑ i : Fin m, x i ⨯₃ p i))

@[simp]
theorem particleSystemDyname_kleinQ {m : ℕ} (x p : Fin m → Vec3) :
    (particleSystemDyname x p).kleinQ = (∑ i : Fin m, p i) ⬝ᵥ (∑ i : Fin m, x i ⨯₃ p i) := by
  rw [particleSystemDyname, ← plucker6Equiv_kleinQ, Equiv.apply_symm_apply]
  exact kleinQ_directionMoment (∑ i : Fin m, p i) (∑ i : Fin m, x i ⨯₃ p i)

/-- Symmetric central internal forces leave the Plücker particle-system dyname unchanged. -/
theorem particleSystemDyname_add_internal_eq {m : ℕ} (x p : Fin m → Vec3)
    (c : Fin m → Fin m → ℝ) (hsym : ∀ i j, c j i = c i j) :
    let pTot : Fin m → Vec3 := fun i => p i + ∑ j : Fin m, c i j • (x j - x i)
    particleSystemDyname x pTot = particleSystemDyname x p := by
  dsimp
  have hforce : ∑ i : Fin m, (p i + ∑ j : Fin m, c i j • (x j - x i)) = ∑ i : Fin m, p i := by
    have hskew : ∀ i j : Fin m, c j i • (x i - x j) = -(c i j • (x j - x i)) := by
      intro i j
      rw [hsym i j, ← smul_neg, neg_sub]
    rw [Finset.sum_add_distrib,
      internal_forces_sum_zero (fun i j => c i j • (x j - x i)) hskew, add_zero]
  have hmom : ∑ i : Fin m, x i ⨯₃ (p i + ∑ j : Fin m, c i j • (x j - x i)) =
      ∑ i : Fin m, x i ⨯₃ p i := by
    have hterm : ∀ i : Fin m, x i ⨯₃ (p i + ∑ j : Fin m, c i j • (x j - x i)) =
        x i ⨯₃ p i + ∑ j : Fin m, x i ⨯₃ (c i j • (x j - x i)) := by
      intro i
      rw [map_add, map_sum]
    simp_rw [hterm, Finset.sum_add_distrib,
      internal_central_cross_torque_zero x c hsym, add_zero]
  simp only [particleSystemDyname, hforce, hmom]

/-- **Bridge VIa Two-Force Dyname Splitting**: Any particle system with nonvanishing resultant
momentum/force `∑ p_i ≠ 0` splits identically into two finite Plücker force lines (`d₁ · m₁ = 0`,
`d₂ · m₂ = 0`, `d₁ + d₂ = ∑ p_i`, `m₁ + m₂ = ∑ x_i × p_i`). -/
theorem particleSystemDyname_two_force_splitting {m : ℕ} (x p : Fin m → Vec3)
    (hd : ∑ i : Fin m, p i ≠ 0) :
    ∃ d₁ m₁ d₂ m₂ : Vec3,
      d₁ ≠ 0 ∧ d₂ ≠ 0 ∧
      d₁ ⬝ᵥ m₁ = 0 ∧ d₂ ⬝ᵥ m₂ = 0 ∧
      d₁ + d₂ = ∑ i : Fin m, p i ∧ m₁ + m₂ = ∑ i : Fin m, x i ⨯₃ p i :=
  exists_two_finite_forces_for_dyname (∑ i : Fin m, p i) (∑ i : Fin m, x i ⨯₃ p i) (Or.inl hd)

end Sec4ConstraintsAndBridgeVIa

end InfoGeometry.Projective.GrassmannMechanicsBarycenterAndPotentials
