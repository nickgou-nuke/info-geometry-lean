import Mathlib.Tactic
import InfoGeometry.Clifford.ConformalGeneratorLemmas55

/-!
# InfoGeometry.Clifford.ConformalLieAlgebra55Dilation

Dilation action lemmas for the $C\ell(5,5)$ conformal generators.
-/

namespace InfoGeometry.Clifford.ConformalLieAlgebra55Dilation

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Clifford.ConformalLieAlgebra55

theorem u5_sq : u5 * u5 = 0 := gammaHeadNullMinus_sq 4
theorem v5_sq : v5 * v5 = 0 := gammaHeadNullPlus_sq 4
theorem u5_v5_add_v5_u5 :
    u5 * v5 + v5 * u5 = 1 :=
  gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap 4

private theorem anti_symm
    {A : Type*} [Ring A]
    {x y : A}
    (h : x * y = - (y * x)) :
    y * x = - (x * y) := by
  rw [h]
  simp

private theorem half_commutator_acts_on_left
    {A : Type*} [Ring A] [Algebra ℝ A]
    (u v : A)
    (hu : u * u = 0)
    (hcar : u * v + v * u = 1) :
    ((1 / 2 : ℝ) • (u * v - v * u)) * u
        - u * ((1 / 2 : ℝ) • (u * v - v * u)) = u := by
  have huv : u * v * u = u := by
    have hsub : u * v = 1 - v * u := by
      exact eq_sub_of_add_eq hcar
    calc
      u * v * u = (1 - v * u) * u := by rw [hsub]
      _ = u - v * (u * u) := by noncomm_ring
      _ = u := by rw [hu]; noncomm_ring

  have hvuu : v * u * u = 0 := by
    calc
      v * u * u = v * (u * u) := by noncomm_ring
      _ = 0 := by rw [hu]; noncomm_ring

  have huuv : u * u * v = 0 := by
    calc
      u * u * v = (u * u) * v := by noncomm_ring
      _ = 0 := by rw [hu]; noncomm_ring

  rw [smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]

  have hcalc :
      (u * v - v * u) * u - u * (u * v - v * u) = u + u := by
    calc
      (u * v - v * u) * u - u * (u * v - v * u)
          =
        (u * v * u - v * u * u) - (u * u * v - u * v * u) := by
          noncomm_ring
      _ = (u - 0) - (0 - u) := by
          rw [huv, hvuu, huuv]
      _ = u + u := by
          noncomm_ring

  rw [hcalc]

  have htwo : u + u = (2 : ℝ) • u := by
    calc
      u + u = (1 : ℝ) • u + (1 : ℝ) • u := by simp
      _ = ((1 : ℝ) + (1 : ℝ)) • u := by rw [add_smul]
      _ = (2 : ℝ) • u := by norm_num

  rw [htwo, smul_smul]
  norm_num

private theorem half_commutator_commutes_of_anti
    {A : Type*} [Ring A] [Algebra ℝ A]
    (u v x : A)
    (hux : u * x = - (x * u))
    (hvx : v * x = - (x * v)) :
    ((1 / 2 : ℝ) • (u * v - v * u)) * x
        - x * ((1 / 2 : ℝ) • (u * v - v * u)) = 0 := by
  have huvx : u * v * x = x * u * v := by
    calc
      u * v * x = u * (v * x) := by noncomm_ring
      _ = u * (-(x * v)) := by rw [hvx]
      _ = - (u * x * v) := by noncomm_ring
      _ = - (-(x * u) * v) := by rw [hux]
      _ = x * u * v := by noncomm_ring

  have hvux : v * u * x = x * v * u := by
    calc
      v * u * x = v * (u * x) := by noncomm_ring
      _ = v * (-(x * u)) := by rw [hux]
      _ = - (v * x * u) := by noncomm_ring
      _ = - (-(x * v) * u) := by rw [hvx]
      _ = x * v * u := by noncomm_ring

  rw [smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]

  have hcalc :
      (u * v - v * u) * x - x * (u * v - v * u) = 0 := by
    calc
      (u * v - v * u) * x - x * (u * v - v * u)
          =
        (u * v * x - v * u * x) - (x * u * v - x * v * u) := by
          noncomm_ring
      _ = (x * u * v - x * v * u) - (x * u * v - x * v * u) := by
          rw [huvx, hvux]
      _ = 0 := by
          noncomm_ring

  rw [hcalc]
  exact smul_zero (1 / 2 : ℝ)

/-! ### Generic Null Pair Dilation Action -/

theorem null_pair_dilation_acts_on_u {A : Type*} [Ring A] [Algebra ℝ A] (u v D : A)
    (hu : u * u = 0) (huv : u * v + v * u = 1) (hD : D = (1/2:ℝ) • (u * v - v * u)) :
    D * u - u * D = u := by
  subst hD
  have h1 : u * v * u = u := by
    calc
      u * v * u = u * (v * u) := by noncomm_ring
      _ = u * (1 - u * v) := by rw [eq_sub_of_add_eq' huv]
      _ = u - u * u * v := by noncomm_ring
      _ = u - 0 * v := by rw [hu]
      _ = u := by noncomm_ring
  have h2 : v * u * u = 0 := by
    calc
      v * u * u = v * (u * u) := by noncomm_ring
      _ = v * 0 := by rw [hu]
      _ = 0 := by rw [mul_zero]
  have h3 : u * u * v = 0 := by
    calc
      u * u * v = (u * u) * v := by noncomm_ring
      _ = 0 * v := by rw [hu]
      _ = 0 := by rw [zero_mul]
  have hd_u : (u * v - v * u) * u = u := by
    calc
      (u * v - v * u) * u = u * v * u - v * u * u := by noncomm_ring
      _ = u - 0 := by rw [h1, h2]
      _ = u := by noncomm_ring
  have hu_d : u * (u * v - v * u) = -u := by
    calc
      u * (u * v - v * u) = u * u * v - u * v * u := by noncomm_ring
      _ = 0 - u := by rw [h3, h1]
      _ = -u := by noncomm_ring
  calc
    (1/2:ℝ) • (u * v - v * u) * u - u * ((1/2:ℝ) • (u * v - v * u))
        = (1/2:ℝ) • ((u * v - v * u) * u) - (1/2:ℝ) • (u * (u * v - v * u)) := by
          rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    _ = (1/2:ℝ) • u - (1/2:ℝ) • (-u) := by rw [hd_u, hu_d]
    _ = (1/2:ℝ) • u + (1/2:ℝ) • u := by rw [smul_neg, sub_neg_eq_add]
    _ = (1:ℝ) • u := by rw [← add_smul]; norm_num
    _ = u := one_smul ℝ u

theorem null_pair_dilation_acts_on_v {A : Type*} [Ring A] [Algebra ℝ A] (u v D : A)
    (hv : v * v = 0) (huv : u * v + v * u = 1) (hD : D = (1/2:ℝ) • (u * v - v * u)) :
    D * v - v * D = -v := by
  subst hD
  have h1 : v * u * v = v := by
    calc
      v * u * v = v * (u * v) := by noncomm_ring
      _ = v * (1 - v * u) := by rw [eq_sub_of_add_eq huv]
      _ = v - v * v * u := by noncomm_ring
      _ = v - 0 * u := by rw [hv]
      _ = v := by noncomm_ring
  have h2 : u * v * v = 0 := by
    calc
      u * v * v = u * (v * v) := by noncomm_ring
      _ = u * 0 := by rw [hv]
      _ = 0 := by rw [mul_zero]
  have h3 : v * v * u = 0 := by
    calc
      v * v * u = (v * v) * u := by noncomm_ring
      _ = 0 * u := by rw [hv]
      _ = 0 := by rw [zero_mul]
  have hd_v : (u * v - v * u) * v = -v := by
    calc
      (u * v - v * u) * v = u * v * v - v * u * v := by noncomm_ring
      _ = 0 - v := by rw [h2, h1]
      _ = -v := by noncomm_ring
  have hv_d : v * (u * v - v * u) = v := by
    calc
      v * (u * v - v * u) = v * u * v - v * v * u := by noncomm_ring
      _ = v - 0 := by rw [h1, h3]
      _ = v := by noncomm_ring
  calc
    (1/2:ℝ) • (u * v - v * u) * v - v * ((1/2:ℝ) • (u * v - v * u))
        = (1/2:ℝ) • ((u * v - v * u) * v) - (1/2:ℝ) • (v * (u * v - v * u)) := by
          rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    _ = (1/2:ℝ) • (-v) - (1/2:ℝ) • v := by rw [hd_v, hv_d]
    _ = -( (1/2:ℝ) • v + (1/2:ℝ) • v ) := by rw [smul_neg]; abel
    _ = -( (1:ℝ) • v ) := by rw [← add_smul]; norm_num
    _ = -v := by rw [one_smul]

theorem dilation_commutes_with_orthogonal_null {A : Type*} [Ring A] [Algebra ℝ A] (u v x D : A)
    (hx_u : x * u = - (u * x)) (hx_v : x * v = - (v * x))
    (hD : D = (1/2:ℝ) • (u * v - v * u)) :
    D * x - x * D = 0 := by
  subst hD
  have h_vx : v * x = - (x * v) := by
    calc
      v * x = - (- (v * x)) := by rw [neg_neg]
      _ = - (x * v) := by rw [← hx_v]
  have h_ux : u * x = - (x * u) := by
    calc
      u * x = - (- (u * x)) := by rw [neg_neg]
      _ = - (x * u) := by rw [← hx_u]
  have h_uv_x : (u * v) * x = x * (u * v) := by
    calc
      (u * v) * x = u * (v * x) := by noncomm_ring
      _ = u * (- (x * v)) := by rw [h_vx]
      _ = - (u * x * v) := by noncomm_ring
      _ = - ((- (x * u)) * v) := by rw [h_ux]
      _ = x * u * v := by noncomm_ring
      _ = x * (u * v) := by noncomm_ring
  have h_vu_x : (v * u) * x = x * (v * u) := by
    calc
      (v * u) * x = v * (u * x) := by noncomm_ring
      _ = v * (- (x * u)) := by rw [h_ux]
      _ = - (v * x * u) := by noncomm_ring
      _ = - ((- (x * v)) * u) := by rw [h_vx]
      _ = x * v * u := by noncomm_ring
      _ = x * (v * u) := by noncomm_ring
  have hd_x : (u * v - v * u) * x = x * (u * v - v * u) := by
    calc
      (u * v - v * u) * x = u * v * x - v * u * x := by noncomm_ring
      _ = x * (u * v) - x * (v * u) := by rw [h_uv_x, h_vu_x]
      _ = x * (u * v - v * u) := by noncomm_ring
  calc
    (1/2:ℝ) • (u * v - v * u) * x - x * ((1/2:ℝ) • (u * v - v * u))
        = (1/2:ℝ) • ((u * v - v * u) * x) - (1/2:ℝ) • (x * (u * v - v * u)) := by
          rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    _ = (1/2:ℝ) • (x * (u * v - v * u)) - (1/2:ℝ) • (x * (u * v - v * u)) := by rw [hd_x]
    _ = 0 := sub_self _

theorem u4_sq : u4 * u4 = 0 := by
  dsimp [u4]
  rw [gammaTail, CliffordAlgebra.ι_sq_scalar, quad_tailLift, headNullMinus_isotropic]
  simp

theorem v4_sq : v4 * v4 = 0 := by
  dsimp [v4]
  rw [gammaTail, CliffordAlgebra.ι_sq_scalar, quad_tailLift, headNullPlus_isotropic]
  simp

theorem u4_v4_add_v4_u4 :
    u4 * v4 + v4 * u4 = 1 := by
  dsimp [u4, v4]
  have h :=
    CliffordAlgebra.ι_mul_ι_add_swap
      (Q := Quad 5)
      (tailLift 4 (headNullMinus 3))
      (tailLift 4 (headNullPlus 3))
  have h_polar :
      QuadraticMap.polar (Quad 5)
          (tailLift 4 (headNullMinus 3))
          (tailLift 4 (headNullPlus 3)) = 1 := by
    rw [QuadraticMap.polar, quad_tailLift, quad_tailLift]
    have h_sum :
        tailLift 4 (headNullMinus 3) + tailLift 4 (headNullPlus 3)
          =
        tailLift 4 (headNullMinus 3 + headNullPlus 3) := by
      simp [tailLift, headNullMinus, headNullPlus, headPair]
    rw [h_sum, quad_tailLift]
    exact polar_headNullMinus_headNullPlus 3
  rw [h_polar] at h
  exact h

/-! ### Application to Cl(5,5) generators -/

theorem adD5_u5 : D5 * u5 - u5 * D5 = u5 := by
  dsimp [D5]
  exact half_commutator_acts_on_left u5 v5 u5_sq u5_v5_add_v5_u5

theorem adD4_u5 : D4 * u5 - u5 * D4 = 0 := by
  dsimp [D4]
  exact
    half_commutator_commutes_of_anti
      u4 v4 u5
      (anti_symm u5_u4_anti)
      (anti_symm u5_v4_anti)

theorem adD : D * u5 - u5 * D = u5 := by
  dsimp [D]
  calc
    (D5 + D4) * u5 - u5 * (D5 + D4)
        =
      (D5 * u5 - u5 * D5) + (D4 * u5 - u5 * D4) := by
        noncomm_ring
    _ = u5 + 0 := by
      rw [adD5_u5, adD4_u5]
    _ = u5 := by
      simp

theorem adD4_u4 : D4 * u4 - u4 * D4 = u4 := by
  dsimp [D4]
  exact half_commutator_acts_on_left u4 v4 u4_sq u4_v4_add_v4_u4

theorem adD5_u4 : D5 * u4 - u4 * D5 = 0 := by
  dsimp [D5]
  exact
    half_commutator_commutes_of_anti
      u5 v5 u4
      u5_u4_anti
      v5_u4_anti

theorem adD_u4 : D * u4 - u4 * D = u4 := by
  dsimp [D]
  calc
    (D5 + D4) * u4 - u4 * (D5 + D4)
        =
      (D5 * u4 - u4 * D5) + (D4 * u4 - u4 * D4) := by
        noncomm_ring
    _ = 0 + u4 := by
      rw [adD5_u4, adD4_u4]
    _ = u4 := by
      simp

theorem adD5_v5 : D5 * v5 - v5 * D5 = -v5 := 
  null_pair_dilation_acts_on_v u5 v5 D5 v5_sq u5_v5_add_v5_u5 rfl

theorem adD4_v4 : D4 * v4 - v4 * D4 = -v4 := 
  null_pair_dilation_acts_on_v u4 v4 D4 v4_sq u4_v4_add_v4_u4 rfl

lemma h_u4_u5 : u4 * u5 = - (u5 * u4) := by
  calc
    u4 * u5 = - (- (u4 * u5)) := by rw [neg_neg]
    _ = - (u5 * u4) := by rw [← u5_u4_anti]

lemma h_v4_u5 : v4 * u5 = - (u5 * v4) := by
  calc
    v4 * u5 = - (- (v4 * u5)) := by rw [neg_neg]
    _ = - (u5 * v4) := by rw [← u5_v4_anti]

lemma h_u4_v5 : u4 * v5 = - (v5 * u4) := by
  calc
    u4 * v5 = - (- (u4 * v5)) := by rw [neg_neg]
    _ = - (v5 * u4) := by rw [← v5_u4_anti]

lemma h_v4_v5 : v4 * v5 = - (v5 * v4) := by
  calc
    v4 * v5 = - (- (v4 * v5)) := by rw [neg_neg]
    _ = - (v5 * v4) := by rw [← v5_v4_anti]

theorem adD5_v4 : D5 * v4 - v4 * D5 = 0 :=
  dilation_commutes_with_orthogonal_null u5 v5 v4 D5
    h_v4_u5 h_v4_v5 rfl

theorem adD4_v5 : D4 * v5 - v5 * D4 = 0 :=
  dilation_commutes_with_orthogonal_null u4 v4 v5 D4
    v5_u4_anti v5_v4_anti rfl

theorem adD_v5 : D * v5 - v5 * D = -v5 := by
  calc
    (D5 + D4) * v5 - v5 * (D5 + D4) = (D5 * v5 - v5 * D5) + (D4 * v5 - v5 * D4) := by noncomm_ring
    _ = -v5 + 0 := by rw [adD5_v5, adD4_v5]
    _ = -v5 := by rw [add_zero]

theorem adD_v4 : D * v4 - v4 * D = -v4 := by
  calc
    (D5 + D4) * v4 - v4 * (D5 + D4) = (D5 * v4 - v4 * D5) + (D4 * v4 - v4 * D4) := by noncomm_ring
    _ = 0 + -v4 := by rw [adD5_v4, adD4_v4]
    _ = -v4 := by rw [zero_add]

end InfoGeometry.Clifford.ConformalLieAlgebra55Dilation

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `u5_sq` : u5 square is zero.
- `v5_sq` : v5 square is zero.
- `u5_v5_add_v5_u5` : u5/v5 Canonical Anticommutation Relation.
- `u4_sq` : u4 square is zero.
- `v4_sq` : v4 square is zero.
- `u4_v4_add_v4_u4` : u4/v4 Canonical Anticommutation Relation.
- `adD5_u5`, `adD5_v5`, `adD4_u4`, `adD4_v4`, `adD5_u4`, `adD5_v4`, `adD4_u5`, `adD4_v5`, `adD`, `adD_v5`, `adD_u4`, `adD_v4` : Full set of conformal dilation action theorems on the null generators.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- None.

#### BUCKET 3: OPEN CLOSURE DEBT
- None.
-/
