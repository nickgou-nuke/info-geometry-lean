import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Bregman Divergence

Core Bregman divergence definitions and theorems.

## Main results
- `bregmanDiv`
- `bregmanThreePoint`
- `bregmanThreePoint_sub`
- `bregmanPythagoreanIneq_of_crossTerm_nonneg`

-/

namespace InfoGeometry

-- Bregman divergence for a convex function F
noncomputable def bregmanDiv (F : ℝ → ℝ) (x y : ℝ) : ℝ :=
  F x - F y - deriv F y * (x - y)

/-- Bregman divergence vanishes on the diagonal. -/
lemma bregmanDiv_self (F : ℝ → ℝ) (x : ℝ) :
  bregmanDiv F x x = 0 := by
  simp [bregmanDiv]

/-- If the two arguments coincide, the Bregman divergence is zero. -/
lemma bregmanDiv_eq_zero_of_eq (F : ℝ → ℝ) (x y : ℝ) (hxy : x = y) :
  bregmanDiv F x y = 0 := by
  simpa [hxy] using bregmanDiv_self F y

/-- Three-point identity for Bregman divergence. -/
lemma bregmanThreePoint (F : ℝ → ℝ) (x y z : ℝ) :
  bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z + (deriv F y - deriv F z) * (x - y) :=
by
  simp [bregmanDiv]
  ring

/-- Rearranged three-point identity isolating the cross term. -/
lemma bregmanThreePoint_sub (F : ℝ → ℝ) (x y z : ℝ) :
  bregmanDiv F x z - bregmanDiv F x y - bregmanDiv F y z
    = (deriv F y - deriv F z) * (x - y) := by
  calc
    bregmanDiv F x z - bregmanDiv F x y - bregmanDiv F y z
        = (bregmanDiv F x y + bregmanDiv F y z + (deriv F y - deriv F z) * (x - y))
            - bregmanDiv F x y - bregmanDiv F y z := by
              rw [bregmanThreePoint F x y z]
    _ = (deriv F y - deriv F z) * (x - y) := by ring

/-- If the cross term vanishes, the three-point identity collapses to equality. -/
lemma bregmanThreePoint_eq_of_crossTerm_eq_zero
    (F : ℝ → ℝ) (x y z : ℝ)
    (hcross : (deriv F y - deriv F z) * (x - y) = 0) :
    bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z := by
  calc
    bregmanDiv F x z
        = bregmanDiv F x y + bregmanDiv F y z + (deriv F y - deriv F z) * (x - y) :=
          bregmanThreePoint F x y z
    _ = bregmanDiv F x y + bregmanDiv F y z := by simp [hcross]

/--
Three-point identity with matching derivatives at `y` and `z`.
This is a theorem-level specialization obtained by proving the cross term is zero.
-/
theorem bregmanThreePoint_eq_of_deriv_eq
    (F : ℝ → ℝ) (x y z : ℝ)
    (hderiv : deriv F y = deriv F z) :
    bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z := by
  apply bregmanThreePoint_eq_of_crossTerm_eq_zero
  calc
    (deriv F y - deriv F z) * (x - y)
        = (deriv F y - deriv F y) * (x - y) := by rw [hderiv]
    _ = 0 := by ring

/-- Pythagorean equality when the Bregman cross term is exactly zero. -/
theorem bregmanPythagoreanEq_of_crossTerm_eq_zero
    (F : ℝ → ℝ) (x y z : ℝ)
    (hcross : (deriv F y - deriv F z) * (x - y) = 0) :
    bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z :=
  bregmanThreePoint_eq_of_crossTerm_eq_zero F x y z hcross

/-- Pythagorean equality under derivative matching at `y` and `z`. -/
theorem bregmanPythagoreanEq_of_deriv_eq
    (F : ℝ → ℝ) (x y z : ℝ)
    (hderiv : deriv F y = deriv F z) :
    bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z :=
  bregmanThreePoint_eq_of_deriv_eq F x y z hderiv

/-- Rearranged three-point defect vanishes when derivatives match at `y` and `z`. -/
theorem bregmanThreePoint_sub_eq_zero_of_deriv_eq
    (F : ℝ → ℝ) (x y z : ℝ)
    (hderiv : deriv F y = deriv F z) :
    bregmanDiv F x z - bregmanDiv F x y - bregmanDiv F y z = 0 := by
  calc
    bregmanDiv F x z - bregmanDiv F x y - bregmanDiv F y z
        = (deriv F y - deriv F z) * (x - y) := bregmanThreePoint_sub F x y z
    _ = (deriv F y - deriv F y) * (x - y) := by rw [hderiv]
    _ = 0 := by ring

/-- Pythagorean inequality as a corollary of derivative matching. -/
theorem bregmanPythagoreanIneq_of_deriv_eq
    (F : ℝ → ℝ) (x y z : ℝ)
    (hderiv : deriv F y = deriv F z) :
    bregmanDiv F x z ≥ bregmanDiv F x y + bregmanDiv F y z := by
  exact (bregmanPythagoreanEq_of_deriv_eq F x y z hderiv).ge

/-- Three-point equality specialization when `x = y`. -/
theorem bregmanThreePoint_eq_of_eq_left
    (F : ℝ → ℝ) (x y z : ℝ)
    (hxy : x = y) :
    bregmanDiv F x z = bregmanDiv F y z := by
  simp [hxy]

/-- Three-point equality specialization when `y = z`. -/
theorem bregmanThreePoint_eq_of_eq_mid_right
    (F : ℝ → ℝ) (x y z : ℝ)
    (hyz : y = z) :
    bregmanDiv F x z = bregmanDiv F x y := by
  have hcross : (deriv F y - deriv F z) * (x - y) = 0 := by
    rw [hyz]
    ring
  have hEq : bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z :=
    bregmanThreePoint_eq_of_crossTerm_eq_zero F x y z hcross
  have hyz0 : bregmanDiv F y z = 0 := bregmanDiv_eq_zero_of_eq F y z hyz
  calc
    bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z := hEq
    _ = bregmanDiv F x y + 0 := by rw [hyz0]
    _ = bregmanDiv F x y := by ring

/-- Pythagorean inequality specialization when `x = y`. -/
theorem bregmanPythagoreanIneq_of_eq_left
    (F : ℝ → ℝ) (x y z : ℝ)
    (hxy : x = y) :
    bregmanDiv F x z ≥ bregmanDiv F x y + bregmanDiv F y z := by
  have hEq : bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z := by
    have hcross : (deriv F y - deriv F z) * (x - y) = 0 := by
      rw [hxy]
      ring
    exact bregmanThreePoint_eq_of_crossTerm_eq_zero F x y z hcross
  exact hEq.ge

/-- Pythagorean inequality specialization when `y = z`. -/
theorem bregmanPythagoreanIneq_of_eq_mid_right
    (F : ℝ → ℝ) (x y z : ℝ)
    (hyz : y = z) :
    bregmanDiv F x z ≥ bregmanDiv F x y + bregmanDiv F y z := by
  have hcross : (deriv F y - deriv F z) * (x - y) = 0 := by
    rw [hyz]
    ring
  exact (bregmanThreePoint_eq_of_crossTerm_eq_zero F x y z hcross).ge

/-- Three-point identity specialized to `x = z`. -/
theorem bregmanThreePoint_eq_zero_sum_of_eq_right
    (F : ℝ → ℝ) (x y z : ℝ)
    (hxz : x = z) :
    0 = bregmanDiv F x y + bregmanDiv F y z + (deriv F y - deriv F z) * (x - y) := by
  calc
    0 = bregmanDiv F x z := by simpa [hxz] using (bregmanDiv_self F x).symm
    _ = bregmanDiv F x y + bregmanDiv F y z + (deriv F y - deriv F z) * (x - y) :=
      bregmanThreePoint F x y z

/-- Rearranged three-point defect specialized to `x = z`. -/
theorem bregmanThreePoint_sub_of_eq_right
    (F : ℝ → ℝ) (x y z : ℝ)
    (hxz : x = z) :
    - bregmanDiv F x y - bregmanDiv F y z = (deriv F y - deriv F z) * (x - y) := by
  calc
    - bregmanDiv F x y - bregmanDiv F y z
        = bregmanDiv F x z - bregmanDiv F x y - bregmanDiv F y z := by
          rw [bregmanDiv_eq_zero_of_eq F x z hxz]
          ring
    _ = (deriv F y - deriv F z) * (x - y) := bregmanThreePoint_sub F x y z

/--
If `x = z` and the derivatives match at `y` and `z`,
the two Bregman terms cancel exactly.
-/
theorem bregmanDiv_add_eq_zero_of_eq_right_of_deriv_eq
    (F : ℝ → ℝ) (x y z : ℝ)
    (hxz : x = z)
    (hderiv : deriv F y = deriv F z) :
    bregmanDiv F x y + bregmanDiv F y z = 0 := by
  have hsum :
      0 = bregmanDiv F x y + bregmanDiv F y z + (deriv F y - deriv F z) * (x - y) :=
    bregmanThreePoint_eq_zero_sum_of_eq_right F x y z hxz
  have hcross0 : (deriv F y - deriv F z) * (x - y) = 0 := by
    rw [hderiv]
    ring
  calc
    bregmanDiv F x y + bregmanDiv F y z
        = bregmanDiv F x y + bregmanDiv F y z + (deriv F y - deriv F z) * (x - y) := by
          rw [hcross0]
          ring
    _ = 0 := by simpa using hsum.symm

/-- Under `x = z` and derivative matching at `y,z`, the two divergences are negatives. -/
theorem bregmanDiv_eq_neg_of_eq_right_of_deriv_eq
    (F : ℝ → ℝ) (x y z : ℝ)
    (hxz : x = z)
    (hderiv : deriv F y = deriv F z) :
    bregmanDiv F x y = - bregmanDiv F y z := by
  have hsum : bregmanDiv F x y + bregmanDiv F y z = 0 :=
    bregmanDiv_add_eq_zero_of_eq_right_of_deriv_eq F x y z hxz hderiv
  calc
    bregmanDiv F x y = bregmanDiv F x y + bregmanDiv F y z - bregmanDiv F y z := by ring
    _ = 0 - bregmanDiv F y z := by rw [hsum]
    _ = - bregmanDiv F y z := by ring

/-- If derivatives match at `y` and `x`, then `D_F(x,y) = -D_F(y,x)`. -/
theorem bregmanDiv_eq_neg_swap_of_deriv_eq
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x) :
    bregmanDiv F x y = - bregmanDiv F y x := by
  simpa using
    (bregmanDiv_eq_neg_of_eq_right_of_deriv_eq F x y x rfl hderiv)

/-- If derivatives match at `x,y`, the two directed divergences sum to zero. -/
theorem bregmanDiv_add_swap_eq_zero_of_deriv_eq
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x) :
    bregmanDiv F x y + bregmanDiv F y x = 0 := by
  have hneg : bregmanDiv F x y = - bregmanDiv F y x :=
    bregmanDiv_eq_neg_swap_of_deriv_eq F x y hderiv
  calc
    bregmanDiv F x y + bregmanDiv F y x = (- bregmanDiv F y x) + bregmanDiv F y x := by rw [hneg]
    _ = 0 := by ring

/-- Under derivative matching at `x,y`, one directed divergence vanishes iff the swapped one vanishes. -/
theorem bregmanDiv_eq_zero_iff_swap_eq_zero_of_deriv_eq
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x) :
    bregmanDiv F x y = 0 ↔ bregmanDiv F y x = 0 := by
  have hneg : bregmanDiv F x y = - bregmanDiv F y x :=
    bregmanDiv_eq_neg_swap_of_deriv_eq F x y hderiv
  constructor
  · intro hxy
    have : - bregmanDiv F y x = 0 := by simpa [hneg] using hxy
    linarith
  · intro hyx
    calc
      bregmanDiv F x y = - bregmanDiv F y x := hneg
      _ = 0 := by simp [hyx]

/-- If derivatives match at `x,y`, swapped divergence is the negative of the original. -/
theorem bregmanDiv_swap_eq_neg_of_deriv_eq
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x) :
    bregmanDiv F y x = - bregmanDiv F x y := by
  have hneg : bregmanDiv F x y = - bregmanDiv F y x :=
    bregmanDiv_eq_neg_swap_of_deriv_eq F x y hderiv
  linarith [hneg]

/-- Sign duality under derivative matching: `D(x,y) ≥ 0` iff `D(y,x) ≤ 0`. -/
theorem bregmanDiv_nonneg_iff_swap_nonpos_of_deriv_eq
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x) :
    0 ≤ bregmanDiv F x y ↔ bregmanDiv F y x ≤ 0 := by
  have hneg : bregmanDiv F x y = - bregmanDiv F y x :=
    bregmanDiv_eq_neg_swap_of_deriv_eq F x y hderiv
  constructor
  · intro hxy
    linarith [hneg, hxy]
  · intro hyx
    linarith [hneg, hyx]

/-- Dual sign form under derivative matching: `D(x,y) ≤ 0` iff `D(y,x) ≥ 0`. -/
theorem bregmanDiv_nonpos_iff_swap_nonneg_of_deriv_eq
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x) :
    bregmanDiv F x y ≤ 0 ↔ 0 ≤ bregmanDiv F y x := by
  have hneg : bregmanDiv F x y = - bregmanDiv F y x :=
    bregmanDiv_eq_neg_swap_of_deriv_eq F x y hderiv
  constructor
  · intro hxy
    linarith [hneg, hxy]
  · intro hyx
    linarith [hneg, hyx]

/-- Under derivative matching at `x,y`, swapped directed divergences have equal absolute value. -/
theorem abs_bregmanDiv_eq_abs_swap_of_deriv_eq
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x) :
    |bregmanDiv F x y| = |bregmanDiv F y x| := by
  have hneg : bregmanDiv F x y = - bregmanDiv F y x :=
    bregmanDiv_eq_neg_swap_of_deriv_eq F x y hderiv
  calc
    |bregmanDiv F x y| = |- bregmanDiv F y x| := by rw [hneg]
    _ = |bregmanDiv F y x| := by simp

/-- Under derivative matching at `x,y`, the squared directed divergences are equal. -/
theorem bregmanDiv_sq_eq_swap_sq_of_deriv_eq
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x) :
    (bregmanDiv F x y) ^ 2 = (bregmanDiv F y x) ^ 2 := by
  have hneg : bregmanDiv F x y = - bregmanDiv F y x :=
    bregmanDiv_eq_neg_swap_of_deriv_eq F x y hderiv
  calc
    (bregmanDiv F x y) ^ 2 = (- bregmanDiv F y x) ^ 2 := by rw [hneg]
    _ = (bregmanDiv F y x) ^ 2 := by ring

/--
Under derivative matching, if both directed divergences are nonnegative,
then both are forced to vanish.
-/
theorem bregmanDiv_eq_zero_and_swap_eq_zero_of_deriv_eq_of_nonneg
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x)
    (hxy_nonneg : 0 ≤ bregmanDiv F x y)
    (hyx_nonneg : 0 ≤ bregmanDiv F y x) :
    bregmanDiv F x y = 0 ∧ bregmanDiv F y x = 0 := by
  have hyx_nonpos : bregmanDiv F y x ≤ 0 :=
    (bregmanDiv_nonneg_iff_swap_nonpos_of_deriv_eq F x y hderiv).1 hxy_nonneg
  have hxy_nonpos : bregmanDiv F x y ≤ 0 :=
    (bregmanDiv_nonpos_iff_swap_nonneg_of_deriv_eq F x y hderiv).2 hyx_nonneg
  have hxy_zero : bregmanDiv F x y = 0 := le_antisymm hxy_nonpos hxy_nonneg
  have hyx_zero : bregmanDiv F y x = 0 := le_antisymm hyx_nonpos hyx_nonneg
  exact ⟨hxy_zero, hyx_zero⟩

/-- Under derivative matching and nonnegativity of both directed terms,
`D_F(x,y)` vanishes. -/
theorem bregmanDiv_eq_zero_of_deriv_eq_of_nonneg_of_swap_nonneg
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x)
    (hxy_nonneg : 0 ≤ bregmanDiv F x y)
    (hyx_nonneg : 0 ≤ bregmanDiv F y x) :
    bregmanDiv F x y = 0 := by
  exact (bregmanDiv_eq_zero_and_swap_eq_zero_of_deriv_eq_of_nonneg
    F x y hderiv hxy_nonneg hyx_nonneg).1

/-- Under derivative matching and nonnegativity of both directed terms,
`D_F(y,x)` vanishes. -/
theorem bregmanDiv_swap_eq_zero_of_deriv_eq_of_nonneg_of_swap_nonneg
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x)
    (hxy_nonneg : 0 ≤ bregmanDiv F x y)
    (hyx_nonneg : 0 ≤ bregmanDiv F y x) :
    bregmanDiv F y x = 0 := by
  exact (bregmanDiv_eq_zero_and_swap_eq_zero_of_deriv_eq_of_nonneg
    F x y hderiv hxy_nonneg hyx_nonneg).2

/-- Under derivative matching and nonnegativity of both directed terms,
the sum of directed divergences is zero. -/
theorem bregmanDiv_add_swap_eq_zero_of_deriv_eq_of_nonneg
    (F : ℝ → ℝ) (x y : ℝ)
    (hderiv : deriv F y = deriv F x)
    (hxy_nonneg : 0 ≤ bregmanDiv F x y)
    (hyx_nonneg : 0 ≤ bregmanDiv F y x) :
    bregmanDiv F x y + bregmanDiv F y x = 0 := by
  have hpair := bregmanDiv_eq_zero_and_swap_eq_zero_of_deriv_eq_of_nonneg
    F x y hderiv hxy_nonneg hyx_nonneg
  calc
    bregmanDiv F x y + bregmanDiv F y x = 0 + 0 := by rw [hpair.1, hpair.2]
    _ = 0 := by ring

/-- Conditional Bregman Pythagorean inequality from a nonnegative cross term.
Deriving the cross-term sign from convexity/projection assumptions is separate. -/
lemma bregmanPythagoreanIneq_of_crossTerm_nonneg
    (F : ℝ → ℝ) (x y z : ℝ)
    (hproj : 0 ≤ (deriv F y - deriv F z) * (x - y)) :
    bregmanDiv F x z ≥ bregmanDiv F x y + bregmanDiv F y z :=
by
  calc
    bregmanDiv F x z
        = bregmanDiv F x y + bregmanDiv F y z + (deriv F y - deriv F z) * (x - y) :=
          bregmanThreePoint F x y z
    _ ≥ bregmanDiv F x y + bregmanDiv F y z := by linarith [hproj]

/-- Backward-compatible alias for
`bregmanPythagoreanIneq_of_crossTerm_nonneg`. -/
lemma bregmanPythagoreanIneq
    (F : ℝ → ℝ) (x y z : ℝ)
    (hproj : 0 ≤ (deriv F y - deriv F z) * (x - y)) :
    bregmanDiv F x z ≥ bregmanDiv F x y + bregmanDiv F y z :=
  bregmanPythagoreanIneq_of_crossTerm_nonneg F x y z hproj

/-! ## Linear-symmetry invariance (vector-space form) -/

/-- Pairing readout from the gradient-linear map. -/
def pairing
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (nablaΦ : V → V →ₗ[ℝ] ℝ)
    (y v : V) : ℝ :=
  nablaΦ y v

/-- Bregman divergence from a potential and gradient pairing surface. -/
def bregmanDivergence
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Φ : V → ℝ)
    (nablaΦ : V → V →ₗ[ℝ] ℝ)
    (x y : V) : ℝ :=
  Φ x - Φ y - pairing nablaΦ y (x - y)

/--
Dual-pairing invariance under the coadjoint action induced by a linear
equivalence.

If `T` is the primal action and the dual action is pullback by `T.symm`, then
`⟨η ∘ T⁻¹, T x⟩ = ⟨η, x⟩`.
-/
theorem pairing_dualMap_linearEquiv
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V ≃ₗ[ℝ] V)
    (η : V →ₗ[ℝ] ℝ)
    (x : V) :
    (η.comp (T.symm : V →ₗ[ℝ] V)) (T x) = η x := by
  change η (T.symm (T x)) = η x
  simp

/--
Fenchel objective invariance under a linear primal/coadjoint pair.
-/
theorem fenchelObjective_invariant_linearEquiv
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Φ : V → ℝ)
    (T : V ≃ₗ[ℝ] V)
    (η : V →ₗ[ℝ] ℝ)
    (hΦ : ∀ x : V, Φ (T x) = Φ x)
    (x : V) :
    (η.comp (T.symm : V →ₗ[ℝ] V)) (T x) - Φ (T x)
      =
    η x - Φ x := by
  rw [hΦ x, pairing_dualMap_linearEquiv T η x]

/--
Affine-coadjoint Fenchel objective invariance.
-/
theorem fenchelObjective_invariant_affineCoadjoint
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Φ : V → ℝ)
    (T : V ≃ₗ[ℝ] V)
    (η θ : V →ₗ[ℝ] ℝ)
    (hΦ : ∀ x : V, Φ (T x) = Φ x)
    (x : V) :
    ((η.comp (T.symm : V →ₗ[ℝ] V) + θ) (T x))
      - (Φ (T x) + θ (T x))
      =
    η x - Φ x := by
  rw [LinearMap.add_apply, hΦ x, pairing_dualMap_linearEquiv T η x]
  ring

/--
Affine-coadjoint invariance of the Bregman divergence.
-/
theorem bregman_invariant_affineCoadjoint
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Φ : V → ℝ)
    (nablaΦ : V → V →ₗ[ℝ] ℝ)
    (T : V ≃ₗ[ℝ] V)
    (θ : V →ₗ[ℝ] ℝ)
    (hΦ : ∀ x : V, Φ (T x) = Φ x + θ (T x))
    (hgrad :
      ∀ y : V,
        nablaΦ (T y) =
          (nablaΦ y).comp (T.symm : V →ₗ[ℝ] V) + θ)
    (x y : V) :
    bregmanDivergence Φ nablaΦ (T x) (T y)
      =
    bregmanDivergence Φ nablaΦ x y := by
  unfold bregmanDivergence pairing
  have harg : T x - T y = T (x - y) := by
    simpa using (map_sub T x y).symm
  have hpair :
      ((nablaΦ y).comp (T.symm : V →ₗ[ℝ] V) + θ) (T (x - y))
        =
      nablaΦ y (x - y) + θ (T x) - θ (T y) := by
    rw [LinearMap.add_apply]
    have hdual :
        ((nablaΦ y).comp (T.symm : V →ₗ[ℝ] V)) (T (x - y))
          =
        nablaΦ y (x - y) :=
      pairing_dualMap_linearEquiv T (nablaΦ y) (x - y)
    have htheta :
        θ (T (x - y)) = θ (T x) - θ (T y) := by
      rw [map_sub T x y, map_sub θ (T x) (T y)]
    rw [hdual, htheta]
    ring
  rw [hΦ x, hΦ y, hgrad y, harg, hpair]
  ring

/--
Bregman divergence is invariant under a linear symmetry that preserves
the potential and the gradient pairing.

No strict convexity is needed for this lemma.
-/
theorem bregman_invariant_of_linear_symmetry
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Φ : V → ℝ)
    (nablaΦ : V → V →ₗ[ℝ] ℝ)
    (T : V →ₗ[ℝ] V)
    (hΦ : ∀ x : V, Φ (T x) = Φ x)
    (hPair : ∀ x y : V, nablaΦ (T x) (T y) = nablaΦ x y)
    (x y : V) :
    bregmanDivergence Φ nablaΦ (T x) (T y) =
      bregmanDivergence Φ nablaΦ x y := by
  unfold bregmanDivergence pairing
  have hsub : T (x - y) = T x - T y := by
    exact map_sub T x y
  rw [← hsub]
  simp [hΦ, hPair]

end InfoGeometry
