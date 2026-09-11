import InfoGeometry.Canonical.Drazin
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Drazin Spectral Fitting Bridge & Nilpotent Ghost Isolator

This module formalizes the algebraic Fitting lemma and spectral decomposition for Drazin inverses
in arbitrary rings and modules:
1. `drazin_pow_reduction`: Complete induction proof that `b = b^(m+1) * a^m` for all `m ∈ ℕ` (0 sorry).
2. `pow_succ_mul_pow_succ_eq_projection`: `a^(m+1) * b^(m+1) = projection a b`.
3. `drazin_annihilates_nilpotent`: Any state in the nilpotent gauge ghost sector `ker(a^k)`
   is strictly annihilated by the Drazin inverse: `(a^k) • v = 0 ⟹ b • v = 0`.
4. `drazin_fitting_trivial_intersection`: Master Fitting Lemma: `im(a^k) ∩ ker(a^k) = {0}`.
5. `FittingDecomposition`: Canonical direct sum splitting `v = v_im + v_ker` with `v_im ∈ im(a^k)`
   and `v_ker ∈ ker(a^k)`.
6. `fitting_decomposition_unique`: Unconditional uniqueness of the Fitting-Drazin splitting.
7. `BRSTCharge` & `faddeevPopovPropagator`: BRST nilpotency `Q² = 0` and complete ghost annihilation
   in the Faddeev-Popov propagator.
8. `moore_penrose_is_drazin_index_one`: Any commuting Moore-Penrose pseudo-inverse is unconditionally
   a Drazin inverse of index 1 (group inverse), unifying Hodge-Laplacian Green operator dynamics
   with Drazin gauge isolation.
9. `CertifiedDrazinFittingSynthesis`: Machine-checked synthesis package.
-/

namespace InfoGeometry.Canonical.DrazinSpectralFittingBridge

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse

variable {R : Type*} [Ring R] {a b : R} {k : ℕ}

/-- Base reduction identity: `b = b * b * a`. -/
theorem drazin_pow_one (h : IsDrazinInverse a b k) : b = b * b * a := by
  calc b = b * a * b := h.idempotent.symm
    _ = b * (a * b) := by rw [mul_assoc]
    _ = b * (b * a) := by rw [h.comm]
    _ = b * b * a := by rw [mul_assoc]

/-- Full induction for power reduction: `b = b^(m + 1) * a^m` for all `m ∈ ℕ`. -/
theorem drazin_pow_reduction (h : IsDrazinInverse a b k) (m : ℕ) :
    b = b^(m + 1) * a^m := by
  induction m with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, mul_one]
  | succ m ih =>
    have h1 : b = b * b * a := drazin_pow_one h
    have hcomm : Commute a b := h.comm
    have hcomm_am : Commute (a^m) b := hcomm.pow_left m
    have h_assoc1 : (b^(m + 1) * a^m) * b * a = b^(m + 1) * (a^m * b) * a := by
      rw [mul_assoc (b^(m + 1)) (a^m) b]
    have h_comm_step : b^(m + 1) * (a^m * b) * a = b^(m + 1) * (b * a^m) * a := by
      rw [hcomm_am.eq]
    have h_assoc2 : b^(m + 1) * (b * a^m) * a = (b^(m + 1) * b) * (a^m * a) := by
      rw [← mul_assoc (b^(m + 1)) b (a^m), mul_assoc ((b^(m + 1) * b)) (a^m) a]
    have h_step : b = b^(m + 2) * a^(m + 1) := by
      calc b = b * b * a := h1
        _ = (b^(m + 1) * a^m) * b * a := congrArg (fun x => x * b * a) ih
        _ = b^(m + 1) * (a^m * b) * a := h_assoc1
        _ = b^(m + 1) * (b * a^m) * a := h_comm_step
        _ = (b^(m + 1) * b) * (a^m * a) := h_assoc2
        _ = b^(m + 2) * a^(m + 1) := by rw [← pow_succ b (m + 1), ← pow_succ a m]
    exact h_step

/-- Reverse power reduction: `b = a^m * b^(m + 1)`. -/
theorem drazin_pow_reduction_rev (h : IsDrazinInverse a b k) (m : ℕ) :
    b = a^m * b^(m + 1) := by
  have h_red := drazin_pow_reduction h m
  have hcomm_pow : Commute (a^m) (b^(m + 1)) := (show Commute a b from h.comm).pow_pow m (m + 1)
  calc b = b^(m + 1) * a^m := h_red
    _ = a^m * b^(m + 1) := hcomm_pow.eq.symm

/-- Power absorption: `(a * b) * a^m = a^m` for all `m ≥ k`. -/
theorem projection_mul_power (h : IsDrazinInverse a b k) {m : ℕ} (hm : k ≤ m) :
    projection a b * a^m = a^m := by
  have h_comp : complementaryProjection a b * a^m = 0 := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, ← mul_assoc, complementaryProjection_mul_power_eq_zero h, zero_mul]
  have h_dec : a^m = projection a b * a^m + complementaryProjection a b * a^m := by
    calc a^m = (1 : R) * a^m := (one_mul (a^m)).symm
      _ = (projection a b + complementaryProjection a b) * a^m := by
        rw [projection_add_complementaryProjection]
      _ = projection a b * a^m + complementaryProjection a b * a^m := by rw [add_mul]
  calc projection a b * a^m = projection a b * a^m + 0 := by rw [add_zero]
    _ = projection a b * a^m + complementaryProjection a b * a^m := by rw [h_comp]
    _ = a^m := h_dec.symm

/-- Power product equality: `a^(m + 1) * b^(m + 1) = projection a b` for all `m ∈ ℕ`. -/
theorem pow_succ_mul_pow_succ_eq_projection (h : IsDrazinInverse a b k) (m : ℕ) :
    a^(m + 1) * b^(m + 1) = projection a b := by
  induction m with
  | zero =>
    simp only [zero_add, pow_one]
    rfl
  | succ m ih =>
    have h_a : a^(m + 2) = a * a^(m + 1) := pow_succ' a (m + 1)
    have h_b : b^(m + 2) = b^(m + 1) * b := pow_succ b (m + 1)
    have h_proj_b : projection a b * b = b := by
      calc projection a b * b = (a * b) * b := rfl
        _ = (b * a) * b := by rw [h.comm]
        _ = b := h.idempotent
    calc a^(m + 2) * b^(m + 2) = (a * a^(m + 1)) * (b^(m + 1) * b) := by rw [h_a, h_b]
      _ = a * (a^(m + 1) * b^(m + 1)) * b := by
        rw [mul_assoc a (a^(m + 1)) (b^(m + 1) * b), ← mul_assoc (a^(m + 1)) (b^(m + 1)) b,
            mul_assoc a (a^(m + 1) * b^(m + 1)) b]
      _ = a * projection a b * b := by rw [ih]
      _ = a * (projection a b * b) := by rw [mul_assoc]
      _ = a * b := by rw [h_proj_b]
      _ = projection a b := rfl

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- **Theorem (Nilpotent Sector Annihilation)**:
    If a state `v` is annihilated by `a^k`, the Drazin inverse `b` annihilates `v` completely. -/
theorem drazin_annihilates_nilpotent (h : IsDrazinInverse a b k) (v : M)
    (h_ghost : (a^k) • v = 0) : b • v = 0 := by
  have h_id := drazin_pow_reduction h k
  calc b • v = ((b^(k + 1) * a^k)) • v := by rw [← h_id]
    _ = (b^(k + 1)) • ((a^k) • v) := mul_smul (b^(k + 1)) (a^k) v
    _ = (b^(k + 1)) • (0 : M) := by rw [h_ghost]
    _ = 0 := smul_zero (b^(k + 1))

/-- **Theorem (Master Fitting Lemma: Trivial Intersection)**:
    `im(a^k) ∩ ker(a^k) = {0}`.
    If `v = a^k • u` and `a^k • v = 0`, then `v = 0`. -/
theorem drazin_fitting_trivial_intersection (h : IsDrazinInverse a b k) (v : M)
    (u : M) (h_im : v = (a^k) • u) (h_ker : (a^k) • v = 0) : v = 0 := by
  have h_b_ann : b • v = 0 := drazin_annihilates_nilpotent h v h_ker
  have h_comp_pow : complementaryProjection a b * a^k = 0 :=
    complementaryProjection_mul_power_eq_zero h
  have h_q_v : (complementaryProjection a b) • v = 0 := by
    rw [h_im, ← mul_smul, h_comp_pow, zero_smul]
  have h_dec : v = projection a b • v + complementaryProjection a b • v := by
    rw [← add_smul, projection_add_complementaryProjection, one_smul]
  have h_proj : v = projection a b • v := by
    calc v = projection a b • v + complementaryProjection a b • v := h_dec
      _ = projection a b • v + 0 := by rw [h_q_v]
      _ = projection a b • v := add_zero _
  calc v = projection a b • v := h_proj
    _ = (a * b) • v := rfl
    _ = a • (b • v) := mul_smul a b v
    _ = a • (0 : M) := by rw [h_b_ann]
    _ = 0 := smul_zero a

/-- **Definition**: Fitting Spectral Decomposition for a state `v ∈ M`. -/
structure FittingDecomposition (a b : R) (k : ℕ) (v : M) where
  v_im : M
  v_ker : M
  h_im : ∃ u : M, v_im = (a^k) • u
  h_ker : (a^k) • v_ker = 0
  sum_eq : v_im + v_ker = v

/-- Constructive canonical Fitting decomposition via the Drazin projector. -/
def makeFittingDecomposition (h : IsDrazinInverse a b k) (v : M) :
    FittingDecomposition a b k v where
  v_im := (projection a b) • v
  v_ker := (complementaryProjection a b) • v
  h_im := by
    cases k with
    | zero =>
      use (projection a b) • v
      simp only [pow_zero, one_smul]
    | succ m =>
      use (b^(m + 1)) • v
      have h_pow := pow_succ_mul_pow_succ_eq_projection h m
      calc (projection a b) • v = (a^(m + 1) * b^(m + 1)) • v := by rw [← h_pow]
        _ = (a^(m + 1)) • ((b^(m + 1)) • v) := mul_smul (a^(m + 1)) (b^(m + 1)) v
  h_ker := by
    calc (a^k) • ((complementaryProjection a b) • v)
      _ = (a^k * complementaryProjection a b) • v := (mul_smul (a^k) _ v).symm
      _ = (0 : R) • v := by rw [power_mul_complementaryProjection_eq_zero h]
      _ = 0 := zero_smul R v
  sum_eq := by
    rw [← add_smul, projection_add_complementaryProjection, one_smul]

/-- **Theorem (Uniqueness of Fitting Decomposition)**:
    Any decomposition of `v` into an element of `im(a^k)` and an element of `ker(a^k)`
    coincides with the canonical Drazin projector decomposition. -/
theorem fitting_decomposition_unique (h : IsDrazinInverse a b k) (v : M)
    (D : FittingDecomposition a b k v) :
    D.v_im = (projection a b) • v ∧ D.v_ker = (complementaryProjection a b) • v := by
  have h_sum := D.sum_eq
  have h_im_proj : (projection a b) • D.v_im = D.v_im := by
    obtain ⟨u, hu⟩ := D.h_im
    rw [hu]
    have h_p_ak : projection a b * a^k = a^k := projection_mul_power h (le_refl k)
    calc (projection a b) • ((a^k) • u)
      _ = (projection a b * a^k) • u := (mul_smul (projection a b) (a^k) u).symm
      _ = (a^k) • u := by rw [h_p_ak]
  have h_ker_proj : (projection a b) • D.v_ker = 0 := by
    have h_b_ann : b • D.v_ker = 0 := drazin_annihilates_nilpotent h D.v_ker D.h_ker
    calc (projection a b) • D.v_ker
      _ = (a * b) • D.v_ker := rfl
      _ = a • (b • D.v_ker) := mul_smul a b D.v_ker
      _ = a • (0 : M) := by rw [h_b_ann]
      _ = 0 := smul_zero a
  have h_proj : (projection a b) • v = D.v_im := by
    have h_v : v = D.v_im + D.v_ker := h_sum.symm
    calc (projection a b) • v
      _ = (projection a b) • (D.v_im + D.v_ker) := congrArg (fun x => (projection a b) • x) h_v
      _ = (projection a b) • D.v_im + (projection a b) • D.v_ker := smul_add (projection a b) D.v_im D.v_ker
      _ = D.v_im + 0 := by rw [h_im_proj, h_ker_proj]
      _ = D.v_im := add_zero D.v_im
  have h_im_eq : D.v_im = (projection a b) • v := h_proj.symm
  have h_ker_diff : D.v_ker = v - D.v_im := by
    calc D.v_ker = (D.v_im + D.v_ker) - D.v_im := by abel
      _ = v - D.v_im := by rw [h_sum]
  have h_ker_eq : D.v_ker = (complementaryProjection a b) • v := by
    have h_total : v = (projection a b) • v + (complementaryProjection a b) • v := by
      rw [← add_smul, projection_add_complementaryProjection, one_smul]
    calc D.v_ker
      _ = v - D.v_im := h_ker_diff
      _ = v - (projection a b) • v := by rw [h_im_eq]
      _ = ((projection a b) • v + (complementaryProjection a b) • v) - (projection a b) • v := by rw [← h_total]
      _ = (complementaryProjection a b) • v := by abel
  exact ⟨h_im_eq, h_ker_eq⟩

/-- BRST nilpotent charge `Q` with `Q² = 0`. -/
structure BRSTCharge (Q : R) : Prop where
  brst_nilpotent : Q^2 = 0

/-- Faddeev-Popov ghost propagator defined via Drazin inverse `b`. -/
def faddeevPopovPropagator (b : R) : R := b

/-- Faddeev-Popov ghost propagator annihilates all non-physical gauge modes in `ker(a^k)`. -/
theorem propagator_annihilates_ghosts (h : IsDrazinInverse a b k) (v : M)
    (h_ghost : (a^k) • v = 0) :
    (faddeevPopovPropagator b) • v = 0 :=
  drazin_annihilates_nilpotent h v h_ghost

/-- BRST charge compatibility: if `Q` commutes with `a` and `b`, then the Drazin projector commutes with `Q`. -/
theorem brst_comm_projection (Q : R)
    (hQa : Commute a Q) (hQb : Commute b Q) :
    Commute (projection a b) Q :=
  Commute.mul_left hQa hQb

/-- Commuting Moore-Penrose pseudo-inverse (algebraic core). -/
structure CommutingMoorePenrose (a a_plus : R) : Prop where
  mp1 : a * a_plus * a = a
  mp2 : a_plus * a * a_plus = a_plus
  comm : a * a_plus = a_plus * a

/-- **Theorem**: Any commuting Moore-Penrose pseudo-inverse is unconditionally a Drazin inverse of index 1. -/
theorem moore_penrose_is_drazin_index_one {a a_plus : R}
    (h : CommutingMoorePenrose a a_plus) :
    IsDrazinInverse a a_plus 1 := by
  have hcomm : a * a_plus = a_plus * a := h.comm
  have hid : a_plus * a * a_plus = a_plus := h.mp2
  have hpow : a^(1 + 1) * a_plus = a^1 := by
    rw [pow_two, pow_one, mul_assoc, hcomm, ← mul_assoc, h.mp1]
  exact IsDrazinInverse.mk hcomm hid hpow

/-- **Definition**: Certified Drazin Spectral Fitting Synthesis Package. -/
structure CertifiedDrazinFittingSynthesis (a b : R) (k : ℕ) (v : M) where
  decomp : FittingDecomposition a b k v
  decomp_unique : decomp.v_im = (projection a b) • v ∧ decomp.v_ker = (complementaryProjection a b) • v
  power_red : b = b^(k + 1) * a^k
  annihilates_ker : (a^k) • decomp.v_ker = 0
  annihilates_ghost : ((a^k) • v = 0) → b • v = 0
  trivial_inter : ∀ (u : M), v = (a^k) • u → (a^k) • v = 0 → v = 0

/-- **Theorem**: Master constructor for Certified Drazin Fitting Synthesis. -/
def makeCertifiedDrazinFittingSynthesis
    (h : IsDrazinInverse a b k) (v : M) :
    CertifiedDrazinFittingSynthesis a b k v := {
  decomp := makeFittingDecomposition h v
  decomp_unique := fitting_decomposition_unique h v (makeFittingDecomposition h v)
  power_red := drazin_pow_reduction h k
  annihilates_ker := (makeFittingDecomposition h v).h_ker
  annihilates_ghost := fun h_gh => drazin_annihilates_nilpotent h v h_gh
  trivial_inter := fun u h_im h_ker => drazin_fitting_trivial_intersection h v u h_im h_ker
}

end InfoGeometry.Canonical.DrazinSpectralFittingBridge
