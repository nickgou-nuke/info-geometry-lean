import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.BostConnesSuperalgebra
import InfoGeometry.Canonical.BostConnesSuperalgebraConstructive
import InfoGeometry.Canonical.KMSTraceColimit

/-!
# Cantor Finite Diagonal Tracial State

This module formalizes the canonical normalized tracial state on the diagonal UHF algebra
stages.  We define the normalized trace on `DiagAlg n`, prove its compatibility with the
inductive morphisms, and establish the finite cylinder weights and positivity statements.

The file does not assert a nontrivial modular flow or a general KMS theorem: the diagonal
finite state is tracial, so its finite modular dynamics are trivial.  Thermodynamic time and
nontrivial relative modular evolution belong to downstream state-dependent owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorKMSState

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.BostConnesSuperalgebra
open InfoGeometry.Canonical.BostConnesSuperalgebraConstructive

/-- Explicit equivalence between `BitWord (n + 1)` and `BitWord n × Bool`. -/
def bitWordEquiv (n : ℕ) : BitWord (n + 1) ≃ BitWord n × Bool where
  toFun w := (prefixSucc n w, w ⟨n, Nat.lt_succ_self n⟩)
  invFun p i := if h : i.1 < n then p.1 ⟨i.1, h⟩ else p.2
  left_inv w := by
    ext i
    dsimp [prefixSucc]
    split_ifs with h
    · rfl
    · have hi : i.1 = n := by
        have h1 : i.1 < n + 1 := i.2
        omega
      have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := by
        ext
        exact hi
      rw [hi_eq]
  right_inv p := by
    ext i
    · dsimp [prefixSucc]
      split_ifs with h
      · rfl
      · omega
    · dsimp
      split_ifs with h
      · omega
      · rfl

theorem card_BitWord (n : ℕ) : Fintype.card (BitWord n) = 2^n := by
  dsimp [BitWord]
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The canonical normalized tracial state on `DiagAlg n`. -/
def DiagTrace (n : ℕ) (f : DiagAlg n) : ℂ :=
  (2 : ℂ)⁻¹ ^ n * Finset.sum Finset.univ f

/-! ### Order-theoretic finite-stage readout

The complex-valued diagonal trace above is the algebraic finite-stage
functional used by the existing UHF/KMS corridor.  For the native
`PositiveLinearMap` API we record its real finite-stage counterpart on the
pointwise ordered function space.  This is deliberately a finite-stage
construction; it does not assert a positive map on the completed Cuntz
algebra.
-/

/-- The normalized real diagonal readout at a finite binary stage. -/
def DiagTraceReal (n : ℕ) (f : BitWord n → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ n * Finset.sum Finset.univ f

/-- The real diagonal readout as a native linear map. -/
def DiagTraceRealLinear (n : ℕ) :
    (BitWord n → ℝ) →ₗ[ℝ] ℝ where
  toFun := DiagTraceReal n
  map_add' f g := by
    simp only [DiagTraceReal, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    simp only [DiagTraceReal, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    simp only [RingHom.id_apply]
    ring

@[simp] theorem DiagTraceRealLinear_apply (n : ℕ) (f : BitWord n → ℝ) :
    DiagTraceRealLinear n f = DiagTraceReal n f :=
  rfl

theorem DiagTraceReal_nonneg (n : ℕ) {f : BitWord n → ℝ}
    (hf : 0 ≤ f) : 0 ≤ DiagTraceReal n f := by
  unfold DiagTraceReal
  have hcoeff : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  exact mul_nonneg hcoeff (Finset.sum_nonneg fun i _ => hf i)

/-- The finite diagonal readout is a genuine positive linear map. -/
def DiagTraceRealPositive (n : ℕ) :
    (BitWord n → ℝ) →ₚ[ℝ] ℝ :=
  { DiagTraceRealLinear n with
    monotone' := by
      intro f g hfg
      rw [← sub_nonneg]
      simpa [DiagTraceRealLinear, DiagTraceReal] using
        (DiagTraceReal_nonneg n (fun i => sub_nonneg.mpr (hfg i))) }

@[simp] theorem DiagTraceRealPositive_apply (n : ℕ) (f : BitWord n → ℝ) :
    DiagTraceRealPositive n f = DiagTraceReal n f :=
  rfl

theorem DiagTraceReal_one (n : ℕ) :
    DiagTraceReal n 1 = 1 := by
  simp [DiagTraceReal, Finset.sum_const, Finset.card_univ,
    Nat.cast_pow, inv_pow]

/-- The real-valued successor map on finite diagonal observables. -/
def diagEmbedSuccReal (n : ℕ) :
    (BitWord n → ℝ) → (BitWord (n + 1) → ℝ) :=
  fun f w => f (prefixSucc n w)

theorem DiagTraceReal_compat (n : ℕ) (f : BitWord n → ℝ) :
    DiagTraceReal (n + 1) (diagEmbedSuccReal n f) = DiagTraceReal n f := by
  dsimp [DiagTraceReal, diagEmbedSuccReal]
  change (2 : ℝ)⁻¹ ^ (n + 1) *
      Finset.sum Finset.univ
        (fun w => (fun p : BitWord n × Bool => f p.1) (bitWordEquiv n w)) = _
  have h_equiv := Equiv.sum_comp (bitWordEquiv n)
    (fun p : BitWord n × Bool => f p.1)
  rw [h_equiv]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  have h_inner : ∀ x : BitWord n,
      Finset.sum Finset.univ (fun _ : Bool => f x) = 2 * f x := by
    intro x
    simp
  simp_rw [h_inner]
  rw [← Finset.mul_sum]
  have h_pow_succ : (2 : ℝ)⁻¹ ^ (n + 1) =
      (2 : ℝ)⁻¹ ^ n * (2 : ℝ)⁻¹ := by
    exact pow_succ (2 : ℝ)⁻¹ n
  rw [h_pow_succ]
  ring

theorem DiagTraceRealPositive_compat (n : ℕ) (f : BitWord n → ℝ) :
    DiagTraceRealPositive (n + 1) (diagEmbedSuccReal n f) =
      DiagTraceRealPositive n f := by
  rw [DiagTraceRealPositive_apply, DiagTraceRealPositive_apply,
    DiagTraceReal_compat]

theorem DiagTrace_eq_normalizedTrace (n : ℕ) (f : DiagAlg n) :
    DiagTrace n f =
      InfoGeometry.Canonical.KMSTraceColimit.normalizedTrace n f := by
  unfold DiagTrace InfoGeometry.Canonical.KMSTraceColimit.normalizedTrace
  rw [inv_pow]
  ring

/-- Linear map implementation of the trace. -/
def DiagTrace_addMonoidHom (n : ℕ) : DiagAlg n →+ ℂ where
  toFun := DiagTrace n
  map_zero' := by
    dsimp [DiagTrace]
    simp
  map_add' f g := by
    dsimp [DiagTrace]
    rw [← mul_add]
    congr 1
    exact Finset.sum_add_distrib

/-- The trace of the identity is 1 (normalization). -/
theorem DiagTrace_one (n : ℕ) : DiagTrace n 1 = 1 := by
  dsimp [DiagTrace]
  have h_sum : Finset.sum Finset.univ (1 : DiagAlg n) = Fintype.card (BitWord n) := by
    simp
  rw [h_sum, card_BitWord, Nat.cast_pow]
  have h_pow : (2 : ℂ)⁻¹ ^ n = (2^n : ℂ)⁻¹ := by
    rw [inv_pow]
  rw [h_pow]
  have h_nonzero : (2^n : ℂ) ≠ 0 := by
    exact pow_ne_zero n (by norm_num)
  exact inv_mul_cancel₀ h_nonzero

/-- The trace maps natively form an `AlgebraicState` on each stage. -/
def DiagTrace_state (n : ℕ) : BostConnesSuperalgebra.AlgebraicState (DiagAlg n) where
  val := DiagTrace_addMonoidHom n
  map_one := DiagTrace_one n

/-- Tracial compatibility: the successor embedding preserves the canonical trace. -/
theorem DiagTrace_compat (n : ℕ) (f : DiagAlg n) :
    DiagTrace (n + 1) (diagEmbedSucc n f) = DiagTrace n f := by
  dsimp [DiagTrace]
  unfold diagEmbedSucc
  change (2 : ℂ)⁻¹ ^ (n + 1) * Finset.sum Finset.univ (fun w => (fun p : BitWord n × Bool => f p.1) (bitWordEquiv n w)) = _
  have h_equiv := Equiv.sum_comp (bitWordEquiv n) (fun p : BitWord n × Bool => f p.1)
  rw [h_equiv]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  have h_inner : ∀ x : BitWord n, Finset.sum Finset.univ (fun _ : Bool => f x) = 2 * f x := by
    intro x
    simp
  simp_rw [h_inner]
  rw [← Finset.mul_sum]
  have h_pow_succ : (2 : ℂ)⁻¹ ^ (n + 1) = (2 : ℂ)⁻¹ ^ n * (2 : ℂ)⁻¹ := by
    exact pow_succ (2 : ℂ)⁻¹ n
  rw [h_pow_succ]
  ring

theorem DiagTrace_compat_two (n : ℕ) (f : DiagAlg n) :
    DiagTrace (n + 2) (diagEmbedSucc (n + 1) (diagEmbedSucc n f)) =
      DiagTrace n f := by
  rw [DiagTrace_compat (n + 1) (diagEmbedSucc n f)]
  exact DiagTrace_compat n f

theorem DiagTrace_const (n : ℕ) (z : ℂ) :
    DiagTrace n (fun _ : BitWord n => z) = z := by
  simp [DiagTrace, Finset.sum_const, Finset.card_univ, card_BitWord,
    Nat.cast_pow, inv_pow]

def cylinderIndicator (n : ℕ) (w : BitWord n) : DiagAlg n :=
  fun v => if v = w then 1 else 0

theorem cylinderIndicator_mul_self (n : ℕ) (w : BitWord n) :
    cylinderIndicator n w * cylinderIndicator n w =
      cylinderIndicator n w := by
  classical
  ext v
  simp [cylinderIndicator]

theorem cylinderIndicator_mul_eq_zero_of_ne
    (n : ℕ) {w v : BitWord n} (hwv : w ≠ v) :
    cylinderIndicator n w * cylinderIndicator n v = 0 := by
  classical
  have hvw : v ≠ w := Ne.symm hwv
  ext u
  by_cases huw : u = w <;> by_cases huv : u = v <;>
    simp [cylinderIndicator, huw, huv, hwv, hvw]

theorem cylinderIndicator_star (n : ℕ) (w : BitWord n) :
    star (cylinderIndicator n w) = cylinderIndicator n w := by
  ext v
  simp [cylinderIndicator]

theorem cylinderIndicator_sum (n : ℕ) :
    ∑ w : BitWord n, cylinderIndicator n w = (1 : DiagAlg n) := by
  classical
  ext v
  simp [cylinderIndicator]

theorem DiagTrace_cylinderIndicator_sum (n : ℕ) :
    DiagTrace n (∑ w : BitWord n, cylinderIndicator n w) = 1 := by
  rw [cylinderIndicator_sum]
  exact DiagTrace_one n

theorem DiagTrace_cylinderIndicator (n : ℕ) (w : BitWord n) :
    DiagTrace n (cylinderIndicator n w) = (2 : ℂ)⁻¹ ^ n := by
  classical
  unfold DiagTrace cylinderIndicator
  rw [Finset.sum_eq_single w]
  · simp
  · intro b hb hbw
    simp [hbw]
  · simp

def extendBitWord (n : ℕ) (w : BitWord n) (b : Bool) : BitWord (n + 1) :=
  (bitWordEquiv n).symm (w, b)

theorem cylinderIndicator_refines
    (n : ℕ) (w : BitWord n) :
    diagEmbedSucc n (cylinderIndicator n w) =
      cylinderIndicator (n + 1) (extendBitWord n w false) +
        cylinderIndicator (n + 1) (extendBitWord n w true) := by
  classical
  ext v
  let p := bitWordEquiv n v
  have hv : v = (bitWordEquiv n).symm p := by
    simpa [p] using (bitWordEquiv n).symm_apply_apply v |>.symm
  rcases p with ⟨u, b⟩
  have hpref : prefixSucc n ((bitWordEquiv n).symm (u, b)) = u := by
    simpa [bitWordEquiv] using
      congrArg Prod.fst ((bitWordEquiv n).apply_symm_apply (u, b))
  cases b <;>
    simp [diagEmbedSucc, cylinderIndicator, extendBitWord, hv, hpref]

theorem DiagTrace_cylinderIndicator_refines
    (n : ℕ) (w : BitWord n) :
    DiagTrace (n + 1)
        (cylinderIndicator (n + 1) (extendBitWord n w false) +
          cylinderIndicator (n + 1) (extendBitWord n w true)) =
      DiagTrace n (cylinderIndicator n w) := by
  rw [← cylinderIndicator_refines n w]
  exact DiagTrace_compat n (cylinderIndicator n w)

theorem DiagTrace_smul (n : ℕ) (z : ℂ) (f : DiagAlg n) :
    DiagTrace n (z • f) = z * DiagTrace n f := by
  unfold DiagTrace
  change (2 : ℂ)⁻¹ ^ n * (∑ w : BitWord n, z * f w) =
    z * ((2 : ℂ)⁻¹ ^ n * ∑ w : BitWord n, f w)
  rw [← Finset.mul_sum]
  ring

theorem DiagTrace_star (n : ℕ) (f : DiagAlg n) :
    DiagTrace n (star f) = star (DiagTrace n f) := by
  unfold DiagTrace
  change (2 : ℂ)⁻¹ ^ n * (∑ w : BitWord n, star (f w)) =
    star ((2 : ℂ)⁻¹ ^ n * ∑ w : BitWord n, f w)
  rw [star_mul, star_sum]
  rw [star_pow]
  have hstar : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    norm_num
  rw [hstar]
  ring

theorem DiagTrace_mul_comm (n : ℕ) (f g : DiagAlg n) :
    DiagTrace n (f * g) = DiagTrace n (g * f) := by
  unfold DiagTrace
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  exact mul_comm (f w) (g w)

theorem DiagTrace_star_mul_self_star (n : ℕ) (f : DiagAlg n) :
    star (DiagTrace n (star f * f)) =
      DiagTrace n (star f * f) := by
  rw [← DiagTrace_star]
  simp only [star_mul, star_star]

theorem DiagTrace_star_mul_self_re_nonneg (n : ℕ) (f : DiagAlg n) :
    0 ≤ (DiagTrace n (star f * f)).re := by
  unfold DiagTrace
  have hscalar : (2 : ℂ)⁻¹ ^ n =
      (((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
    norm_num
  rw [hscalar]
  have hsum :
      (∑ w : BitWord n, (star f * f) w).re =
        ∑ w : BitWord n, Complex.normSq (f w) := by
    let s : Finset (BitWord n) := Finset.univ
    have hsum_re : ∀ u : Finset (BitWord n),
        (Finset.sum u (fun w => (star f * f) w)).re =
          Finset.sum u (fun w => Complex.normSq (f w)) := by
      intro u
      induction u using Finset.induction_on with
      | empty => simp
      | @insert w u hw ih =>
          simp only [Finset.sum_insert hw, Complex.add_re, ih]
          simp only [Pi.mul_apply, Pi.star_apply]
          have hpoint :
              (f w * star (f w)).re = Complex.normSq (f w) := by
            change (f w * (starRingEnd ℂ) (f w)).re = Complex.normSq (f w)
            rw [Complex.mul_re, Complex.conj_re, Complex.conj_im,
              Complex.normSq_apply]
            ring
          rw [show star (f w) * f w = f w * star (f w) by ac_rfl, hpoint]
    simpa [s] using hsum_re Finset.univ
  change 0 ≤
    ((((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) *
      (∑ w : BitWord n, (star f * f) w)).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hsum]
  have hscalar_nonneg : 0 ≤ (2 : ℝ)⁻¹ ^ n := by
    exact pow_nonneg (by norm_num) n
  have hsum_nonneg :
      0 ≤ ∑ w : BitWord n, Complex.normSq (f w) := by
    exact Finset.sum_nonneg (fun w hw => Complex.normSq_nonneg (f w))
  simpa using mul_nonneg hscalar_nonneg hsum_nonneg

theorem DiagTrace_star_mul_self_im_zero (n : ℕ) (f : DiagAlg n) :
    (DiagTrace n (star f * f)).im = 0 := by
  have hstar := DiagTrace_star_mul_self_star n f
  have him := congrArg Complex.im hstar
  have him' : -(DiagTrace n (star f * f)).im =
      (DiagTrace n (star f * f)).im := by
    simpa only [Complex.star_def, Complex.conj_im] using him
  linarith

theorem DiagTrace_star_mul_self_eq_ofReal_nonneg (n : ℕ) (f : DiagAlg n) :
    ∃ r : ℝ, 0 ≤ r ∧
      DiagTrace n (star f * f) = (r : ℂ) := by
  refine ⟨(DiagTrace n (star f * f)).re,
    DiagTrace_star_mul_self_re_nonneg n f, ?_⟩
  apply Complex.ext
  · rfl
  · exact DiagTrace_star_mul_self_im_zero n f

end InfoGeometry.Canonical.CantorKMSState

end noncomputable section
