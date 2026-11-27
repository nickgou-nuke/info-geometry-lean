/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import InfoGeometry.Twistor.InfinityTwistor

/-!
# Spinor-helicity identities on the native complex momentum carrier

The bracket is the existing infinity alternating form restricted to its lower
spinor plane. Momenta are the existing `spinorOuter` matrices. The determinant
identity fixes the angle/square sign without assuming a normalization for a
separately defined Lorentz pairing. Nonzero momentum factorizations form one
inverse-scaling orbit. No amplitude or Lorentzian reality condition is assumed.

Reference: Witten, hep-th/0312171v2, equations (2.3)--(2.7).
-/

namespace InfoGeometry.Twistor.WittenSpinorHelicity

open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.InfinityTwistor
open scoped Matrix

/-- The native infinity form restricted to the lower-spinor plane. -/
def spinorBracket (lambda mu : Spinor2) : ℂ :=
  infinityTwistor (0, lambda) (0, mu)

@[simp] theorem spinorBracket_apply (lambda mu : Spinor2) :
    spinorBracket lambda mu = lambda 0 * mu 1 - lambda 1 * mu 0 := rfl

@[simp] theorem spinorBracket_self (lambda : Spinor2) :
    spinorBracket lambda lambda = 0 := by
  exact infinityTwistor_self (0, lambda)

theorem spinorBracket_swap (lambda mu : Spinor2) :
    spinorBracket mu lambda = -spinorBracket lambda mu := by
  exact infinityTwistor_swap (0, lambda) (0, mu)

theorem spinorBracket_smul (c d : ℂ) (lambda mu : Spinor2) :
    spinorBracket (c • lambda) (d • mu) =
      (c * d) * spinorBracket lambda mu := by
  simp only [spinorBracket_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The two-component Schouten identity is a genuine spinor equality. -/
theorem spinorBracket_schouten (lambda mu nu : Spinor2) :
    spinorBracket lambda mu • nu + spinorBracket mu nu • lambda +
      spinorBracket nu lambda • mu = 0 := by
  funext i
  fin_cases i
  · change (lambda 0 * mu 1 - lambda 1 * mu 0) * nu 0 +
      (mu 0 * nu 1 - mu 1 * nu 0) * lambda 0 +
      (nu 0 * lambda 1 - nu 1 * lambda 0) * mu 0 = 0
    ring
  · change (lambda 0 * mu 1 - lambda 1 * mu 0) * nu 1 +
      (mu 0 * nu 1 - mu 1 * nu 0) * lambda 1 +
      (nu 0 * lambda 1 - nu 1 * lambda 0) * mu 1 = 0
    ring

/-- The Mandelstam determinant for two independent complex null momenta. -/
theorem det_sum_spinorOuter
    (lambda mu lambdaTilde muTilde : Spinor2) :
    (spinorOuter lambda lambdaTilde + spinorOuter mu muTilde).det =
      spinorBracket lambda mu * spinorBracket lambdaTilde muTilde := by
  simp [spinorOuter, Matrix.det_fin_two]
  ring

/-- Both factors scale independently in the existing rank-one matrix. -/
theorem spinorOuter_smul (c d : ℂ) (lambda lambdaTilde : Spinor2) :
    spinorOuter (c • lambda) (d • lambdaTilde) =
      (c * d) • spinorOuter lambda lambdaTilde := by
  ext i j
  simp [spinorOuter, smul_eq_mul]
  ring

/-- Nonzero inverse scalings preserve the momentum itself. -/
theorem spinorOuter_littleGroup (c : ℂ) (hc : c ≠ 0)
    (lambda lambdaTilde : Spinor2) :
    spinorOuter (c • lambda) (c⁻¹ • lambdaTilde) =
      spinorOuter lambda lambdaTilde := by
  rw [spinorOuter_smul, mul_inv_cancel₀ hc, one_smul]

theorem spinor_exists_nonzero_coordinate (lambda : Spinor2)
    (hlambda : lambda ≠ 0) : ∃ i, lambda i ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hlambda
  funext i
  exact h i

/-- A rank-one momentum vanishes exactly when one spinor factor vanishes. -/
theorem spinorOuter_eq_zero_iff (lambda lambdaTilde : Spinor2) :
    spinorOuter lambda lambdaTilde = 0 ↔ lambda = 0 ∨ lambdaTilde = 0 := by
  constructor
  · intro h
    by_cases hlambda : lambda = 0
    · exact Or.inl hlambda
    · right
      obtain ⟨i, hi⟩ := spinor_exists_nonzero_coordinate lambda hlambda
      funext j
      have hij := congrArg (fun M : M2C => M i j) h
      change lambda i * lambdaTilde j = 0 at hij
      exact (mul_eq_zero.mp hij).resolve_left hi
  · rintro (rfl | rfl) <;> ext i j <;> simp [spinorOuter]

/-- Two nonzero rank-one factorizations differ by inverse scalar factors.
The proof uses a nonzero matrix entry, not a chosen normalization field. -/
theorem exists_littleGroup_scale
    (lambda lambdaTilde mu muTilde : Spinor2)
    (hlambda : lambda ≠ 0) (hlambdaTilde : lambdaTilde ≠ 0)
    (h : spinorOuter lambda lambdaTilde = spinorOuter mu muTilde) :
    ∃ c : ℂ, c ≠ 0 ∧ mu = c • lambda ∧ muTilde = c⁻¹ • lambdaTilde := by
  obtain ⟨i, hi⟩ := spinor_exists_nonzero_coordinate lambda hlambda
  obtain ⟨j, hj⟩ := spinor_exists_nonzero_coordinate lambdaTilde hlambdaTilde
  have hentry (a b : Fin 2) : lambda a * lambdaTilde b = mu a * muTilde b :=
    congrArg (fun M : M2C => M a b) h
  have hprod : mu i * muTilde j ≠ 0 := by
    rw [← hentry i j]
    exact mul_ne_zero hi hj
  have hmi : mu i ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hmtj : muTilde j ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  refine ⟨mu i / lambda i, div_ne_zero hmi hi, ?_, ?_⟩
  · funext a
    change mu a = (mu i / lambda i) * lambda a
    have hcross : mu a * lambda i = mu i * lambda a := by
      apply mul_right_cancel₀ hmtj
      linear_combination -(lambda i) * (hentry a j) +
        (lambda a) * (hentry i j)
    field_simp [hi]
    exact hcross
  · funext b
    change muTilde b = (mu i / lambda i)⁻¹ * lambdaTilde b
    field_simp [hi, hmi]
    linear_combination -(hentry i b)

/-- The inverse-scaling parameter is itself unique when the first spinor is nonzero. -/
theorem littleGroup_scale_unique (lambda mu : Spinor2) (hlambda : lambda ≠ 0)
    {c d : ℂ} (hc : mu = c • lambda) (hd : mu = d • lambda) : c = d := by
  obtain ⟨i, hi⟩ := spinor_exists_nonzero_coordinate lambda hlambda
  apply mul_right_cancel₀ hi
  exact congrArg (fun v : Spinor2 => v i) (hc.symm.trans hd)

/-- The fiber over a nonzero null momentum is one free little-group orbit. -/
theorem existsUnique_littleGroup_scale
    (lambda lambdaTilde mu muTilde : Spinor2)
    (hP : spinorOuter lambda lambdaTilde ≠ 0)
    (h : spinorOuter lambda lambdaTilde = spinorOuter mu muTilde) :
    ∃! c : ℂ, c ≠ 0 ∧ mu = c • lambda ∧ muTilde = c⁻¹ • lambdaTilde := by
  have hnonzero : lambda ≠ 0 ∧ lambdaTilde ≠ 0 := by
    exact not_or.mp (mt (spinorOuter_eq_zero_iff lambda lambdaTilde).mpr hP)
  obtain ⟨c, hc, hmu, hmuTilde⟩ :=
    exists_littleGroup_scale lambda lambdaTilde mu muTilde
      hnonzero.1 hnonzero.2 h
  refine ⟨c, ⟨hc, hmu, hmuTilde⟩, ?_⟩
  intro d hd
  exact littleGroup_scale_unique lambda mu hnonzero.1 hd.2.1 hmu

/-! ## Real Minkowski Hermitian slice and compact U(1) little group -/

/-- Embed a real 4-momentum `P : Fin 4 → ℝ` into `FourMomentum`. -/
def realFourMomentum (P : Fin 4 → ℝ) : FourMomentum :=
  ⟨P 0, P 1, P 2, P 3⟩

/-- A real 4-momentum produces a Hermitian Pauli matrix (`P = Pᴴ`). -/
theorem pauliMomentum_real_isHermitian (P : Fin 4 → ℝ) :
    (pauliMomentum (realFourMomentum P))ᴴ = pauliMomentum (realFourMomentum P) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [pauliMomentum, realFourMomentum, Matrix.conjTranspose_apply, Complex.conj_I]; try ring)

/-- The Pauli momentum matrix is Hermitian (`Pᴴ = P`) if and only if all four momentum
components are real. -/
theorem pauliMomentum_isHermitian_iff (P : FourMomentum) :
    (pauliMomentum P)ᴴ = pauliMomentum P ↔
      P.E.im = 0 ∧ P.px.im = 0 ∧ P.py.im = 0 ∧ P.pz.im = 0 := by
  constructor
  · intro h
    have h00 : star (pauliMomentum P 0 0) = pauliMomentum P 0 0 :=
      congrArg (fun M : M2C => M 0 0) h
    have h11 : star (pauliMomentum P 1 1) = pauliMomentum P 1 1 :=
      congrArg (fun M : M2C => M 1 1) h
    have h01 : star (pauliMomentum P 1 0) = pauliMomentum P 0 1 :=
      congrArg (fun M : M2C => M 0 1) h
    simp only [pauliMomentum, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.star_def] at h00 h11 h01
    have h00_im := congrArg Complex.im h00
    have h11_im := congrArg Complex.im h11
    have h01_re := congrArg Complex.re h01
    have h01_im := congrArg Complex.im h01
    simp only [Complex.conj_im, Complex.conj_re, Complex.add_im, Complex.sub_im,
      Complex.add_re, Complex.sub_re, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, zero_mul, one_mul]
      at h00_im h11_im h01_re h01_im
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨hE, hpx, hpy, hpz⟩
    let Pr : Fin 4 → ℝ := ![P.E.re, P.px.re, P.py.re, P.pz.re]
    have hEq : P = realFourMomentum Pr := by
      cases P
      simp only [realFourMomentum, Pr]
      congr 1 <;> apply Complex.ext <;> simp_all
    rw [hEq]
    exact pauliMomentum_real_isHermitian Pr

/-- Determinant of the Pauli matrix of a real 4-momentum is the real Minkowski
norm square `P₀² - P₁² - P₂² - P₃²`. -/
theorem det_pauliMomentum_real (P : Fin 4 → ℝ) :
    (pauliMomentum (realFourMomentum P)).det =
      ((P 0 ^ 2 - P 1 ^ 2 - P 2 ^ 2 - P 3 ^ 2 : ℝ) : ℂ) := by
  rw [det_pauliMomentum]
  simp [minkowskiSq, realFourMomentum]

/-- If a real 4-momentum factors as a spinor outer product, it satisfies the
null Minkowski condition `P₀² - P₁² - P₂² - P₃² = 0`. -/
theorem realFourMomentum_null_of_eq_spinorOuter (P : Fin 4 → ℝ)
    (lambda lambdaTilde : Spinor2)
    (hP : pauliMomentum (realFourMomentum P) = spinorOuter lambda lambdaTilde) :
    P 0 ^ 2 - P 1 ^ 2 - P 2 ^ 2 - P 3 ^ 2 = 0 := by
  have hdet : (pauliMomentum (realFourMomentum P)).det = 0 := by
    rw [hP]
    exact det_spinorOuter_zero lambda lambdaTilde
  rw [det_pauliMomentum_real] at hdet
  exact_mod_cast hdet

/-- Any real scalar multiple of `star λ` yields a Hermitian outer product. -/
theorem spinorOuter_isHermitian_of_real_smul (r : ℝ) (lambda : Spinor2) :
    (spinorOuter lambda ((r : ℂ) • star lambda))ᴴ =
      spinorOuter lambda ((r : ℂ) • star lambda) := by
  ext i j
  simp [spinorOuter, Matrix.conjTranspose_apply, smul_eq_mul]
  ring

/-- A rank-one momentum `spinorOuter λ λ̃` with `λ ≠ 0` is Hermitian iff `λ̃` is
a real multiple of `star λ`. -/
theorem spinorOuter_isHermitian_iff (lambda lambdaTilde : Spinor2)
    (hlambda : lambda ≠ 0) :
    (spinorOuter lambda lambdaTilde)ᴴ = spinorOuter lambda lambdaTilde ↔
      ∃ r : ℝ, lambdaTilde = (r : ℂ) • star lambda := by
  constructor
  · intro hHerm
    obtain ⟨i, hi⟩ := spinor_exists_nonzero_coordinate lambda hlambda
    have hij (a b : Fin 2) :
        star (lambda b) * star (lambdaTilde a) = lambda a * lambdaTilde b := by
      have := congrArg (fun M : M2C => M a b) hHerm
      simpa [spinorOuter, Matrix.conjTranspose_apply, mul_comm] using this
    have hii : star (lambda i) * star (lambdaTilde i) = lambda i * lambdaTilde i :=
      hij i i
    have hstari : star (lambda i) ≠ 0 := star_ne_zero.mpr hi
    let c : ℂ := lambdaTilde i / star (lambda i)
    have hc_real : star c = c := by
      dsimp [c]
      simp only [map_div₀, Complex.conj_conj]
      field_simp [hi, hstari]
      simpa [Complex.star_def, mul_comm] using hii
    have hcim : c.im = 0 := by
      have := congrArg Complex.im hc_real
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    have hc_eq : c = (c.re : ℂ) := Complex.ext rfl hcim
    refine ⟨c.re, ?_⟩
    funext j
    have hji := hij i j
    have hlamTilde_i : star (lambdaTilde i) = star c * lambda i := by
      dsimp [c]
      simp only [map_div₀, Complex.conj_conj]
      field_simp [hi]
    rw [hlamTilde_i, hc_real, hc_eq] at hji
    change lambdaTilde j = (c.re : ℂ) * star (lambda j)
    apply mul_left_cancel₀ hi
    calc
      lambda i * lambdaTilde j = star (lambda j) * ((c.re : ℂ) * lambda i) := hji.symm
      _ = lambda i * ((c.re : ℂ) * star (lambda j)) := by ring
  · rintro ⟨r, rfl⟩
    exact spinorOuter_isHermitian_of_real_smul r lambda

/-- For a nonzero spinor outer product, Hermiticity is equivalent to `λ̃ = r • star λ`
with `r : ℝ`, `r ≠ 0`. -/
theorem spinorOuter_nonzero_isHermitian_iff (lambda lambdaTilde : Spinor2)
    (hP : spinorOuter lambda lambdaTilde ≠ 0) :
    (spinorOuter lambda lambdaTilde)ᴴ = spinorOuter lambda lambdaTilde ↔
      ∃ r : ℝ, r ≠ 0 ∧ lambdaTilde = (r : ℂ) • star lambda := by
  have hnonzero : lambda ≠ 0 ∧ lambdaTilde ≠ 0 :=
    not_or.mp (mt (spinorOuter_eq_zero_iff lambda lambdaTilde).mpr hP)
  constructor
  · intro hHerm
    obtain ⟨r, hr⟩ := (spinorOuter_isHermitian_iff lambda lambdaTilde hnonzero.1).mp hHerm
    refine ⟨r, ?_, hr⟩
    intro hr0
    apply hnonzero.2
    rw [hr, hr0]
    simp
  · rintro ⟨r, -, rfl⟩
    exact spinorOuter_isHermitian_of_real_smul r lambda

/-- Real null momentum factored as `spinorOuter λ λ̃` forces `λ̃ = r • star λ` (`r ≠ 0`)
and `P₀² - P₁² - P₂² - P₃² = 0`. -/
theorem real_null_pauliMomentum_spinorOuter_reality (P : Fin 4 → ℝ)
    (lambda lambdaTilde : Spinor2)
    (hP_ne : spinorOuter lambda lambdaTilde ≠ 0)
    (hP : pauliMomentum (realFourMomentum P) = spinorOuter lambda lambdaTilde) :
    (P 0 ^ 2 - P 1 ^ 2 - P 2 ^ 2 - P 3 ^ 2 = 0) ∧
      (∃ r : ℝ, r ≠ 0 ∧ lambdaTilde = (r : ℂ) • star lambda) := by
  refine ⟨realFourMomentum_null_of_eq_spinorOuter P lambda lambdaTilde hP, ?_⟩
  have hHerm : (spinorOuter lambda lambdaTilde)ᴴ = spinorOuter lambda lambdaTilde := by
    rw [← hP]
    exact pauliMomentum_real_isHermitian P
  exact (spinorOuter_nonzero_isHermitian_iff lambda lambdaTilde hP_ne).mp hHerm

/-- A compact `U(1)` phase (`star c * c = 1`) preserves the reality slice `λ̃ = r • star λ`. -/
theorem u1_littleGroup_preserves_reality (c : ℂ) (hc : star c * c = 1)
    (r : ℝ) (lambda : Spinor2) :
    c⁻¹ • ((r : ℂ) • star lambda) = (r : ℂ) • star (c • lambda) := by
  have hcinv : c⁻¹ = star c := by
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hc
      exact zero_ne_one hc
    apply mul_right_cancel₀ hc0
    rw [inv_mul_cancel₀ hc0, hc]
  funext i
  simp [hcinv, smul_eq_mul, mul_left_comm]

/-- On a nonzero real-slice spinor pair `(λ, r • star λ)` (`r ≠ 0`, `λ ≠ 0`),
the little-group scaling `(c • λ, c⁻¹ • λ̃)` preserves the reality slice iff
`star c * c = 1` (compact `U(1)`). -/
theorem littleGroup_preserves_reality_iff_u1 (c : ℂ) (hc0 : c ≠ 0)
    (r : ℝ) (hr : r ≠ 0) (lambda : Spinor2) (hlambda : lambda ≠ 0) :
    c⁻¹ • ((r : ℂ) • star lambda) = (r : ℂ) • star (c • lambda) ↔ star c * c = 1 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := spinor_exists_nonzero_coordinate lambda hlambda
    have hEntry := congrArg (fun v : Spinor2 => v i) h
    simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_smul] at hEntry
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    have hstari : star (lambda i) ≠ 0 := star_ne_zero.mpr hi
    have hcoeff : c⁻¹ = star c := by
      apply mul_right_cancel₀ hrC
      apply mul_right_cancel₀ hstari
      calc
        c⁻¹ * (r : ℂ) * star (lambda i) = c⁻¹ * ((r : ℂ) * star (lambda i)) := by ring
        _ = (r : ℂ) * (star c * star (lambda i)) := hEntry
        _ = star c * (r : ℂ) * star (lambda i) := by ring
    calc
      star c * c = c⁻¹ * c := by rw [hcoeff]
      _ = 1 := inv_mul_cancel₀ hc0
  · intro hc
    exact u1_littleGroup_preserves_reality c hc r lambda

/-- The compact `U(1)` condition `star c * c = 1` is equivalent to `‖c‖ = 1`. -/
theorem star_mul_self_eq_one_iff_norm_eq_one (c : ℂ) :
    star c * c = 1 ↔ ‖c‖ = 1 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj]
  constructor
  · intro h
    have hre : (Complex.normSq c : ℝ) = 1 := by
      exact_mod_cast h
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    have hsq : c.re * c.re + c.im * c.im = 1 := by
      simpa [Complex.normSq_apply] using hre
    rw [show c.re ^ 2 + c.im ^ 2 = c.re * c.re + c.im * c.im by ring, hsq, Real.sqrt_one]
  · intro h
    have hns : Complex.normSq c = 1 := by
      rw [Complex.normSq_eq_norm_sq, h]
      norm_num
    exact_mod_cast hns

/-! ## Lorentz 2-momentum inner product bridge -/

/-- Minkowski inner product on complexified `FourMomentum` (mostly-minus signature). -/
def minkowskiDot (P₁ P₂ : FourMomentum) : ℂ :=
  P₁.E * P₂.E - P₁.px * P₂.px - P₁.py * P₂.py - P₁.pz * P₂.pz

/-- Minkowski inner product on real `Fin 4 → ℝ` momenta (mostly-minus signature). -/
def realMinkowskiDot (P₁ P₂ : Fin 4 → ℝ) : ℝ :=
  P₁ 0 * P₂ 0 - P₁ 1 * P₂ 1 - P₁ 2 * P₂ 2 - P₁ 3 * P₂ 3

theorem minkowskiDot_real (P₁ P₂ : Fin 4 → ℝ) :
    minkowskiDot (realFourMomentum P₁) (realFourMomentum P₂) =
      (realMinkowskiDot P₁ P₂ : ℂ) := by
  simp [minkowskiDot, realFourMomentum, realMinkowskiDot]

/-- Determinant of the sum of two Pauli momentum matrices expands via Minkowski norms
and twice the Lorentz inner product. -/
theorem det_add_pauliMomentum (P₁ P₂ : FourMomentum) :
    (pauliMomentum P₁ + pauliMomentum P₂).det =
      minkowskiSq P₁ + minkowskiSq P₂ + 2 * minkowskiDot P₁ P₂ := by
  have hsum : pauliMomentum P₁ + pauliMomentum P₂ =
      pauliMomentum ⟨P₁.E + P₂.E, P₁.px + P₂.px, P₁.py + P₂.py, P₁.pz + P₂.pz⟩ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliMomentum] <;> ring
  rw [hsum, det_pauliMomentum]
  simp only [minkowskiSq, minkowskiDot]
  ring

/-- For two null momenta `P₁ = λ₁ λ̃₁`, `P₂ = λ₂ λ̃₂`, `det(p₁ + p₂) = 2 (P₁ · P₂)`. -/
theorem det_sum_pauliMomentum_eq_two_minkowskiDot (P₁ P₂ : FourMomentum)
    (lambda₁ lambdaTilde₁ lambda₂ lambdaTilde₂ : Spinor2)
    (h₁ : pauliMomentum P₁ = spinorOuter lambda₁ lambdaTilde₁)
    (h₂ : pauliMomentum P₂ = spinorOuter lambda₂ lambdaTilde₂) :
    (spinorOuter lambda₁ lambdaTilde₁ + spinorOuter lambda₂ lambdaTilde₂).det =
      2 * minkowskiDot P₁ P₂ := by
  have hsq₁ : minkowskiSq P₁ = 0 := by
    rw [← det_pauliMomentum, h₁]
    exact det_spinorOuter_zero lambda₁ lambdaTilde₁
  have hsq₂ : minkowskiSq P₂ = 0 := by
    rw [← det_pauliMomentum, h₂]
    exact det_spinorOuter_zero lambda₂ lambdaTilde₂
  rw [← h₁, ← h₂, det_add_pauliMomentum, hsq₁, hsq₂]
  ring

/-- Lorentz inner product of two null momenta matches the spinor bracket product
`2 (P₁ · P₂) = ⟨λ₁ λ₂⟩ [λ̃₁ λ̃₂]`. -/
theorem two_minkowskiDot_eq_spinorBracket_mul (P₁ P₂ : FourMomentum)
    (lambda₁ lambdaTilde₁ lambda₂ lambdaTilde₂ : Spinor2)
    (h₁ : pauliMomentum P₁ = spinorOuter lambda₁ lambdaTilde₁)
    (h₂ : pauliMomentum P₂ = spinorOuter lambda₂ lambdaTilde₂) :
    2 * minkowskiDot P₁ P₂ =
      spinorBracket lambda₁ lambda₂ * spinorBracket lambdaTilde₁ lambdaTilde₂ := by
  rw [← det_sum_pauliMomentum_eq_two_minkowskiDot P₁ P₂ lambda₁ lambdaTilde₁ lambda₂ lambdaTilde₂ h₁ h₂]
  exact det_sum_spinorOuter lambda₁ lambda₂ lambdaTilde₁ lambdaTilde₂

/-! ## Spin-1 helicity polarization matrices and gauge invariance -/

/-- Spinor-raised/adjugate Pauli dual `ε Aᵀ εᵀ = adjugate A`, providing the
Lorentz trace pairing `Tr(A * pauliBar B) = 2 (A · B)`. -/
def pauliBar (A : M2C) : M2C :=
  !![A 1 1, -A 0 1; -A 1 0, A 0 0]

theorem pauliBar_pauliMomentum (P : FourMomentum) :
    pauliBar (pauliMomentum P) = pauliMomentum ⟨P.E, -P.px, -P.py, -P.pz⟩ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliBar, pauliMomentum] <;> ring

/-- Trace pairing against `pauliBar` equals twice the Minkowski dot product. -/
theorem trace_pauliMomentum_mul_pauliBar (P₁ P₂ : FourMomentum) :
    Matrix.trace (pauliMomentum P₁ * pauliBar (pauliMomentum P₂)) =
      2 * minkowskiDot P₁ P₂ := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two,
    pauliMomentum, pauliBar, minkowskiDot, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Trace pairing of two rank-one spinor matrices against `pauliBar` equals the
product of angle and square brackets. -/
theorem trace_spinorOuter_mul_pauliBar (u v x y : Spinor2) :
    Matrix.trace (spinorOuter u v * pauliBar (spinorOuter x y)) =
      spinorBracket u x * spinorBracket v y := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two,
    spinorOuter, pauliBar, spinorBracket_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Positive-helicity (`+1`) spin-1 polarization matrix with reference spinor `q`. -/
noncomputable def epsPlus (q lambda lambdaTilde : Spinor2) : M2C :=
  (spinorBracket q lambda)⁻¹ • spinorOuter q lambdaTilde

/-- Negative-helicity (`-1`) spin-1 polarization matrix with reference spinor `qTilde`. -/
noncomputable def epsMinus (qTilde lambda lambdaTilde : Spinor2) : M2C :=
  (spinorBracket qTilde lambdaTilde)⁻¹ • spinorOuter lambda qTilde

/-- Plus-helicity polarization matrix is null (`det = 0`). -/
theorem det_epsPlus_zero (q lambda lambdaTilde : Spinor2) :
    (epsPlus q lambda lambdaTilde).det = 0 := by
  rw [epsPlus, Matrix.det_smul, det_spinorOuter_zero, mul_zero]

/-- Minus-helicity polarization matrix is null (`det = 0`). -/
theorem det_epsMinus_zero (qTilde lambda lambdaTilde : Spinor2) :
    (epsMinus qTilde lambda lambdaTilde).det = 0 := by
  rw [epsMinus, Matrix.det_smul, det_spinorOuter_zero, mul_zero]

/-- Plus-helicity polarization is transverse to `p = λ λ̃` (`Tr(ε⁺ p̄) = 0`). -/
theorem epsPlus_transverse (q lambda lambdaTilde : Spinor2) :
    Matrix.trace (epsPlus q lambda lambdaTilde * pauliBar (spinorOuter lambda lambdaTilde)) = 0 := by
  rw [epsPlus, Matrix.smul_mul, Matrix.trace_smul, trace_spinorOuter_mul_pauliBar,
    spinorBracket_self, mul_zero, smul_zero]

/-- Minus-helicity polarization is transverse to `p = λ λ̃` (`Tr(ε⁻ p̄) = 0`). -/
theorem epsMinus_transverse (qTilde lambda lambdaTilde : Spinor2) :
    Matrix.trace (epsMinus qTilde lambda lambdaTilde * pauliBar (spinorOuter lambda lambdaTilde)) = 0 := by
  rw [epsMinus, Matrix.smul_mul, Matrix.trace_smul, trace_spinorOuter_mul_pauliBar,
    spinorBracket_self, zero_mul, smul_zero]

/-- Transversality in determinant form: `det(ε⁺ + p) = 0`. -/
theorem det_epsPlus_add_momentum_zero (q lambda lambdaTilde : Spinor2) :
    (epsPlus q lambda lambdaTilde + spinorOuter lambda lambdaTilde).det = 0 := by
  have heps : epsPlus q lambda lambdaTilde =
      spinorOuter ((spinorBracket q lambda)⁻¹ • q) lambdaTilde := by
    ext i j
    simp [epsPlus, spinorOuter, smul_eq_mul, mul_assoc]
  rw [heps, det_sum_spinorOuter, spinorBracket_self, mul_zero]

/-- Transversality in determinant form: `det(ε⁻ + p) = 0`. -/
theorem det_epsMinus_add_momentum_zero (qTilde lambda lambdaTilde : Spinor2) :
    (epsMinus qTilde lambda lambdaTilde + spinorOuter lambda lambdaTilde).det = 0 := by
  have heps : epsMinus qTilde lambda lambdaTilde =
      spinorOuter lambda ((spinorBracket qTilde lambdaTilde)⁻¹ • qTilde) := by
    ext i j
    simp [epsMinus, spinorOuter, smul_eq_mul, mul_left_comm]
  rw [heps, det_sum_spinorOuter, spinorBracket_self, zero_mul]

/-- Gauge invariance of `epsPlus`: shifting reference spinor `q ↦ q'` changes `ε⁺`
by a scalar multiple of `p = spinorOuter λ λ̃`. -/
theorem epsPlus_gauge_shift (q q' lambda lambdaTilde : Spinor2)
    (hq : spinorBracket q lambda ≠ 0) (hq' : spinorBracket q' lambda ≠ 0) :
    epsPlus q' lambda lambdaTilde - epsPlus q lambda lambdaTilde =
      (spinorBracket q q' / (spinorBracket q' lambda * spinorBracket q lambda)) •
        spinorOuter lambda lambdaTilde := by
  have hlin : spinorBracket q lambda • q' - spinorBracket q' lambda • q =
      spinorBracket q q' • lambda := by
    funext i
    fin_cases i <;>
      (simp [spinorBracket_apply]; ring)
  ext i j
  have hcoord := congrArg (fun v : Spinor2 => v i) hlin
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  simp only [epsPlus, Matrix.sub_apply, Matrix.smul_apply, spinorOuter, smul_eq_mul]
  field_simp [hq, hq']
  linear_combination lambdaTilde j * hcoord

/-- Gauge invariance of `epsMinus`: shifting reference spinor `q̃ ↦ q̃'` changes `ε⁻`
by a scalar multiple of `p = spinorOuter λ λ̃`. -/
theorem epsMinus_gauge_shift (qTilde qTilde' lambda lambdaTilde : Spinor2)
    (hq : spinorBracket qTilde lambdaTilde ≠ 0)
    (hq' : spinorBracket qTilde' lambdaTilde ≠ 0) :
    epsMinus qTilde' lambda lambdaTilde - epsMinus qTilde lambda lambdaTilde =
      (spinorBracket qTilde qTilde' /
        (spinorBracket qTilde' lambdaTilde * spinorBracket qTilde lambdaTilde)) •
        spinorOuter lambda lambdaTilde := by
  have hlin : spinorBracket qTilde lambdaTilde • qTilde' -
      spinorBracket qTilde' lambdaTilde • qTilde =
      spinorBracket qTilde qTilde' • lambdaTilde := by
    funext j
    fin_cases j <;>
      (simp [spinorBracket_apply]; ring)
  ext i j
  have hcoord := congrArg (fun v : Spinor2 => v j) hlin
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  simp only [epsMinus, Matrix.sub_apply, Matrix.smul_apply, spinorOuter, smul_eq_mul]
  field_simp [hq, hq']
  linear_combination lambda i * hcoord

/-- Little-group helicity weight of `epsPlus`: `c • λ, c⁻¹ • λ̃` scales `ε⁺` by `c⁻²`. -/
theorem epsPlus_littleGroup (c : ℂ)
    (q lambda lambdaTilde : Spinor2) :
    epsPlus q (c • lambda) (c⁻¹ • lambdaTilde) =
      (c * c)⁻¹ • epsPlus q lambda lambdaTilde := by
  have hbr : spinorBracket q (c • lambda) = c * spinorBracket q lambda := by
    simpa using spinorBracket_smul 1 c q lambda
  ext i j
  simp only [epsPlus, hbr, Matrix.smul_apply, spinorOuter, Pi.smul_apply, smul_eq_mul,
    mul_inv_rev]
  ring

/-- Little-group helicity weight of `epsMinus`: `c • λ, c⁻¹ • λ̃` scales `ε⁻` by `c²`. -/
theorem epsMinus_littleGroup (c : ℂ)
    (qTilde lambda lambdaTilde : Spinor2) :
    epsMinus qTilde (c • lambda) (c⁻¹ • lambdaTilde) =
      (c * c) • epsMinus qTilde lambda lambdaTilde := by
  have hbr : spinorBracket qTilde (c⁻¹ • lambdaTilde) =
      c⁻¹ * spinorBracket qTilde lambdaTilde := by
    simpa using spinorBracket_smul 1 c⁻¹ qTilde lambdaTilde
  ext i j
  simp only [epsMinus, hbr, Matrix.smul_apply, spinorOuter, Pi.smul_apply, smul_eq_mul,
    mul_inv_rev, inv_inv]
  ring

/-- Opposite-helicity polarization inner product pairing: `Tr(ε⁺ (ε⁻)̄) = -1`. -/
theorem trace_epsPlus_mul_pauliBar_epsMinus
    (q qTilde lambda lambdaTilde : Spinor2)
    (hq : spinorBracket q lambda ≠ 0) (hqTilde : spinorBracket qTilde lambdaTilde ≠ 0) :
    Matrix.trace (epsPlus q lambda lambdaTilde *
      pauliBar (epsMinus qTilde lambda lambdaTilde)) = -1 := by
  have hbar : ∀ a : ℂ, ∀ M : M2C, pauliBar (a • M) = a • pauliBar M := by
    intro a M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliBar]
  rw [epsPlus, epsMinus, hbar, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul, trace_spinorOuter_mul_pauliBar,
    spinorBracket_swap qTilde lambdaTilde]
  simp only [smul_eq_mul]
  field_simp [hq, hqTilde]

end InfoGeometry.Twistor.WittenSpinorHelicity
