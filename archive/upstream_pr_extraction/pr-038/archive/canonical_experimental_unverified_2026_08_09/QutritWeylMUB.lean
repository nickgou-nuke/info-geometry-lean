import Mathlib
import InfoGeometry.Canonical.SixStateSpectralBridge
import InfoGeometry.Canonical.QutritWeylCommutingLines

/-!
# The four mutually unbiased qutrit bases

The commuting-line owner records the four Weyl directions only.  This owner
adds the normalized quadratic-phase vectors and proves the overlap invariant
directly.  It does not identify the four bases with the sheet phase.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritWeylMUB

open Complex
open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.SixStateSpectralBridge
open InfoGeometry.Canonical.QutritWeylOperatorBasis
open InfoGeometry.Topology.Parafermion

abbrev QutritVector := Fin 3 → ℂ

def normFactor : ℂ := ((1 / Real.sqrt 3 : ℝ) : ℂ)

def phaseExponent (b a x : Fin 3) : ℕ :=
  (b : ℕ) * (x : ℕ) * (x : ℕ) + (a : ℕ) * (x : ℕ)

def chirpVector (b a : Fin 3) : QutritVector :=
  fun x => normFactor * omega ^ phaseExponent b a x

def computationalVector (a : Fin 3) : QutritVector :=
  fun x => if x = a then 1 else 0

def qutritInner (u v : QutritVector) : ℂ :=
  ∑ x : Fin 3, star (u x) * v x

private lemma sqrt_three_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
  norm_num

private lemma normFactor_normSq : Complex.normSq normFactor = (1 / 3 : ℝ) := by
  simp [normFactor, Complex.normSq_apply]

private lemma omega_star_pow (n : ℕ) :
    (starRingEnd ℂ) (omega ^ n) = omega ^ (2 * n) := by
  change (starRingEnd ℂ) (omega ^ n) = omega ^ (2 * n)
  have hstar : (starRingEnd ℂ) omega = omega ^ 2 := by
    simpa only [Complex.star_def] using omega_star_eq_sq
  rw [map_pow, hstar]
  rw [pow_mul]

private lemma omega_pow_star_mul (n : ℕ) :
    (starRingEnd ℂ) (omega ^ n) * omega ^ n = 1 := by
  rw [omega_star_pow, ← pow_add]
  have : 2 * n + n = 3 * n := by ring
  rw [this, pow_mul, omega_cube_eq_one, one_pow]

private lemma omega_pow_mod_three (n : ℕ) :
    omega ^ n = omega ^ (n % 3) := by
  calc
    omega ^ n = omega ^ (n % 3 + 3 * (n / 3)) := by
      rw [Nat.mod_add_div]
    _ = omega ^ (n % 3) * omega ^ (3 * (n / 3)) := by
      rw [pow_add]
    _ = omega ^ (n % 3) := by
      rw [pow_mul, omega_cube_eq_one, one_pow, mul_one]

private lemma normFactor_star_mul :
    (starRingEnd ℂ) normFactor * normFactor = (1 / 3 : ℂ) := by
  norm_num [normFactor, Complex.star_def, Complex.normSq_apply]
  field_simp
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

private lemma chirp_inner_term (m n : ℕ) :
    (starRingEnd ℂ) (normFactor * omega ^ m) *
        (normFactor * omega ^ n) =
      (1 / 3 : ℂ) * ((starRingEnd ℂ) (omega ^ m) * omega ^ n) := by
  calc
    (starRingEnd ℂ) (normFactor * omega ^ m) *
        (normFactor * omega ^ n) =
      (starRingEnd ℂ) normFactor *
        (starRingEnd ℂ) (omega ^ m) *
          (normFactor * omega ^ n) := by rw [map_mul]
    _ = ((starRingEnd ℂ) normFactor * normFactor) *
        ((starRingEnd ℂ) (omega ^ m) * omega ^ n) := by ring
    _ = (1 / 3 : ℂ) *
        ((starRingEnd ℂ) (omega ^ m) * omega ^ n) := by
      rw [normFactor_star_mul]

private lemma chirp_inner_term_star (m n : ℕ) :
    star (normFactor * omega ^ m) * (normFactor * omega ^ n) =
      (1 / 3 : ℂ) * ((starRingEnd ℂ) (omega ^ m) * omega ^ n) := by
  exact chirp_inner_term m n

set_option maxHeartbeats 1000000 in
theorem chirpVector_normSq (b a : Fin 3) :
    Complex.normSq (qutritInner (chirpVector b a) (chirpVector b a)) = 1 := by
  have hterm (x : Fin 3) :
      star (chirpVector b a x) * chirpVector b a x = (1 / 3 : ℂ) := by
    change (starRingEnd ℂ) (normFactor * omega ^ phaseExponent b a x) *
      (normFactor * omega ^ phaseExponent b a x) = (1 / 3 : ℂ)
    calc
      (starRingEnd ℂ) (normFactor * omega ^ phaseExponent b a x) *
          (normFactor * omega ^ phaseExponent b a x) =
      (starRingEnd ℂ) normFactor *
          (starRingEnd ℂ) (omega ^ phaseExponent b a x) *
            (normFactor * omega ^ phaseExponent b a x) := by
        rw [map_mul]
      _ = ((starRingEnd ℂ) normFactor * normFactor) *
            ((starRingEnd ℂ) (omega ^ phaseExponent b a x) *
              omega ^ phaseExponent b a x) := by ring
      _ = (1 / 3 : ℂ) := by rw [normFactor_star_mul, omega_pow_star_mul]; ring
  change Complex.normSq (∑ x : Fin 3,
    star (chirpVector b a x) * chirpVector b a x) = 1
  simp_rw [hterm]
  norm_num [Complex.normSq_apply, Fin.sum_univ_three]

theorem computational_chirp_overlap (a b c : Fin 3) :
    Complex.normSq
      (qutritInner (computationalVector a) (chirpVector b c)) = (1 / 3 : ℝ) := by
  have hsum : qutritInner (computationalVector a) (chirpVector b c) =
      normFactor * omega ^ phaseExponent b c a := by
    simp [qutritInner, computationalVector, chirpVector]
  rw [hsum]
  rw [Complex.normSq_mul]
  rw [normFactor_normSq]
  have hunit : Complex.normSq (omega ^ phaseExponent b c a) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    rw [norm_pow]
    simp [omega, Complex.norm_exp]
  rw [hunit]
  norm_num

def mutuallyUnbiased (u v : QutritVector) : Prop :=
  Complex.normSq (qutritInner u v) = (1 / 3 : ℝ)

theorem computationalVector_normSq (a : Fin 3) :
    Complex.normSq
      (qutritInner (computationalVector a) (computationalVector a)) = 1 := by
  unfold qutritInner computationalVector
  simp [Fin.sum_univ_three, Complex.normSq_apply]

theorem computationalVector_orthogonal {a a' : Fin 3} (h : a ≠ a') :
    qutritInner (computationalVector a) (computationalVector a') = 0 := by
  unfold qutritInner computationalVector
  simp [Fin.sum_univ_three, h, Ne.symm h]

set_option maxHeartbeats 2000000 in
private lemma normSq_one_add_two_omega :
    Complex.normSq (1 + 2 * omega) = 3 := by
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  have hstar_one : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _
  have hstar_two : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa only [Complex.star_def] using (star_natCast 2 : star (2 : ℂ) = 2)
  have hstar_omega : (starRingEnd ℂ) omega = omega ^ 2 := by
    simpa only [Complex.star_def] using omega_star_eq_sq
  rw [map_add, map_mul, hstar_one, hstar_two, hstar_omega]
  have hsum : 1 + omega + omega ^ 2 = 0 := by
    have hfactor : (omega - 1) * (1 + omega + omega ^ 2) = 0 := by
      calc
        (omega - 1) * (1 + omega + omega ^ 2) = omega ^ 3 - 1 := by ring
        _ = 0 := by rw [omega_cube_eq_one]; ring
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr omega_ne_one)
  ring_nf
  rw [omega_cube_eq_one]
  linear_combination (2 : ℂ) * hsum

private lemma normSq_two_add_omega_sq :
    Complex.normSq (2 + omega ^ 2) = 3 := by
  have hmul : (2 + omega ^ 2 : ℂ) = omega ^ 2 * (1 + 2 * omega) := by
    calc
      2 + omega ^ 2 = omega ^ 2 + 2 := by ring
      _ = omega ^ 2 + 2 * (omega ^ 2 * omega) := by
        have hpow : omega ^ 2 * omega = 1 := by
          calc
            omega ^ 2 * omega = omega ^ 3 := by ring
            _ = 1 := omega_cube_eq_one
        rw [hpow]
        ring
      _ = omega ^ 2 * (1 + 2 * omega) := by ring
  rw [hmul, Complex.normSq_mul, normSq_one_add_two_omega]
  have : Complex.normSq (omega ^ 2) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow]
    simp [omega, Complex.norm_exp]
  rw [this]
  norm_num

theorem chirpVector_cross_unbiased {b b' a a' : Fin 3} (h : b ≠ b') :
    mutuallyUnbiased (chirpVector b a) (chirpVector b' a') := by
  have hsum : 1 + omega + omega ^ 2 = 0 := by
    have hfactor : (omega - 1) * (1 + omega + omega ^ 2) = 0 := by
      calc
        (omega - 1) * (1 + omega + omega ^ 2) = omega ^ 3 - 1 := by ring
        _ = 0 := by rw [omega_cube_eq_one]; ring
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr omega_ne_one)
  have hpow4 : omega ^ 4 = omega := by
    calc
      omega ^ 4 = omega ^ 3 * omega := by ring
      _ = omega := by rw [omega_cube_eq_one]; simp
  unfold mutuallyUnbiased qutritInner chirpVector phaseExponent
  simp_rw [chirp_inner_term_star, omega_star_pow, omega_pow_mod_three]
  fin_cases b <;> fin_cases b' <;> simp_all
  all_goals
    fin_cases a <;> fin_cases a' <;>
      simp_all [Fin.sum_univ_three, hpow4, hsum]
  all_goals
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self]
    simp [map_add, map_mul, omega_star_pow, hpow4, hsum,
      omega_cube_eq_one]
    ring

theorem chirpVector_orthogonal {b a a' : Fin 3} (h : a ≠ a') :
    qutritInner (chirpVector b a) (chirpVector b a') = 0 := by
  have hsum : 1 + omega + omega ^ 2 = 0 := by
    have hfactor : (omega - 1) * (1 + omega + omega ^ 2) = 0 := by
      calc
        (omega - 1) * (1 + omega + omega ^ 2) = omega ^ 3 - 1 := by ring
        _ = 0 := by rw [omega_cube_eq_one]; ring
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr omega_ne_one)
  have hpow4 : omega ^ 4 = omega := by
    calc
      omega ^ 4 = omega ^ 3 * omega := by ring
      _ = omega := by rw [omega_cube_eq_one]; simp
  unfold qutritInner chirpVector phaseExponent
  simp_rw [chirp_inner_term_star, omega_star_pow, omega_pow_mod_three]
  fin_cases b <;> fin_cases a <;> fin_cases a' <;>
    simp_all [Fin.sum_univ_three, omega_cube_eq_one, hpow4] <;>
    try { linear_combination (1 / 3 : ℂ) * hsum } <;>
    ring

def mubFamily : Fin 4 → Fin 3 → QutritVector :=
  ![computationalVector, chirpVector 0, chirpVector 1, chirpVector 2]

def OrthonormalQutritFamily (v : Fin 3 → QutritVector) : Prop :=
  (∀ a, Complex.normSq (qutritInner (v a) (v a)) = 1) ∧
    (∀ a a', a ≠ a' → qutritInner (v a) (v a') = 0)

def FourQutritMUB : Prop :=
  (∀ g : Fin 4, OrthonormalQutritFamily (mubFamily g)) ∧
    (∀ g g' : Fin 4, g ≠ g' → ∀ a a' : Fin 3,
      mutuallyUnbiased (mubFamily g a) (mubFamily g' a'))

set_option maxHeartbeats 2000000 in
theorem mubFamily_is_four_MUB : FourQutritMUB := by
  constructor
  · intro g
    constructor
    · intro a
      fin_cases g
      · exact computationalVector_normSq a
      · exact chirpVector_normSq 0 a
      · exact chirpVector_normSq 1 a
      · exact chirpVector_normSq 2 a
    · intro a a' h
      fin_cases g
      · exact computationalVector_orthogonal h
      · exact chirpVector_orthogonal h
      · exact chirpVector_orthogonal h
      · exact chirpVector_orthogonal h
  · intro g g' h a a'
    fin_cases g <;> fin_cases g'
    all_goals simp_all [mubFamily]
    all_goals
      first
      | exact computational_chirp_overlap a 0 a'
      | exact computational_chirp_overlap a 1 a'
      | exact computational_chirp_overlap a 2 a'
      | exact computational_chirp_overlap a' 0 a
      | exact computational_chirp_overlap a' 1 a
      | exact computational_chirp_overlap a' 2 a
      | exact chirpVector_cross_unbiased (by omega)

end InfoGeometry.Canonical.QutritWeylMUB

end noncomputable section
