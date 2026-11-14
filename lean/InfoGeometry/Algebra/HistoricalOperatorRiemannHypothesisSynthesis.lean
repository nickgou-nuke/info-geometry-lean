/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.NoncommutativeGeneralWeightRiemannHypothesis

/-!
# Historical Operator Riemann Hypothesis Synthesis ($\mathcal{H}\mathcal{R}_1$–$\mathcal{H}\mathcal{R}_4$)

Epistemic compilation of the five-stage historical convergence of the Riemann Hypothesis
into noncommutative $\star$-ring and `ClTower A n` operator algebra:

1. **$\mathcal{H}\mathcal{R}_1$ (Hasse 1936 – Weil 1948)**
   (`universal_hasse_weil_discriminant_and_castelnuovo_severi`):
   Universal noncommutative Hasse–Weil discriminant identity
   `4 • (star F * F) - star (F + star F) * (F + star F) = star (F - star F) * (F - star F) + 2 • ⁅star F, F⁆`
   and Castelnuovo–Severi–Weil quadratic pencil polarization over any `StarRing B`.
2. **$\mathcal{H}\mathcal{R}_2$ (Deuring 1941 – Weil 1949)**
   (`deuring_quaternion_and_rosati_trace_positivity`):
   Rosati–Hilbert–Schmidt trace positivity `Matrix.trace (Fᴴ * F) = 2 • (star a * a + star b * b)`
   and skew-adjoint quaternion endomorphism generators `quatI, quatJ ι, quatK ι` in `ClTower A 1`.
3. **$\mathcal{H}\mathcal{R}_3$ (Tate 1950 – Serre 1960 – Laumon 1987)**
   (`serre_kahler_similitude_and_laumon_cayley_rotation`):
   Kähler metric–symplectic compatibility `kahlerMetric X Y = Xᴴ * Y`, simultaneous similitude
   of `weilFrobenius a b`, and Laumon–Cayley Mellin-to-shift rotation
   `cayleyFrobenius * gamma1Op * cayleyFrobeniusᴴ = 2 • sigmaOp`.
4. **$\mathcal{H}\mathcal{R}_4$ (Deligne 1974 – Connes 1999)**
   (`deligne_rankin_even_power_and_connes_porous_cutoff`):
   Even-power Rankin positivity `t ^ (2 * m) = star (t ^ m) * (t ^ m)` and Connes phase-space
   cutoff projection energy conservation.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis
open InfoGeometry.Algebra.NoncommutativeWeilCohomologyAndPicardLefschetzSynthesis
open InfoGeometry.Algebra.NoncommutativeGeneralWeightRiemannHypothesis

namespace InfoGeometry.Algebra.HistoricalOperatorRiemannHypothesisSynthesis

section Matrix2Operators

variable {A : Type*} [Ring A]

@[simp] lemma trace_fin2 (M : ClTower A 1) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

/-- Diagonal Mellin grading operator `mat2 1 0 0 (-1)` in `ClTower A 1 = M₂(A)`. -/
def gamma1Op : ClTower A 1 := mat2 1 0 0 (-1)

/-- Off-diagonal Weyl shift operator `mat2 0 1 1 0` in `ClTower A 1 = M₂(A)`. -/
def sigmaOp : ClTower A 1 := mat2 0 1 1 0

end Matrix2Operators

/-!
## Archetype $\mathcal{H}\mathcal{R}_1$: Universal Noncommutative Hasse–Weil Discriminant & Castelnuovo–Severi Identity
-/

section ArchetypeHR1_UniversalHasseWeilDiscriminant

variable {B : Type*} [Ring B] [StarRing B]

/-- **Universal Noncommutative Hasse–Weil Discriminant & Castelnuovo–Severi Identity ($\mathcal{H}\mathcal{R}_1$)**:
In *any* noncommutative `StarRing B`:
1. `4 • (star F * F) - star (F + star F) * (F + star F) = star (F - star F) * (F - star F) + 2 • ⁅star F, F⁆`,
2. When `F` is normal (`⁅star F, F⁆ = 0`), `4 • (star F * F) - (F + star F)^2 = star (F - star F) * (F - star F)`,
3. Castelnuovo–Severi–Weil quadratic pencil polarization. -/
theorem universal_hasse_weil_discriminant_and_castelnuovo_severi
    (F : B) (m n : ℕ) (h_norm : ⁅star F, F⁆ = 0) :
    4 • (star F * F) - star (F + star F) * (F + star F) =
      star (F - star F) * (F - star F) + 2 • ⁅star F, F⁆ ∧
    4 • (star F * F) - (F + star F) * (F + star F) =
      star (F - star F) * (F - star F) ∧
    star ((2 * m) • (1 : B) - n • (F + star F)) * ((2 * m) • (1 : B) - n • (F + star F)) +
      star (n • (F - star F)) * (n • (F - star F)) =
      2 • (star (m • (1 : B) - n • F) * (m • (1 : B) - n • F)) +
      2 • ((m • (1 : B) - n • F) * star (m • (1 : B) - n • F)) := by
  have h_disc : 4 • (star F * F) - star (F + star F) * (F + star F) =
      star (F - star F) * (F - star F) + 2 • ⁅star F, F⁆ := by
    rw [Ring.lie_def]
    simp only [star_add, star_sub, star_star, nsmul_eq_mul, Nat.cast_ofNat]
    noncomm_ring
  refine ⟨h_disc, ?_, ?_⟩
  · have h_sa : star (F + star F) = F + star F := by
      simp [star_add, add_comm]
    rw [h_sa] at h_disc
    rw [h_disc, h_norm, smul_zero, add_zero]
  · have h_nF : (n : B) * F = F * n := Nat.cast_comm n F
    have h_nsF : (n : B) * star F = star F * n := Nat.cast_comm n (star F)
    simp only [nsmul_eq_mul, star_add, star_sub, star_mul, star_natCast, star_ofNat,
      star_one, star_star, Nat.cast_mul, Nat.cast_ofNat]
    noncomm_ring
    simp only [h_nF, h_nsF]
    rw [← mul_assoc (n : B) F, h_nF, mul_assoc]
    rw [← mul_assoc (n : B) F, h_nF, mul_assoc]
    rw [← mul_assoc (n : B) F, h_nF, mul_assoc]
    abel

end ArchetypeHR1_UniversalHasseWeilDiscriminant

/-!
## Archetype $\mathcal{H}\mathcal{R}_2$: Deuring–Weil Quaternion Splitting & Rosati Trace Positivity
-/

section ArchetypeHR2_DeuringQuaternionAndRosatiPositivity

variable {A : Type*} [Ring A] [StarRing A]

/-- Skew-adjoint quaternion generator `J(ι) = mat2 ι 0 0 (-ι)` in `ClTower A 1`. -/
def quatJ (ι : A) : ClTower A 1 := mat2 ι 0 0 (-ι)

/-- Skew-adjoint quaternion generator `K(ι) = mat2 0 ι ι 0` in `ClTower A 1`. -/
def quatK (ι : A) : ClTower A 1 := mat2 0 ι ι 0

/-- **Deuring–Weil Quaternion Splitting & Rosati Trace Positivity ($\mathcal{H}\mathcal{R}_2$)**:
1. `Matrix.trace (Fᴴ * F) = 2 • (star a * a + star b * b)` for `F = weilFrobenius a b`,
2. For any `ι : A` with `ι * ι = -1` and `star ι = -ι`, `quatI`, `quatJ ι`, `quatK ι` are
   skew-adjoint unitaries satisfying `quatI * quatJ ι = quatK ι`. -/
theorem deuring_quaternion_and_rosati_trace_positivity
    (a b : A) {ι : A} (hι_sq : ι * ι = -1) (hι_sa : star ι = -ι) :
    let F := weilFrobenius a b
    Matrix.trace (Fᴴ * F) = 2 • (star a * a + star b * b) ∧
    (quatI : ClTower A 1)ᴴ = -quatI ∧
    (quatJ ι)ᴴ = -quatJ ι ∧
    (quatK ι)ᴴ = -quatK ι ∧
    (quatI : ClTower A 1)ᴴ * quatI = 1 ∧
    (quatJ ι)ᴴ * quatJ ι = 1 ∧
    (quatK ι)ᴴ * quatK ι = 1 ∧
    quatI * quatJ ι = quatK ι := by
  have h_neg_sq : -ι * ι = 1 := by
    calc -ι * ι = -(ι * ι) := by noncomm_ring
      _ = -(-1) := by rw [hι_sq]
      _ = 1 := neg_neg 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [weilFrobenius, mat2, Matrix.trace_fin_two, two_smul]; abel
  · apply ext_fin2 <;> simp [quatI, mat2]
  · apply ext_fin2 <;> simp [quatJ, mat2, hι_sa]
  · apply ext_fin2 <;> simp [quatK, mat2, hι_sa]
  · apply ext_fin2 <;> simp [quatI, mat2]
  · apply ext_fin2 <;> simp [quatJ, mat2, hι_sa, h_neg_sq, hι_sq]
  · apply ext_fin2 <;> simp [quatK, mat2, hι_sa, h_neg_sq]
  · apply ext_fin2 <;> simp [quatI, quatJ, quatK, mat2]

end ArchetypeHR2_DeuringQuaternionAndRosatiPositivity

/-!
## Archetype $\mathcal{H}\mathcal{R}_3$: Serre's Kähler Similitude & Laumon–Cayley Mellin-to-Shift Rotation
-/

section ArchetypeHR3_SerreKahlerAndLaumonCayley

variable {A : Type*} [Ring A] [StarRing A]

/-- Symplectic Kähler pairing `ω_Ω(X, Y) = Xᴴ * omegaOp * Y` on `ClTower A 1`. -/
def kahlerSymplectic (X Y : ClTower A 1) : ClTower A 1 :=
  Xᴴ * omegaOp * Y

/-- Associated Riemannian metric pairing `g_Ω(X, Y) = -ω_Ω(X, omegaOp * Y)` on `ClTower A 1`. -/
def kahlerMetric (X Y : ClTower A 1) : ClTower A 1 :=
  -kahlerSymplectic X (omegaOp * Y)

/-- **Serre's Kähler Similitude & Laumon's Fourier–Cayley Rotation Theorem ($\mathcal{H}\mathcal{R}_3$)**:
1. `kahlerMetric X Y = Xᴴ * Y`,
2. For commuting self-adjoint `a, b : A`, `weilFrobenius a b` is a Kähler similitude of
   multiplier `a * a + b * b` for both `kahlerSymplectic` and `kahlerMetric`,
3. `cayleyFrobenius` satisfies Plancherel scaling `cayleyFrobeniusᴴ * cayleyFrobenius = 2 • 1`
   and rotates `gamma1Op` into `2 • sigmaOp`. -/
theorem serre_kahler_similitude_and_laumon_cayley_rotation
    (X Y : ClTower A 1) {a b : A}
    (ha : star a = a) (hb : star b = b) (hab : a * b = b * a) :
    let F := weilFrobenius a b
    let q := a * a + b * b
    kahlerMetric X Y = Xᴴ * Y ∧
    kahlerSymplectic (F * X) (F * Y) = Xᴴ * (fiberEmbed q * omegaOp) * Y ∧
    kahlerMetric (F * X) (F * Y) = Xᴴ * fiberEmbed q * Y ∧
    (cayleyFrobenius : ClTower A 1)ᴴ * cayleyFrobenius = 2 • (1 : ClTower A 1) ∧
    (cayleyFrobenius : ClTower A 1) * gamma1Op * cayleyFrobeniusᴴ =
      2 • (sigmaOp : ClTower A 1) := by
  have hO2 : (omegaOp : ClTower A 1) * omegaOp = -1 := omegaOp_sq
  have h_met : ∀ (U V : ClTower A 1), kahlerMetric U V = Uᴴ * V := by
    intro U V
    dsimp [kahlerMetric, kahlerSymplectic]
    calc -(Uᴴ * omegaOp * (omegaOp * V))
      _ = -(Uᴴ * (omegaOp * omegaOp) * V) := by noncomm_ring
      _ = -(Uᴴ * (-1) * V) := by rw [hO2]
      _ = Uᴴ * V := by noncomm_ring
  have hF_symp : (weilFrobenius a b)ᴴ * omegaOp * weilFrobenius a b =
      fiberEmbed (a * a + b * b) * omegaOp := by
    apply ext_fin2 <;> simp [weilFrobenius, fiberEmbed, omegaOp, mat2, ha, hb, hab]
  have hF_met : (weilFrobenius a b)ᴴ * weilFrobenius a b =
      fiberEmbed (a * a + b * b) := by
    apply ext_fin2 <;> simp [weilFrobenius, fiberEmbed, mat2, ha, hb, hab, add_comm]
  refine ⟨h_met X Y, ?_, ?_, ?_, ?_⟩
  · dsimp [kahlerSymplectic]
    rw [conjTranspose_mul]
    calc Xᴴ * (weilFrobenius a b)ᴴ * omegaOp * (weilFrobenius a b * Y)
      _ = Xᴴ * ((weilFrobenius a b)ᴴ * omegaOp * weilFrobenius a b) * Y := by noncomm_ring
      _ = Xᴴ * (fiberEmbed (a * a + b * b) * omegaOp) * Y := by rw [hF_symp]
  · rw [h_met, conjTranspose_mul]
    calc Xᴴ * (weilFrobenius a b)ᴴ * (weilFrobenius a b * Y)
      _ = Xᴴ * ((weilFrobenius a b)ᴴ * weilFrobenius a b) * Y := by noncomm_ring
      _ = Xᴴ * fiberEmbed (a * a + b * b) * Y := by rw [hF_met]
  · apply ext_fin2 <;> simp [cayleyFrobenius, omegaOp, mat2, two_smul]
  · apply ext_fin2 <;> simp [cayleyFrobenius, gamma1Op, sigmaOp, omegaOp, mat2, two_smul]

end ArchetypeHR3_SerreKahlerAndLaumonCayley

/-!
## Archetype $\mathcal{H}\mathcal{R}_4$: Deligne's Even-Power Rankin Positivity & Connes' Porous Cutoff Identity
-/

section ArchetypeHR4_DeligneRankinEvenPowerAndConnesCutoff

variable {B : Type*} [Ring B] [StarRing B]

/-- **Deligne's Even-Power Rankin Positivity & Connes' Porous Cutoff Identity ($\mathcal{H}\mathcal{R}_4$)**:
1. `t ^ (2 * m) = star (t ^ m) * (t ^ m)` for self-adjoint `t : B`,
2. For `star U * U = q` and projection `P * P = P`, `star P = P` commuting with `q`,
   `star (P * U * P) * (P * U * P) + star ((1 - P) * U * P) * ((1 - P) * U * P) = q * P`. -/
theorem deligne_rankin_even_power_and_connes_porous_cutoff
    {t U P q : B} (ht : star t = t) (hU : star U * U = q)
    (hP_idem : P * P = P) (hP_sa : star P = P) (hqP : P * q = q * P) (m : ℕ) :
    t ^ (2 * m) = star (t ^ m) * (t ^ m) ∧
    star (P * U * P) * (P * U * P) +
    star ((1 - P) * U * P) * ((1 - P) * U * P) = q * P := by
  refine ⟨?_, ?_⟩
  · rw [star_pow, ht, two_mul, pow_add]
  · have h1P : (1 - P) * (1 - P) = 1 - P := by
      calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
        _ = 1 - P := by rw [hP_idem]; noncomm_ring
    simp only [star_mul, star_sub, star_one, hP_sa]
    calc P * (star U * P) * (P * U * P) +
         P * (star U * (1 - P)) * ((1 - P) * U * P)
      _ = P * star U * (P * P + (1 - P) * (1 - P)) * U * P := by noncomm_ring
      _ = P * star U * (P + (1 - P)) * U * P := by rw [hP_idem, h1P]
      _ = P * (star U * U) * P := by rw [add_sub_cancel]; noncomm_ring
      _ = (P * q) * P := by rw [hU]
      _ = q * (P * P) := by rw [hqP]; noncomm_ring
      _ = q * P := by rw [hP_idem]

private theorem historicalRH_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ x y : ClTower A 1, x * y ≠ y * x := by
  refine ⟨mat2 0 1 0 0, mat2 0 0 1 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [mat2, Matrix.mul_apply, Fin.sum_univ_two] at h00

end ArchetypeHR4_DeligneRankinEvenPowerAndConnesCutoff

end InfoGeometry.Algebra.HistoricalOperatorRiemannHypothesisSynthesis
