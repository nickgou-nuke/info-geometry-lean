/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CliffordDirac.Defect
import InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Native endomorphisms and inner derivations

The existing named Dirac operators receive the unrestricted defect formulas.
The adjoint Lie action supplies genuine inner derivations on the associative
algebra; arbitrary coefficient matrices are not silently called derivations.
-/

noncomputable section

namespace InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis

open InfoGeometry.OperatorAlgebra.CliffordDirac

variable {R Ω : Type*} [CommRing R] [AddCommGroup Ω] [Module R Ω]

theorem diracOperator_sq_with_mixed_commutators {ι : Type*} [Fintype ι]
    (g x : ι → Module.End R Ω) :
    diracOperator g x * diracOperator g x =
      (∑ i, ∑ j, (g i * g j) * (x i * x j)) +
        ∑ i, ∑ j, g i * ⁅x i, g j⁆ * x j :=
  sum_sq_with_mixed_commutators g x

theorem diracOperator₂_sq_with_defect (g h x y : Module.End R Ω)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0) :
    diracOperator₂ g h x y * diracOperator₂ g h x y =
      bochnerLaplacian₂ x y + (g * h) * curvatureCommutator x y +
        g * ⁅x, g⁆ * x + g * ⁅x, h⁆ * y +
        h * ⁅y, g⁆ * x + h * ⁅y, h⁆ * y :=
  clifford_sum_sq_with_defect g h x y hg hh hanti

/-- The sign-flipped hyperbolic Dirac operator, obtained by negating its
second covariant endomorphism. -/
def diracOperator₂_flipped (g h x y : Module.End R Ω) : Module.End R Ω :=
  diracOperator₂ g h x (-y)

/-- The ordered product of the forward and flipped Clifford operators is the
operator difference of squares minus the Clifford bivector times the Jordan
product of the two covariant endomorphisms. The statement is in the full
endomorphism algebra; no scalar or diagonal representation is selected. -/
theorem diracOperator₂_mul_flipped (g h x y : Module.End R Ω)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (hcomm11 : x * g = g * x) (hcomm12 : x * h = h * x)
    (hcomm21 : y * g = g * y) (hcomm22 : y * h = h * y) :
    diracOperator₂ g h x y * diracOperator₂_flipped g h x y =
      (x * x - y * y) - (g * h) * (x * y + y * x) := by
  unfold diracOperator₂_flipped diracOperator₂
  have h21 : h * g = -(g * h) := by
    calc
      h * g = (g * h + h * g) - g * h := by abel
      _ = -(g * h) := by rw [hanti, zero_sub]
  have hgg : (g * x) * (g * x) = x * x := by
    calc
      (g * x) * (g * x) = g * (x * g) * x := by simp only [mul_assoc]
      _ = g * (g * x) * x := by rw [hcomm11]
      _ = (g * g) * (x * x) := by simp only [mul_assoc]
      _ = x * x := by rw [hg, one_mul]
  have hhh : (h * y) * (h * y) = y * y := by
    calc
      (h * y) * (h * y) = h * (y * h) * y := by simp only [mul_assoc]
      _ = h * (h * y) * y := by rw [hcomm22]
      _ = (h * h) * (y * y) := by simp only [mul_assoc]
      _ = y * y := by rw [hh, one_mul]
  have hxy : (g * x) * (h * y) = (g * h) * (x * y) := by
    calc
      (g * x) * (h * y) = g * (x * h) * y := by simp only [mul_assoc]
      _ = g * (h * x) * y := by rw [hcomm12]
      _ = (g * h) * (x * y) := by simp only [mul_assoc]
  have hyx : (h * y) * (g * x) = -((g * h) * (y * x)) := by
    calc
      (h * y) * (g * x) = h * (y * g) * x := by simp only [mul_assoc]
      _ = h * (g * y) * x := by rw [hcomm21]
      _ = (h * g) * (y * x) := by simp only [mul_assoc]
      _ = -((g * h) * (y * x)) := by rw [h21, neg_mul]
  calc
    (g * x + h * y) * (g * x + h * -y) =
        (g * x + h * y) * (g * x - h * y) := by
      simp only [mul_neg, sub_eq_add_neg]
    _ =
        (g * x) * (g * x) - (h * y) * (h * y) +
          ((h * y) * (g * x) - (g * x) * (h * y)) := by noncomm_ring
    _ = (x * x - y * y) - (g * h) * (x * y + y * x) := by
      rw [hgg, hhh, hyx, hxy]
      noncomm_ring

/-- Reversing the order of the two hyperbolic Dirac factors reverses the
operator-valued Jordan strain term while preserving the difference-of-squares
term. -/
theorem diracOperator₂_flipped_mul (g h x y : Module.End R Ω)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (hcomm11 : x * g = g * x) (hcomm12 : x * h = h * x)
    (hcomm21 : y * g = g * y) (hcomm22 : y * h = h * y) :
    diracOperator₂_flipped g h x y * diracOperator₂ g h x y =
      (x * x - y * y) + (g * h) * (x * y + y * x) := by
  unfold diracOperator₂_flipped diracOperator₂
  have h21 : h * g = -(g * h) := by
    calc
      h * g = (g * h + h * g) - g * h := by abel
      _ = -(g * h) := by rw [hanti, zero_sub]
  have hgg : (g * x) * (g * x) = x * x := by
    calc
      (g * x) * (g * x) = g * (x * g) * x := by simp only [mul_assoc]
      _ = g * (g * x) * x := by rw [hcomm11]
      _ = (g * g) * (x * x) := by simp only [mul_assoc]
      _ = x * x := by rw [hg, one_mul]
  have hhh : (h * y) * (h * y) = y * y := by
    calc
      (h * y) * (h * y) = h * (y * h) * y := by simp only [mul_assoc]
      _ = h * (h * y) * y := by rw [hcomm22]
      _ = (h * h) * (y * y) := by simp only [mul_assoc]
      _ = y * y := by rw [hh, one_mul]
  have hxy : (g * x) * (h * y) = (g * h) * (x * y) := by
    calc
      (g * x) * (h * y) = g * (x * h) * y := by simp only [mul_assoc]
      _ = g * (h * x) * y := by rw [hcomm12]
      _ = (g * h) * (x * y) := by simp only [mul_assoc]
  have hyx : (h * y) * (g * x) = -((g * h) * (y * x)) := by
    calc
      (h * y) * (g * x) = h * (y * g) * x := by simp only [mul_assoc]
      _ = h * (g * y) * x := by rw [hcomm21]
      _ = (h * g) * (y * x) := by simp only [mul_assoc]
      _ = -((g * h) * (y * x)) := by rw [h21, neg_mul]
  calc
    (g * x + h * -y) * (g * x + h * y) =
        (g * x - h * y) * (g * x + h * y) := by
      simp only [mul_neg, sub_eq_add_neg]
    _ =
        (g * x) * (g * x) - (h * y) * (h * y) +
          ((g * x) * (h * y) - (h * y) * (g * x)) := by noncomm_ring
    _ = (x * x - y * y) + (g * h) * (x * y + y * x) := by
      rw [hgg, hhh, hxy, hyx]
      noncomm_ring

end InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis

namespace InfoGeometry.OperatorAlgebra.CliffordDirac

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The native adjoint Lie action also satisfies the associative Leibniz rule. -/
theorem inner_ad_leibniz (a x y : A) :
    LieAlgebra.ad R A a (x * y) =
      LieAlgebra.ad R A a x * y + x * LieAlgebra.ad R A a y := by
  simp only [LieAlgebra.ad_apply, Ring.lie_def]
  noncomm_ring

/-- The mixed connection defect is left multiplication by the coefficient bracket. -/
theorem inner_ad_lmul_commutator (a b : A) :
    ⁅LieAlgebra.ad R A a, Algebra.lmul R A b⁆ = Algebra.lmul R A ⁅a, b⁆ := by
  apply LinearMap.ext
  intro z
  change (a * (b * z) - (b * z) * a) - b * (a * z - z * a) = (a * b - b * a) * z
  noncomm_ring

theorem inner_ad_lmul_commute_iff (a b : A) :
    Commute (LieAlgebra.ad R A a) (Algebra.lmul R A b) ↔ Commute a b := by
  rw [commute_iff_lie_eq, inner_ad_lmul_commutator, commute_iff_lie_eq]
  constructor
  · intro h
    apply Algebra.lmul_injective (R := R)
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- The square of a Clifford sum of actual inner derivations.
The curvature term is the native adjoint of the coefficient commutator. -/
theorem inner_dirac_sq (g h a b : A)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (cga : Commute g a) (cgb : Commute g b)
    (cha : Commute h a) (chb : Commute h b) :
    let D := InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis.diracOperator₂
      (Algebra.lmul R A g) (Algebra.lmul R A h) (LieAlgebra.ad R A a) (LieAlgebra.ad R A b)
    D * D =
      LieAlgebra.ad R A a * LieAlgebra.ad R A a +
      LieAlgebra.ad R A b * LieAlgebra.ad R A b +
      Algebra.lmul R A (g * h) * LieAlgebra.ad R A ⁅a, b⁆ := by
  have hlg : Algebra.lmul R A g * Algebra.lmul R A g = 1 := by
    rw [← map_mul, hg, map_one]
  have hlh : Algebra.lmul R A h * Algebra.lmul R A h = 1 := by
    rw [← map_mul, hh, map_one]
  have hla : Algebra.lmul R A g * Algebra.lmul R A h +
      Algebra.lmul R A h * Algebra.lmul R A g = 0 := by
    rw [← map_mul, ← map_mul, ← map_add, hanti, map_zero]
  have caa := (inner_ad_lmul_commute_iff (R := R) a g).2 cga.symm
  have cab := (inner_ad_lmul_commute_iff (R := R) a h).2 cha.symm
  have cba := (inner_ad_lmul_commute_iff (R := R) b g).2 cgb.symm
  have cbb := (inner_ad_lmul_commute_iff (R := R) b h).2 chb.symm
  have hs := InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis.diracOperator₂_sq_weitzenbock
      (Algebra.lmul R A g) (Algebra.lmul R A h) (LieAlgebra.ad R A a) (LieAlgebra.ad R A b)
      hlg hlh hla caa.eq cab.eq cba.eq cbb.eq
  change _ = _
  rw [hs]
  change _ + (Algebra.lmul R A g * Algebra.lmul R A h) *
    ⁅LieAlgebra.ad R A a, LieAlgebra.ad R A b⁆ = _
  rw [← map_mul, ← (LieAlgebra.ad R A).map_lie]
  rfl

end InfoGeometry.OperatorAlgebra.CliffordDirac
