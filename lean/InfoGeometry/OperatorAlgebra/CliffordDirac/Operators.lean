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
