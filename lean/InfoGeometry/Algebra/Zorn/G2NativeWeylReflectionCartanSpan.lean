import InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2NativeWeylReflectionCartanSpan

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
open InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionStandardDerivation

theorem realWeylReflection_maps_nativeCartanSpan
    {D : ZornVectorMatrix.Derivation (R := ℝ)} (hD : D ∈ nativeCartanSpan) :
    conjugateNativeDerivation realWeylReflection D ∈ nativeCartanSpan := by
  have h0 : conjugateNativeDerivation realWeylReflection (cartanDerivation 0) ∈ nativeCartanSpan := by
    have hrepr : cartanDerivation 0 = (1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (-1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by module
    rw [hrepr]
    change conjugateNativeDerivationLinear realWeylReflection _ ∈ _
    have hA : conjugateNativeDerivationLinear realWeylReflection
        (cartanDerivation 0 + cartanDerivation 1) = -(cartanDerivation 0 + cartanDerivation 1) := by
      simpa [conjugateNativeDerivationLinear_apply] using realWeylReflection_cartanPair_zero
    have hB : conjugateNativeDerivationLinear realWeylReflection
        ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
        (-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1 := by
      simpa [conjugateNativeDerivationLinear_apply] using realWeylReflection_cartanPair_one
    have hcalc : conjugateNativeDerivationLinear realWeylReflection
          ((1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
            (-1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1)) =
        (1 / 3 : ℝ) • (-(cartanDerivation 0 + cartanDerivation 1)) +
          (-1 / 3 : ℝ) • ((-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1) := by
      calc
        _ = (1 / 3 : ℝ) • conjugateNativeDerivationLinear realWeylReflection
              (cartanDerivation 0 + cartanDerivation 1) +
            (-1 / 3 : ℝ) • conjugateNativeDerivationLinear realWeylReflection
              ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
          simp only [map_add, map_smul]
        _ = _ := by rw [hA, hB]
    rw [hcalc]
    have h0mem : cartanDerivation 0 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} : Set _)) (by simp)
    have h1mem : cartanDerivation 1 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} : Set _)) (by simp)
    have hA_mem := nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem (-1 : ℝ) h0mem) (nativeCartanSpan.smul_mem (-1 : ℝ) h1mem)
    have hB_mem := nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem (-1 : ℝ) h0mem) (nativeCartanSpan.smul_mem (2 : ℝ) h1mem)
    convert nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem (1 / 3 : ℝ) hA_mem)
      (nativeCartanSpan.smul_mem (-1 / 3 : ℝ) hB_mem) using 1; module
  have h1 : conjugateNativeDerivation realWeylReflection (cartanDerivation 1) ∈ nativeCartanSpan := by
    have hrepr : cartanDerivation 1 = (2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by module
    rw [hrepr]
    change conjugateNativeDerivationLinear realWeylReflection _ ∈ _
    have hA : conjugateNativeDerivationLinear realWeylReflection
        (cartanDerivation 0 + cartanDerivation 1) = -(cartanDerivation 0 + cartanDerivation 1) := by
      simpa [conjugateNativeDerivationLinear_apply] using realWeylReflection_cartanPair_zero
    have hB : conjugateNativeDerivationLinear realWeylReflection
        ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
        (-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1 := by
      simpa [conjugateNativeDerivationLinear_apply] using realWeylReflection_cartanPair_one
    have hcalc : conjugateNativeDerivationLinear realWeylReflection
          ((2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
            (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1)) =
        (2 / 3 : ℝ) • (-(cartanDerivation 0 + cartanDerivation 1)) +
          (1 / 3 : ℝ) • ((-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1) := by
      calc
        _ = (2 / 3 : ℝ) • conjugateNativeDerivationLinear realWeylReflection
              (cartanDerivation 0 + cartanDerivation 1) +
            (1 / 3 : ℝ) • conjugateNativeDerivationLinear realWeylReflection
              ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
          simp only [map_add, map_smul]
        _ = _ := by rw [hA, hB]
    rw [hcalc]
    have h0mem : cartanDerivation 0 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} : Set _)) (by simp)
    have h1mem : cartanDerivation 1 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} : Set _)) (by simp)
    have hA_mem := nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem (-1 : ℝ) h0mem) (nativeCartanSpan.smul_mem (-1 : ℝ) h1mem)
    have hB_mem := nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem (-1 : ℝ) h0mem) (nativeCartanSpan.smul_mem (2 : ℝ) h1mem)
    convert nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem (2 / 3 : ℝ) hA_mem)
      (nativeCartanSpan.smul_mem (1 / 3 : ℝ) hB_mem) using 1; module
  refine Submodule.span_induction (p := fun E _ =>
      conjugateNativeDerivation realWeylReflection E ∈ nativeCartanSpan) ?_ ?_ ?_ ?_ hD
  · intro E hE
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hE
    rcases hE with rfl | rfl
    · exact h0
    · exact h1
  · change conjugateNativeDerivationLinear realWeylReflection 0 ∈ nativeCartanSpan
    simpa only [map_zero] using nativeCartanSpan.zero_mem
  · intro E F _ _ hE hF
    simpa only [map_add] using nativeCartanSpan.add_mem hE hF
  · intro a E _ hE
    simpa only [map_smul] using nativeCartanSpan.smul_mem a hE

end InfoGeometry.Algebra.Zorn.G2NativeWeylReflectionCartanSpan
