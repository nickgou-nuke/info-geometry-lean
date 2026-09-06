import InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport

/-!
# Linear Cartan action for the real Weyl generators

This owner packages the verified native Cartan basis readbacks into the
linear action on arbitrary elements of the two-dimensional Cartan span.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-! Explicit parameter bridge for the Cartan readback layer. -/

theorem parameterDerivation_eq_parameterLinearEquiv (p : Params) :
    parameterDerivation p = parameterLinearEquiv p := rfl

@[simp] theorem parameterLinearEquiv_symm_parameterDerivation (p : Params) :
    parameterLinearEquiv.symm (parameterDerivation p) = p := by
  exact parameterLinearEquiv.left_inv p

theorem derivationParameters_parameterDerivation_public (p : Params) :
    derivationParameters (parameterDerivation p) = p := by
  exact parameterLinearEquiv.left_inv p

theorem realWeylCycle_cartanPair_zero :
    conjugateNativeDerivation realWeylCycle
        (cartanDerivation 0 + cartanDerivation 1) =
      (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 :=
  realWeylCycle_cartanPair_zero_verified

theorem realWeylCycle_cartanPair_one :
    conjugateNativeDerivation realWeylCycle
        ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
      cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1 :=
  realWeylCycle_cartanPair_one_verified

theorem realWeylReflection_cartanPair_zero :
    conjugateNativeDerivation realWeylReflection
        (cartanDerivation 0 + cartanDerivation 1) =
      -(cartanDerivation 0 + cartanDerivation 1) :=
  realWeylReflection_cartanPair_zero_verified

theorem realWeylReflection_cartanPair_one :
    conjugateNativeDerivation realWeylReflection
        ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
      (-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1 := by
  rw [← U1V1_innerDerivation_eq_cartanDerivation_combination]
  rw [realWeylReflection_U1V1_pair_readback]
  change NativeStanDerivationBilinear.innerDerivation
      (canonicalVectorEquiv (canonicalV 2))
      (canonicalVectorEquiv (canonicalU 2)) = _
  rw [NativeStanDerivationBilinear.innerDerivation_swap]
  rw [U2V2_innerDerivation_eq_cartanDerivation_combination]
  module

def nativeCartanSpan : Submodule ℝ (ZornVectorMatrix.Derivation (R := ℝ)) :=
  Submodule.span ℝ
    ({cartanDerivation 0, cartanDerivation 1} : Set (ZornVectorMatrix.Derivation (R := ℝ)))

theorem realWeylCycle_maps_nativeCartanSpan
    {D : ZornVectorMatrix.Derivation (R := ℝ)} (hD : D ∈ nativeCartanSpan) :
    conjugateNativeDerivation realWeylCycle D ∈ nativeCartanSpan := by
  have h0 : conjugateNativeDerivation realWeylCycle (cartanDerivation 0) ∈ nativeCartanSpan := by
    have hrepr : cartanDerivation 0 = (1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (-1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by module
    rw [hrepr]
    change conjugateNativeDerivationLinear realWeylCycle
      ((1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (-1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1)) ∈ _
    have hA : conjugateNativeDerivationLinear realWeylCycle
        (cartanDerivation 0 + cartanDerivation 1) =
        (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
      simpa [conjugateNativeDerivationLinear_apply] using realWeylCycle_cartanPair_zero
    have hB : conjugateNativeDerivationLinear realWeylCycle
        ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
        cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1 := by
      simpa [conjugateNativeDerivationLinear_apply] using realWeylCycle_cartanPair_one
    have hcalc : conjugateNativeDerivationLinear realWeylCycle
          ((1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
            (-1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1)) =
        (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) +
          (-1 / 3 : ℝ) • (cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1) := by
      calc
        _ = (1 / 3 : ℝ) •
              conjugateNativeDerivationLinear realWeylCycle
                (cartanDerivation 0 + cartanDerivation 1) +
            (-1 / 3 : ℝ) •
              conjugateNativeDerivationLinear realWeylCycle
                ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
          simp only [map_add, map_smul]
        _ = _ := by rw [hA, hB]
    rw [hcalc]
    have h0mem : cartanDerivation 0 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} :
        Set (ZornVectorMatrix.Derivation (R := ℝ)))) (by simp)
    have h1mem : cartanDerivation 1 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} :
        Set (ZornVectorMatrix.Derivation (R := ℝ)))) (by simp)
    have hBmem : (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 ∈ nativeCartanSpan :=
      nativeCartanSpan.add_mem (nativeCartanSpan.smul_mem _ h0mem) h1mem
    have hCmem : cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1 ∈ nativeCartanSpan :=
      nativeCartanSpan.add_mem h0mem (nativeCartanSpan.smul_mem _ h1mem)
    convert nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem _ hBmem)
      (nativeCartanSpan.smul_mem _ hCmem) using 1
  have h1 : conjugateNativeDerivation realWeylCycle (cartanDerivation 1) ∈ nativeCartanSpan := by
    have hrepr : cartanDerivation 1 = (2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by module
    rw [hrepr]
    change conjugateNativeDerivationLinear realWeylCycle
      ((2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1)) ∈ _
    have hA : conjugateNativeDerivationLinear realWeylCycle
        (cartanDerivation 0 + cartanDerivation 1) =
        (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
      simpa [conjugateNativeDerivationLinear_apply] using realWeylCycle_cartanPair_zero
    have hB : conjugateNativeDerivationLinear realWeylCycle
        ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
        cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1 := by
      simpa [conjugateNativeDerivationLinear_apply] using realWeylCycle_cartanPair_one
    have hcalc : conjugateNativeDerivationLinear realWeylCycle
          ((2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
            (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1)) =
        (2 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) +
          (1 / 3 : ℝ) • (cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1) := by
      calc
        _ = (2 / 3 : ℝ) •
              conjugateNativeDerivationLinear realWeylCycle
                (cartanDerivation 0 + cartanDerivation 1) +
            (1 / 3 : ℝ) •
              conjugateNativeDerivationLinear realWeylCycle
                ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
          simp only [map_add, map_smul]
        _ = _ := by rw [hA, hB]
    rw [hcalc]
    have h0mem : cartanDerivation 0 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} :
        Set (ZornVectorMatrix.Derivation (R := ℝ)))) (by simp)
    have h1mem : cartanDerivation 1 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} :
        Set (ZornVectorMatrix.Derivation (R := ℝ)))) (by simp)
    have hBmem : (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 ∈ nativeCartanSpan :=
      nativeCartanSpan.add_mem (nativeCartanSpan.smul_mem _ h0mem) h1mem
    have hCmem : cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1 ∈ nativeCartanSpan :=
      nativeCartanSpan.add_mem h0mem (nativeCartanSpan.smul_mem _ h1mem)
    convert nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem _ hBmem)
      (nativeCartanSpan.smul_mem _ hCmem) using 1
  refine Submodule.span_induction (p := fun E _ =>
      conjugateNativeDerivation realWeylCycle E ∈ nativeCartanSpan) ?_ ?_ ?_ ?_ hD
  · intro E hE
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hE
    rcases hE with rfl | rfl
    · exact h0
    · exact h1
  · change conjugateNativeDerivationLinear realWeylCycle 0 ∈ nativeCartanSpan
    simpa only [map_zero] using nativeCartanSpan.zero_mem
  · intro E F _ _ hE hF
    simpa only [map_add] using nativeCartanSpan.add_mem hE hF
  · intro a E _ hE
    simpa only [map_smul] using nativeCartanSpan.smul_mem a hE

/-
theorem realWeylReflection_maps_nativeCartanSpan
    {D : ZornVectorMatrix.Derivation (R := ℝ)} (hD : D ∈ nativeCartanSpan) :
    conjugateNativeDerivation realWeylReflection D ∈ nativeCartanSpan := by
  have h0 : conjugateNativeDerivation realWeylReflection (cartanDerivation 0) ∈
      nativeCartanSpan := by
    have hrepr : cartanDerivation 0 =
        (1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
          (-1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
      module
    rw [hrepr]
    change conjugateNativeDerivationLinear realWeylReflection _ ∈ _
    have hA : conjugateNativeDerivationLinear realWeylReflection
          (cartanDerivation 0 + cartanDerivation 1) =
        -(cartanDerivation 0 + cartanDerivation 1) := by
      simpa [conjugateNativeDerivationLinear_apply] using
        realWeylReflection_cartanPair_zero
    have hB : conjugateNativeDerivationLinear realWeylReflection
          ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
        (-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1 := by
      simpa [conjugateNativeDerivationLinear_apply] using
        realWeylReflection_cartanPair_one
    have hcalc : conjugateNativeDerivationLinear realWeylReflection
          ((1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
            (-1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1)) =
        (1 / 3 : ℝ) • (-(cartanDerivation 0 + cartanDerivation 1)) +
          (-1 / 3 : ℝ) • ((-1 : ℝ) • cartanDerivation 0 +
            2 • cartanDerivation 1) := by
      calc
        _ = (1 / 3 : ℝ) • conjugateNativeDerivationLinear realWeylReflection
              (cartanDerivation 0 + cartanDerivation 1) +
            (-1 / 3 : ℝ) • conjugateNativeDerivationLinear realWeylReflection
              ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
          simp only [map_add, map_smul]
        _ = _ := by rw [hA, hB]
    rw [hcalc]
    have h0mem : cartanDerivation 0 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} :
        Set (ZornVectorMatrix.Derivation (R := ℝ)))) (by simp)
    have h1mem : cartanDerivation 1 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} :
        Set (ZornVectorMatrix.Derivation (R := ℝ)))) (by simp)
    have hsum := nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem (-1 : ℝ) h0mem) h1mem
    have hsum' := nativeCartanSpan.add_mem h0mem
      (nativeCartanSpan.smul_mem (-2 : ℝ) h1mem)
    convert nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem _ hsum)
      (nativeCartanSpan.smul_mem _ hsum') using 1 <;> module
  have h1 : conjugateNativeDerivation realWeylReflection (cartanDerivation 1) ∈
      nativeCartanSpan := by
    have hrepr : cartanDerivation 1 =
        (2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
          (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
      module
    rw [hrepr]
    change conjugateNativeDerivationLinear realWeylReflection _ ∈ _
    have hA : conjugateNativeDerivationLinear realWeylReflection
          (cartanDerivation 0 + cartanDerivation 1) =
        -(cartanDerivation 0 + cartanDerivation 1) := by
      simpa [conjugateNativeDerivationLinear_apply] using
        realWeylReflection_cartanPair_zero
    have hB : conjugateNativeDerivationLinear realWeylReflection
          ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
        (-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1 := by
      simpa [conjugateNativeDerivationLinear_apply] using
        realWeylReflection_cartanPair_one
    have hcalc : conjugateNativeDerivationLinear realWeylReflection
          ((2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
            (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1)) =
        (2 / 3 : ℝ) • (-(cartanDerivation 0 + cartanDerivation 1)) +
          (1 / 3 : ℝ) • ((-1 : ℝ) • cartanDerivation 0 +
            2 • cartanDerivation 1) := by
      calc
        _ = (2 / 3 : ℝ) • conjugateNativeDerivationLinear realWeylReflection
              (cartanDerivation 0 + cartanDerivation 1) +
            (1 / 3 : ℝ) • conjugateNativeDerivationLinear realWeylReflection
              ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
          simp only [map_add, map_smul]
        _ = _ := by rw [hA, hB]
    rw [hcalc]
    have h0mem : cartanDerivation 0 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} :
        Set (ZornVectorMatrix.Derivation (R := ℝ)))) (by simp)
    have h1mem : cartanDerivation 1 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} :
        Set (ZornVectorMatrix.Derivation (R := ℝ)))) (by simp)
    have hsum : (1 : ℝ) • cartanDerivation 0 + cartanDerivation 1 ∈
        nativeCartanSpan := nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem (1 : ℝ) h0mem) h1mem
    have hsum' : cartanDerivation 0 + (2 : ℝ) • cartanDerivation 1 ∈
        nativeCartanSpan := nativeCartanSpan.add_mem h0mem
      (nativeCartanSpan.smul_mem (2 : ℝ) h1mem)
    convert nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem _ hsum)
      (nativeCartanSpan.smul_mem _ hsum') using 1 <;> module
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

/-! The span restriction now has an explicit action on its native basis. -/

theorem realWeylCycle_cartanDerivation_zero :
    conjugateNativeDerivation realWeylCycle (cartanDerivation 0) =
      -(cartanDerivation 0) + cartanDerivation 1 := by
  have hA := realWeylCycle_cartanPair_zero
  have hB := realWeylCycle_cartanPair_one
  have h0 : cartanDerivation 0 =
      (1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (-1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
    module
  rw [h0]
  change conjugateNativeDerivationLinear realWeylCycle _ = _
  rw [map_add, map_smul]
  rw [show conjugateNativeDerivationLinear realWeylCycle
      (cartanDerivation 0 + cartanDerivation 1) =
        (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 by
    simpa [conjugateNativeDerivationLinear_apply] using hA]
  rw [show conjugateNativeDerivationLinear realWeylCycle
      ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
        cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1 by
    simpa [conjugateNativeDerivationLinear_apply] using hB]
  module

theorem realWeylCycle_cartanDerivation_one :
    conjugateNativeDerivation realWeylCycle (cartanDerivation 1) =
      -(cartanDerivation 0) := by
  have hA := realWeylCycle_cartanPair_zero
  have hB := realWeylCycle_cartanPair_one
  have h1 : cartanDerivation 1 =
      (2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
    module
  rw [h1]
  change conjugateNativeDerivationLinear realWeylCycle _ = _
  rw [map_add, map_smul]
  rw [show conjugateNativeDerivationLinear realWeylCycle
      (cartanDerivation 0 + cartanDerivation 1) =
        (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 by
    simpa [conjugateNativeDerivationLinear_apply] using hA]
  rw [show conjugateNativeDerivationLinear realWeylCycle
      ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
        cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1 by
    simpa [conjugateNativeDerivationLinear_apply] using hB]
  module

theorem realWeylReflection_cartanDerivation_zero :
    conjugateNativeDerivation realWeylReflection (cartanDerivation 0) =
      (1 / 3 : ℝ) • cartanDerivation 0 +
        (-2 / 3 : ℝ) • cartanDerivation 1 := by
  have hA := realWeylReflection_cartanPair_zero
  have hB := realWeylReflection_cartanPair_one
  have h0 : cartanDerivation 0 =
      (1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (-1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
    module
  rw [h0]
  change conjugateNativeDerivationLinear realWeylReflection _ = _
  rw [map_add, map_smul]
  rw [show conjugateNativeDerivationLinear realWeylReflection
      (cartanDerivation 0 + cartanDerivation 1) =
        -(cartanDerivation 0 + cartanDerivation 1) by
    simpa [conjugateNativeDerivationLinear_apply] using hA]
  rw [show conjugateNativeDerivationLinear realWeylReflection
      ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
        (-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1 by
    simpa [conjugateNativeDerivationLinear_apply] using hB]
  module

theorem realWeylReflection_cartanDerivation_one :
    conjugateNativeDerivation realWeylReflection (cartanDerivation 1) =
      (-4 / 3 : ℝ) • cartanDerivation 0 +
        (-1 / 3 : ℝ) • cartanDerivation 1 := by
  have hA := realWeylReflection_cartanPair_zero
  have hB := realWeylReflection_cartanPair_one
  have h1 : cartanDerivation 1 =
      (2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by
    module
  rw [h1]
  change conjugateNativeDerivationLinear realWeylReflection _ = _
  rw [map_add, map_smul]
  rw [show conjugateNativeDerivationLinear realWeylReflection
      (cartanDerivation 0 + cartanDerivation 1) =
        -(cartanDerivation 0 + cartanDerivation 1) by
    simpa [conjugateNativeDerivationLinear_apply] using hA]
  rw [show conjugateNativeDerivationLinear realWeylReflection
      ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
        (-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1 by
    simpa [conjugateNativeDerivationLinear_apply] using hB]
  module

noncomputable def realWeylCycle_nativeCartanSpanLinearMap :
    nativeCartanSpan →ₗ[ℝ] nativeCartanSpan where
  toFun D := ⟨conjugateNativeDerivation realWeylCycle D, realWeylCycle_maps_nativeCartanSpan D.property⟩
  map_add' D E := by
    apply Subtype.ext
    change conjugateNativeDerivation realWeylCycle (D + E) = _
    change conjugateNativeDerivationLinear realWeylCycle (D + E) = _
    simp only [map_add, conjugateNativeDerivationLinear_apply]
  map_smul' r D := by
    apply Subtype.ext
    change conjugateNativeDerivation realWeylCycle (r • D) = _
    change conjugateNativeDerivationLinear realWeylCycle (r • D) = _
    simp only [map_smul, conjugateNativeDerivationLinear_apply]

noncomputable def realWeylReflection_nativeCartanSpanLinearMap :
    nativeCartanSpan →ₗ[ℝ] nativeCartanSpan where
  toFun D := ⟨conjugateNativeDerivation realWeylReflection D, realWeylReflection_maps_nativeCartanSpan D.property⟩
  map_add' D E := by
    apply Subtype.ext
    change conjugateNativeDerivation realWeylReflection (D + E) = _
    change conjugateNativeDerivationLinear realWeylReflection (D + E) = _
    simp only [map_add, conjugateNativeDerivationLinear_apply]
  map_smul' r D := by
    apply Subtype.ext
    change conjugateNativeDerivation realWeylReflection (r • D) = _
    change conjugateNativeDerivationLinear realWeylReflection (r • D) = _
    simp only [map_smul, conjugateNativeDerivationLinear_apply]

@[simp] theorem realWeylCycle_nativeCartanSpanLinearMap_basis_zero
    (h0 : cartanDerivation 0 ∈ nativeCartanSpan) :
    (realWeylCycle_nativeCartanSpanLinearMap ⟨cartanDerivation 0, h0⟩).1 =
      -(cartanDerivation 0) + cartanDerivation 1 := by
  exact realWeylCycle_cartanDerivation_zero

@[simp] theorem realWeylCycle_nativeCartanSpanLinearMap_basis_one
    (h1 : cartanDerivation 1 ∈ nativeCartanSpan) :
    (realWeylCycle_nativeCartanSpanLinearMap ⟨cartanDerivation 1, h1⟩).1 =
      -(cartanDerivation 0) := by
  exact realWeylCycle_cartanDerivation_one

@[simp] theorem realWeylReflection_nativeCartanSpanLinearMap_basis_zero
    (h0 : cartanDerivation 0 ∈ nativeCartanSpan) :
    (realWeylReflection_nativeCartanSpanLinearMap ⟨cartanDerivation 0, h0⟩).1 =
      (1 / 3 : ℝ) • cartanDerivation 0 +
        (-2 / 3 : ℝ) • cartanDerivation 1 := by
  exact realWeylReflection_cartanDerivation_zero

@[simp] theorem realWeylReflection_nativeCartanSpanLinearMap_basis_one
    (h1 : cartanDerivation 1 ∈ nativeCartanSpan) :
    (realWeylReflection_nativeCartanSpanLinearMap ⟨cartanDerivation 1, h1⟩).1 =
      (-4 / 3 : ℝ) • cartanDerivation 0 +
        (-1 / 3 : ℝ) • cartanDerivation 1 := by
  exact realWeylReflection_cartanDerivation_one

theorem realWeylCycle_cartan_linear_combination (a b : ℝ) :
    conjugateNativeDerivation realWeylCycle
        (a • cartanDerivation 0 + b • cartanDerivation 1) =
      a • (-(cartanDerivation 0) + cartanDerivation 1) +
        b • (-(cartanDerivation 0)) := by
  change conjugateNativeDerivationLinear realWeylCycle _ = _
  simp only [map_add, map_smul]
  rw [realWeylCycle_cartanDerivation_zero,
    realWeylCycle_cartanDerivation_one]

theorem realWeylReflection_cartan_linear_combination (a b : ℝ) :
    conjugateNativeDerivation realWeylReflection
        (a • cartanDerivation 0 + b • cartanDerivation 1) =
      a • ((1 / 3 : ℝ) • cartanDerivation 0 +
        (-2 / 3 : ℝ) • cartanDerivation 1) +
        b • ((-4 / 3 : ℝ) • cartanDerivation 0 +
          (-1 / 3 : ℝ) • cartanDerivation 1) := by
  change conjugateNativeDerivationLinear realWeylReflection _ = _
  simp only [map_add, map_smul]
  rw [realWeylReflection_cartanDerivation_zero,
    realWeylReflection_cartanDerivation_one]

theorem realWeylCycle_conjugatedCartanParameters_is_cartan :
    ∀ j : Fin 2,
      conjugatedCartanParameters realWeylCycle j =
        conjugatedCartanParameters realWeylCycle j 6 •
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          conjugatedCartanParameters realWeylCycle j 13 •
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  intro j
  exact conjugatedCartanParameters_cycle_eq_cartan_coordinates j

theorem realWeylReflection_conjugatedCartanParameters_is_cartan :
    ∀ j : Fin 2,
      conjugatedCartanParameters realWeylReflection j =
        conjugatedCartanParameters realWeylReflection j 6 •
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          conjugatedCartanParameters realWeylReflection j 13 •
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  intro j
  exact conjugatedCartanParameters_reflection_eq_cartan_coordinates j

theorem conjugatedCartanParameters_eq_conjugatedParameterLinearMap
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (j : Fin 2) :
    conjugatedCartanParameters φ j =
      conjugatedParameterLinearMap φ
        (derivationParameters (cartanDerivation j)) := by
  unfold conjugatedCartanParameters conjugatedParameterLinearMap
  rfl

theorem realWeylCycle_cartan_parameter_action (j : Fin 2) :
    conjugatedCartanParameters realWeylCycle j =
      cycleCartanParameterAction (derivationParameters (cartanDerivation j)) := by
  rw [conjugatedCartanParameters_eq_conjugatedParameterLinearMap]
  apply conjugatedParameterLinearMap_cycle_eq_cycleCartanParameterAction_on_cartanParameterPlane
  fin_cases j
  · change derivationParameters (parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 6)) ∈ _
    rw [parameterLinearEquiv.left_inv]
    apply Submodule.subset_span
    simp [cartanParameterPlane]
  · change derivationParameters (parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 13)) ∈ _
    rw [parameterLinearEquiv.left_inv]
    apply Submodule.subset_span
    simp [cartanParameterPlane]

theorem realWeylReflection_cartan_parameter_action (j : Fin 2) :
    conjugatedCartanParameters realWeylReflection j =
      reflectionCartanParameterAction (derivationParameters (cartanDerivation j)) := by
  rw [conjugatedCartanParameters_eq_conjugatedParameterLinearMap]
  apply conjugatedParameterLinearMap_reflection_eq_reflectionCartanParameterAction_on_cartanParameterPlane
  fin_cases j
  · change derivationParameters (parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 6)) ∈ _
    rw [parameterLinearEquiv.left_inv]
    apply Submodule.subset_span
    simp [cartanParameterPlane]
  · change derivationParameters (parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 13)) ∈ _
    rw [parameterLinearEquiv.left_inv]
    apply Submodule.subset_span
    simp [cartanParameterPlane]

noncomputable def canonicalCartanRestrictionEquiv
    (L : canonicalZornDerivations ≃ₗ[ℝ] canonicalZornDerivations)
    (hL : ∀ D ∈ canonicalCartanParameterPlane,
      L D ∈ canonicalCartanParameterPlane)
    (hLinv : ∀ D ∈ canonicalCartanParameterPlane,
      L.symm D ∈ canonicalCartanParameterPlane) :
    canonicalCartanParameterPlane ≃ₗ[ℝ] canonicalCartanParameterPlane := by
  let f : canonicalCartanParameterPlane →ₗ[ℝ] canonicalCartanParameterPlane :=
    { toFun := fun D => ⟨L D, hL D D.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact L.map_add x y
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact L.map_smul a x }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply L.injective
    exact congrArg (fun z : canonicalCartanParameterPlane => (z : canonicalZornDerivations)) hxy
  · intro y
    refine ⟨⟨L.symm y, hLinv y y.property⟩, ?_⟩
    apply Subtype.ext
    exact L.apply_symm_apply y

noncomputable def realWeylCycle_canonicalCartanRestriction :
    canonicalCartanParameterPlane ≃ₗ[ℝ] canonicalCartanParameterPlane :=
  canonicalCartanRestrictionEquiv
    (conjugateCanonicalDerivation realWeylCycle)
    (fun D hD => realWeylCycle_maps_canonicalCartanParameterPlane hD)
    (fun D hD => conjugateCanonicalDerivation_symm_mem_canonicalCartanParameterPlane
      realWeylCycle
      (fun D hD => realWeylCycle_maps_canonicalCartanParameterPlane hD) hD)

noncomputable def realWeylReflection_canonicalCartanRestriction :
    canonicalCartanParameterPlane ≃ₗ[ℝ] canonicalCartanParameterPlane :=
  canonicalCartanRestrictionEquiv
    (conjugateCanonicalDerivation realWeylReflection)
    (fun D hD => realWeylReflection_maps_canonicalCartanParameterPlane hD)
    (fun D hD => conjugateCanonicalDerivation_symm_mem_canonicalCartanParameterPlane
      realWeylReflection
      (fun D hD => realWeylReflection_maps_canonicalCartanParameterPlane hD) hD)

theorem native_rootSpace_transport_of_cartan_normalizer
    (i j : nonzeroIndex)
    (e : Der ≃ₗ[ℝ] Der)
    (c : axialCartanLieSubalgebra ≃ₗ[ℝ] axialCartanLieSubalgebra)
    (hbracket : ∀ X Y, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (hcartan : ∀ H : axialCartanLieSubalgebra,
      e (H : Der) = ((c H : axialCartanLieSubalgebra) : Der))
    (hweight : ∀ H : axialCartanLieSubalgebra,
      nativeRootWeight i (c.symm H) = nativeRootWeight j H)
    (D : Der)
    (hD : ∀ H : axialCartanLieSubalgebra,
      ⁅(H : Der), D⁆ = nativeRootWeight i H • D) :
    e D ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra
      (nativeRootWeight j) := by
  exact LinearEquiv.map_rootSpace_mem_of_cartan_normalizer
    i j e c hbracket hcartan hweight D hD

noncomputable def axialCartan_toSubmodule_equiv :
    axialCartanLieSubalgebra ≃ₗ[ℝ]
      axialCartanLieSubalgebra.toSubmodule := by
  let f : axialCartanLieSubalgebra →ₗ[ℝ]
      axialCartanLieSubalgebra.toSubmodule :=
    { toFun := fun H => ⟨H.1, H.2⟩
      map_add' := by intro H K; rfl
      map_smul' := by intro a H; rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · intro H K h
    apply Subtype.ext
    exact congrArg (fun z : axialCartanLieSubalgebra.toSubmodule => (z : Der)) h
  · intro H
    exact ⟨⟨H.1, H.2⟩, rfl⟩

noncomputable def realWeylCycle_axialCartanEquiv :
    axialCartanLieSubalgebra ≃ₗ[ℝ] axialCartanLieSubalgebra :=
  axialCartan_toSubmodule_equiv.trans
    (nativeCartanParameterPlaneEquiv.trans
      (realWeylCycle_canonicalCartanRestriction.trans
        (nativeCartanParameterPlaneEquiv.symm.trans
          axialCartan_toSubmodule_equiv.symm)))

noncomputable def realWeylReflection_axialCartanEquiv :
    axialCartanLieSubalgebra ≃ₗ[ℝ] axialCartanLieSubalgebra :=
  axialCartan_toSubmodule_equiv.trans
    (nativeCartanParameterPlaneEquiv.trans
      (realWeylReflection_canonicalCartanRestriction.trans
        (nativeCartanParameterPlaneEquiv.symm.trans
          axialCartan_toSubmodule_equiv.symm)))

theorem realWeylCycle_conjugates_Cartan
    (H : axialCartanLieSubalgebra) :
    conjugateCanonicalDerivation realWeylCycle (H : canonicalZornDerivations) =
      ((realWeylCycle_axialCartanEquiv H : axialCartanLieSubalgebra) :
        canonicalZornDerivations) := by
  rfl

theorem realWeylReflection_conjugates_Cartan
    (H : axialCartanLieSubalgebra) :
    conjugateCanonicalDerivation realWeylReflection (H : canonicalZornDerivations) =
      ((realWeylReflection_axialCartanEquiv H : axialCartanLieSubalgebra) :
        canonicalZornDerivations) := by
  rfl

theorem vectorCanonicalLieEquiv_cartanDerivation_zero_mem :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv
        (cartanDerivation 0) ∈ canonicalCartanParameterPlane := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv
      (nativeParameterBasis 6) ∈ canonicalCartanParameterPlane
  change parameterCanonicalLieEquiv (parameterUnit 6) ∈ canonicalCartanParameterPlane
  exact canonicalCartanParameterPlane.subset_span (by simp [canonicalCartanParameterPlane,
    cartanParameterPlane])

theorem vectorCanonicalLieEquiv_cartanDerivation_one_mem :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv
        (cartanDerivation 1) ∈ canonicalCartanParameterPlane := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv
      (nativeParameterBasis 13) ∈ canonicalCartanParameterPlane
  change parameterCanonicalLieEquiv (parameterUnit 13) ∈ canonicalCartanParameterPlane
  exact canonicalCartanParameterPlane.subset_span (by simp [canonicalCartanParameterPlane,
    cartanParameterPlane])

theorem vectorCanonicalLieEquiv_map_nativeCartanSpan_le :
    nativeCartanSpan.map
        InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv.toLinearMap ≤
      canonicalCartanParameterPlane := by
  rintro _ ⟨D, hD, rfl⟩
  refine Submodule.span_induction
    (p := fun D _ =>
      InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv D ∈
        canonicalCartanParameterPlane) ?_ ?_ ?_ ?_ hD
  · intro D hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · exact vectorCanonicalLieEquiv_cartanDerivation_zero_mem
    · exact vectorCanonicalLieEquiv_cartanDerivation_one_mem
  · simpa using canonicalCartanParameterPlane.zero_mem
  · intro D E _ _ hD hE
    simpa only [map_add] using canonicalCartanParameterPlane.add_mem hD hE
  · intro a D _ hD
    simpa only [map_smul] using canonicalCartanParameterPlane.smul_mem a hD

theorem cartanDerivation_zero_ne_one :
    cartanDerivation 0 ≠ cartanDerivation 1 := by
  intro h
  have h' := congrArg parameterLinearEquiv.symm h
  simpa [cartanDerivation, nativeParameterBasis, parameterUnit,
    Pi.basisFun, Pi.single_apply] using h'

theorem cartanDerivation_linearIndependent :
    LinearIndependent ℝ (fun j : Fin 2 => cartanDerivation j) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hparam := congrArg parameterLinearEquiv.symm hg
  fin_cases i
  · have hcoord := congrFun hparam 6
    simpa [cartanDerivation, nativeParameterBasis, parameterUnit,
      Pi.basisFun, Pi.single_apply] using hcoord
  · have hcoord := congrFun hparam 13
    simpa [cartanDerivation, nativeParameterBasis, parameterUnit,
      Pi.basisFun, Pi.single_apply] using hcoord

theorem nativeCartanSpan_finrank :
    Module.finrank ℝ nativeCartanSpan = 2 := by
  have hset : ({cartanDerivation 0, cartanDerivation 1} :
      Set (ZornVectorMatrix.Derivation (R := ℝ))) =
      Set.range (fun j : Fin 2 => cartanDerivation j) := by
    ext D
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · intro h
      rcases h with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp
  change Module.finrank ℝ
    (Submodule.span ℝ (Set.range (fun j : Fin 2 => cartanDerivation j))) = 2
  rw [← hset, finrank_span_eq_card cartanDerivation_linearIndependent]
  rfl

theorem canonicalCartanParameterPlane_finrank :
    Module.finrank ℝ canonicalCartanParameterPlane = 2 := by
  have h := (nativeCartanParameterPlaneEquiv).finrank_map_eq
    (InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra.toSubmodule)
  rw [← h]
  change Module.finrank ℝ axialCartanLieSubalgebra = 2
  exact axialCartanLieSubalgebra_finrank

theorem vectorCanonicalLieEquiv_map_nativeCartanSpan_eq :
    nativeCartanSpan.map
        InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv.toLinearMap =
      canonicalCartanParameterPlane := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact vectorCanonicalLieEquiv_map_nativeCartanSpan_le
  · rw [nativeCartanSpan_finrank, canonicalCartanParameterPlane_finrank]

noncomputable def nativeCartanSpanCanonicalEquiv :
    nativeCartanSpan ≃ₗ[ℝ] canonicalCartanParameterPlane := by
  let f : nativeCartanSpan →ₗ[ℝ] canonicalCartanParameterPlane :=
    { toFun := fun D => ⟨
        InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv D,
        by
          have h : InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv D ∈
              nativeCartanSpan.map
                InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv.toLinearMap :=
            ⟨D, D.property, rfl⟩
          rw [vectorCanonicalLieEquiv_map_nativeCartanSpan_eq] at h
          exact h⟩
      map_add' := by
        intro D E
        apply Subtype.ext
        exact InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv.map_add D E
      map_smul' := by
        intro a D
        apply Subtype.ext
        exact InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv.map_smul a D }
  apply LinearEquiv.ofBijective f
  constructor
  · intro D E h
    apply Subtype.ext
    apply InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv.injective
    exact congrArg (fun z : canonicalCartanParameterPlane =>
      (z : canonicalZornDerivations)) h
  · intro E
    have h : (E : canonicalZornDerivations) ∈
        nativeCartanSpan.map
          InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv.toLinearMap := by
      rw [vectorCanonicalLieEquiv_map_nativeCartanSpan_eq]
      exact E.property
    rcases h with ⟨D, hD, hDE⟩
    refine ⟨⟨D, hD⟩, ?_⟩
    apply Subtype.ext
    exact hDE.symm

theorem nativeCartanSpanCanonicalEquiv_cycle_intertwines
    (D : nativeCartanSpan) :
    nativeCartanSpanCanonicalEquiv
        (realWeylCycle_nativeCartanSpanLinearMap D) =
      realWeylCycle_canonicalCartanRestriction
        (nativeCartanSpanCanonicalEquiv D) := by
  apply Subtype.ext
  rfl

theorem nativeCartanSpanCanonicalEquiv_reflection_intertwines
    (D : nativeCartanSpan) :
    nativeCartanSpanCanonicalEquiv
        (realWeylReflection_nativeCartanSpanLinearMap D) =
      realWeylReflection_canonicalCartanRestriction
        (nativeCartanSpanCanonicalEquiv D) := by
  apply Subtype.ext
  rfl

/-
theorem realWeylReflection_maps_nativeCartanSpan_duplicate
    {D : ZornVectorMatrix.Derivation (R := ℝ)} (hD : D ∈ nativeCartanSpan) :
    conjugateNativeDerivation realWeylReflection D ∈ nativeCartanSpan := by
  have h0 : conjugateNativeDerivation realWeylReflection (cartanDerivation 0) ∈ nativeCartanSpan := by
    have hrepr : cartanDerivation 0 = (1 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (-1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by module
    rw [hrepr]
    change conjugateNativeDerivationLinear realWeylReflection _ ∈ _
    have hA : conjugateNativeDerivationLinear realWeylReflection
        (cartanDerivation 0 + cartanDerivation 1) =
        -(cartanDerivation 0 + cartanDerivation 1) := by
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
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} :
        Set (ZornVectorMatrix.Derivation (R := ℝ)))) (by simp)
    have h1mem : cartanDerivation 1 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} :
        Set (ZornVectorMatrix.Derivation (R := ℝ)))) (by simp)
    exact nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem _ (nativeCartanSpan.add_mem
        (nativeCartanSpan.smul_mem _ h0mem) (nativeCartanSpan.smul_mem _ h1mem)))
      (nativeCartanSpan.smul_mem _ (nativeCartanSpan.add_mem
        (nativeCartanSpan.smul_mem _ h0mem) (nativeCartanSpan.smul_mem _ h1mem)))
  have h1 : conjugateNativeDerivation realWeylReflection (cartanDerivation 1) ∈ nativeCartanSpan := by
    have hrepr : cartanDerivation 1 = (2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
        (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) := by module
    rw [hrepr]
    change conjugateNativeDerivationLinear realWeylReflection _ ∈ _
    have hA : conjugateNativeDerivationLinear realWeylReflection (cartanDerivation 0) +
        conjugateNativeDerivationLinear realWeylReflection (cartanDerivation 1) =
        -(cartanDerivation 0 + cartanDerivation 1) := by
      simpa [conjugateNativeDerivationLinear_apply] using realWeylReflection_cartanPair_zero
    have hB : (-2 : ℝ) • conjugateNativeDerivationLinear realWeylReflection (cartanDerivation 0) +
        conjugateNativeDerivationLinear realWeylReflection (cartanDerivation 1) =
        (-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1 := by
      simpa [conjugateNativeDerivationLinear_apply] using realWeylReflection_cartanPair_one
    have hcalc : conjugateNativeDerivationLinear realWeylReflection
          ((2 / 3 : ℝ) • (cartanDerivation 0 + cartanDerivation 1) +
            (1 / 3 : ℝ) • ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1)) =
        (2 / 3 : ℝ) • (-(cartanDerivation 0 + cartanDerivation 1)) +
          (1 / 3 : ℝ) • ((-1 : ℝ) • cartanDerivation 0 + 2 • cartanDerivation 1) := by
      simp only [map_add, map_smul]
      rw [hA, hB]
    rw [hcalc]
    have h0mem : cartanDerivation 0 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} : Set _)) (by simp)
    have h1mem : cartanDerivation 1 ∈ nativeCartanSpan :=
      Submodule.subset_span (s := ({cartanDerivation 0, cartanDerivation 1} : Set _)) (by simp)
    exact nativeCartanSpan.add_mem
      (nativeCartanSpan.smul_mem _ (nativeCartanSpan.add_mem
        (nativeCartanSpan.smul_mem _ h0mem) (nativeCartanSpan.smul_mem (2 : ℝ) h1mem)))
      (nativeCartanSpan.smul_mem _ (nativeCartanSpan.add_mem
        (nativeCartanSpan.smul_mem _ h0mem) (nativeCartanSpan.smul_mem (2 : ℝ) h1mem)))
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
-/

-/

end InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction
