/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwelveFoldCyclotomicNative
import InfoGeometry.LLM.LanguageSymmetryFourier
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.Trace.Basic

/-!
# Cyclotomic Galois actions and integral Fourier orbit sums

The carrier is a native cyclotomic number field and the harmonic is Mathlib's
`AddChar.zmodChar`. A Galois automorphism acts by its associated unit modulo
the period. The sum over those units is a field trace; integrality of the
root of unity and integrally closedness of `ℤ` prove that it is an integer.

The integer statement is not inferred from Galois invariance alone. An orbit
sum is one invariant function, not a basis for an entire divisor shell.
There is no assertion that an arbitrary cyclotomic field automorphism acts
on real and imaginary coordinates by ordinary complex conjugation.
-/

noncomputable section

namespace InfoGeometry.LLM.LanguageSymmetry

open scoped BigOperators Classical

section FrequencyShells

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Multiplication by a unit preserves the exact additive order of a frequency. -/
theorem unit_frequency_preserves_order (u : (ZMod n)ˣ) (k : ZMod n) :
    addOrderOf ((u : ZMod n) * k) = addOrderOf k := by
  exact (Units.mulLeftLinearEquiv ℤ (ZMod n) u).toAddEquiv.addOrderOf_eq k

/-- The exact additive order completely classifies unit orbits of cyclic
frequencies; the reverse implication constructs a unit, rather than merely
showing that the order is an invariant. -/
theorem unit_frequency_orbit_iff (k l : ZMod n) :
    (∃ u : (ZMod n)ˣ, (u : ZMod n) * k = l) ↔ addOrderOf k = addOrderOf l := by
  constructor
  · rintro ⟨u, rfl⟩
    exact (unit_frequency_preserves_order u k).symm
  · intro hkl
    obtain ⟨d, hd, u, hu, hk⟩ := ZMod.eq_unit_mul_divisor k
    obtain ⟨e, he, v, hv, hl⟩ := ZMod.eq_unit_mul_divisor l
    rcases hu with ⟨u, rfl⟩
    rcases hv with ⟨v, rfl⟩
    rw [hk, hl, unit_frequency_preserves_order, unit_frequency_preserves_order,
      ZMod.addOrderOf_coe d (NeZero.ne n), ZMod.addOrderOf_coe e (NeZero.ne n),
      Nat.gcd_eq_right hd, Nat.gcd_eq_right he] at hkl
    have hde : d = e := by
      calc
        d = n / (n / d) := (Nat.div_div_self hd (NeZero.ne n)).symm
        _ = n / (n / e) := by rw [hkl]
        _ = e := Nat.div_div_self he (NeZero.ne n)
    subst e
    refine ⟨v * u⁻¹, ?_⟩
    rw [hk, hl, Units.val_mul]
    simp only [mul_assoc, Units.inv_mul_cancel_left]

/-- Frequencies of exact additive order `d` form the usual divisor shell. -/
def frequencyShell (n : ℕ) [NeZero n] (d : ℕ) : Finset (ZMod n) :=
  Finset.univ.filter (fun k => addOrderOf k = d)

/-- Frequencies have exactly one order, so distinct order shells are disjoint. -/
theorem frequencyShell_disjoint {d e : ℕ} (hde : d ≠ e) :
    Disjoint (frequencyShell n d) (frequencyShell n e) := by
  apply Finset.disjoint_left.mpr
  intro k hk hl
  exact hde ((Finset.mem_filter.mp hk).2.symm.trans (Finset.mem_filter.mp hl).2)

/-- The shells indexed by divisors of the period are an actual partition of
the frequency-index set, not only a numerical totient identity. -/
theorem frequencyShell_partition :
    n.divisors.biUnion (frequencyShell n) = Finset.univ := by
  ext k
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  refine ⟨addOrderOf k, Nat.mem_divisors.mpr ⟨?_, NeZero.ne n⟩, ?_⟩
  · simpa only [ZMod.card] using (addOrderOf_dvd_card (x := k))
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, rfl⟩

/-- The native cyclic-group counting theorem gives the size of each shell. -/
theorem frequencyShell_card {d : ℕ} (hd : d ∣ n) :
    (frequencyShell n d).card = Nat.totient d := by
  exact IsAddCyclic.card_addOrderOf_eq_totient
    (by simpa only [ZMod.card] using hd)

/-- The exact-order shells exhaust the `n` frequency indices in cardinality. -/
theorem frequencyShell_card_sum :
    ∑ d ∈ n.divisors, (frequencyShell n d).card = n := by
  calc
    ∑ d ∈ n.divisors, (frequencyShell n d).card =
        ∑ d ∈ n.divisors, Nat.totient d := by
          apply Finset.sum_congr rfl
          intro d hd
          exact frequencyShell_card (Nat.dvd_of_mem_divisors hd)
    _ = n := Nat.sum_totient n

/-- Each divisor shell is stable under every unit action on frequencies. -/
theorem frequencyShell_unit_invariant (u : (ZMod n)ˣ) (d : ℕ) (k : ZMod n) :
    (u : ZMod n) * k ∈ frequencyShell n d ↔ k ∈ frequencyShell n d := by
  simp only [frequencyShell, Finset.mem_filter, Finset.mem_univ, true_and,
    unit_frequency_preserves_order]

end FrequencyShells

section CyclotomicAction

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K]

/-- The Galois action on the root-of-unity character is the frequency-unit action. -/
theorem galois_zmodChar_action (σ : Gal(K / ℚ)) {ζ : K} (hζ : ζ ^ n = 1)
    (x : ZMod n) :
    σ (AddChar.zmodChar n hζ x) = AddChar.zmodChar n hζ
      ((IsCyclotomicExtension.Rat.galEquivZMod n K σ : ZMod n) * x) := by
  change σ (ζ ^ x.val) =
    ζ ^ ((IsCyclotomicExtension.Rat.galEquivZMod n K σ : ZMod n) * x).val
  rw [map_pow, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n K σ hζ,
    ← pow_mul, ZMod.val_mul]
  exact pow_eq_pow_mod _ hζ

/-- Applying a Galois automorphism sends the `k`th harmonic to the `u*k`th
harmonic for the actual associated unit `u`. -/
theorem galois_harmonic_action (σ : Gal(K / ℚ)) {ζ : K} (hζ : ζ ^ n = 1)
    (k x : ZMod n) :
    σ ((AddChar.zmodChar n hζ).mulShift k x) =
      (AddChar.zmodChar n hζ).mulShift
        ((IsCyclotomicExtension.Rat.galEquivZMod n K σ : ZMod n) * k) x := by
  simpa only [AddChar.mulShift_apply, mul_assoc] using
    galois_zmodChar_action σ hζ (k * x)

omit [NumberField K] [IsCyclotomicExtension {n} ℚ K] in
/-- A primitive root gives distinct values at distinct cyclic residues. -/
theorem primitive_zmodChar_injective {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (AddChar.zmodChar n hζ.pow_eq_one) := by
  intro k l hkl
  exact ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt k) (ZMod.val_lt l) hkl)

/-- For a primitive root, its character values lie in the same Galois orbit
exactly when the frequency indices have the same additive order. -/
theorem galois_character_orbit_iff {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (k l : ZMod n) :
    (∃ σ : Gal(K / ℚ), σ (AddChar.zmodChar n hζ.pow_eq_one k) =
      AddChar.zmodChar n hζ.pow_eq_one l) ↔ addOrderOf k = addOrderOf l := by
  rw [← unit_frequency_orbit_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨IsCyclotomicExtension.Rat.galEquivZMod n K σ, ?_⟩
    apply primitive_zmodChar_injective hζ
    rwa [← galois_zmodChar_action σ hζ.pow_eq_one]
  · rintro ⟨u, hu⟩
    refine ⟨(IsCyclotomicExtension.Rat.galEquivZMod n K).symm u, ?_⟩
    rw [galois_zmodChar_action, MulEquiv.apply_symm_apply, hu]

/-- The size of the Galois orbit of a character value is the totient of its
exact order. This counts values, not a repeated sum over stabilizers. -/
theorem galois_character_orbit_card {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (k : ZMod n) :
    (Finset.univ.filter (fun l : ZMod n => ∃ σ : Gal(K / ℚ),
      σ (AddChar.zmodChar n hζ.pow_eq_one k) =
        AddChar.zmodChar n hζ.pow_eq_one l)).card = Nat.totient (addOrderOf k) := by
  have hset : (Finset.univ.filter (fun l : ZMod n => ∃ σ : Gal(K / ℚ),
      σ (AddChar.zmodChar n hζ.pow_eq_one k) =
        AddChar.zmodChar n hζ.pow_eq_one l)) = frequencyShell n (addOrderOf k) := by
    ext l
    simp only [frequencyShell, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (galois_character_orbit_iff hζ k l).trans eq_comm
  rw [hset]
  exact frequencyShell_card (by simpa only [ZMod.card] using
    (addOrderOf_dvd_card (x := k)))

/-- The Ramanujan orbit sum associated with the chosen `n`th root of unity.
For a primitive root it sums the primitive-frequency characters evaluated at
`x`; different characters may take the same value at that particular `x`. -/
def cyclotomicOrbitSum {ζ : K} (hζ : ζ ^ n = 1) (x : ZMod n) : K :=
  ∑ u : (ZMod n)ˣ, AddChar.zmodChar n hζ ((u : ZMod n) * x)

/-- The unit-indexed Fourier orbit sum is the field trace of the character value. -/
theorem cyclotomicOrbitSum_eq_trace {ζ : K} (hζ : ζ ^ n = 1) (x : ZMod n) :
    cyclotomicOrbitSum hζ x =
      algebraMap ℚ K (Algebra.trace ℚ K (AddChar.zmodChar n hζ x)) := by
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  rw [trace_eq_sum_automorphisms]
  symm
  apply Fintype.sum_equiv (IsCyclotomicExtension.Rat.galEquivZMod n K).toEquiv
  intro σ
  exact galois_zmodChar_action σ hζ x

/-- Roots of unity give integral character values, hence integer traces.
This proves integer-valuedness of the actual Fourier orbit sum. -/
theorem cyclotomicOrbitSum_is_integer {ζ : K} (hζ : ζ ^ n = 1) (x : ZMod n) :
    ∃ z : ℤ, cyclotomicOrbitSum hζ x = (z : K) := by
  have hζint : IsIntegral ℤ ζ :=
    IsIntegral.of_pow (NeZero.pos n) (by simpa only [hζ] using (isIntegral_one :
      IsIntegral ℤ (1 : K)))
  have hxint : IsIntegral ℤ (AddChar.zmodChar n hζ x) := hζint.pow x.val
  have htint : IsIntegral ℤ (Algebra.trace ℚ K (AddChar.zmodChar n hζ x)) :=
    Algebra.isIntegral_trace hxint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp htint
  refine ⟨z, ?_⟩
  rw [cyclotomicOrbitSum_eq_trace, ← hz]
  simp

/-- Every Galois automorphism fixes the orbit sum, as follows from its integer value. -/
theorem galois_cyclotomicOrbitSum (σ : Gal(K / ℚ)) {ζ : K} (hζ : ζ ^ n = 1)
    (x : ZMod n) : σ (cyclotomicOrbitSum hζ x) = cyclotomicOrbitSum hζ x := by
  obtain ⟨z, hz⟩ := cyclotomicOrbitSum_is_integer hζ x
  rw [hz, map_intCast]

omit [NumberField K] [IsCyclotomicExtension {n} ℚ K] in
/-- At the zero residue, the orbit sum is the number of units, Euler's totient. -/
theorem cyclotomicOrbitSum_zero {ζ : K} (hζ : ζ ^ n = 1) :
    cyclotomicOrbitSum hζ 0 = (Nat.totient n : K) := by
  simp only [cyclotomicOrbitSum, mul_zero, AddChar.map_zero_eq_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, ZMod.card_units_eq_totient]

end CyclotomicAction

section ConcreteHarmonicBasis

open Matrix

variable {n : ℕ} [NeZero n] {ζ : ℂ}

/-- A primitive complex root identifies cyclic frequency indices with all
complex additive characters, rather than only a selected family of modes. -/
def primitiveHarmonicEquiv (hζ : IsPrimitiveRoot ζ n) :
    ZMod n ≃ AddChar (ZMod n) ℂ :=
  Equiv.ofBijective (AddChar.zmodChar n hζ.pow_eq_one).mulShift (by
    rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
    exact ⟨AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.zmodChar_primitive_of_primitive_root n hζ), rfl⟩)

/-- The concrete cyclotomic harmonics form a native full basis of functions. -/
def primitiveHarmonicBasis (hζ : IsPrimitiveRoot ζ n) :
    Module.Basis (ZMod n) ℂ (ZMod n → ℂ) :=
  (AddChar.complexBasis (ZMod n)).reindex (primitiveHarmonicEquiv hζ).symm

@[simp]
theorem primitiveHarmonicBasis_apply (hζ : IsPrimitiveRoot ζ n) (k : ZMod n) :
    primitiveHarmonicBasis hζ k =
      ((AddChar.zmodChar n hζ.pow_eq_one).mulShift k : ZMod n → ℂ) := by
  simp only [primitiveHarmonicBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    AddChar.complexBasis_apply]
  rfl

/-- Every vector of this concrete basis satisfies the previously established
circulant eigenvector equation, with the same Fourier-coefficient convention. -/
theorem circulant_mulVec_primitiveHarmonicBasis (C : ZMod n → ℂ)
    (hζ : IsPrimitiveRoot ζ n) (k : ZMod n) :
    Matrix.circulant C *ᵥ primitiveHarmonicBasis hζ k =
      kernelEigenvalue C ((AddChar.zmodChar n hζ.pow_eq_one).mulShift k) •
        primitiveHarmonicBasis hζ k := by
  simpa only [primitiveHarmonicBasis_apply] using
    circulant_mulVec_character C ((AddChar.zmodChar n hζ.pow_eq_one).mulShift k)

end ConcreteHarmonicBasis

section Ramanujan

open Polynomial

/-- The power sum of all primitive complex `n`th roots. This is the
root-independent version of the Ramanujan Fourier orbit sum. -/
def primitiveFourierSum (n x : ℕ) : ℂ :=
  ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ x

/-- Primitive unit powers enumerate the primitive roots without duplication. -/
theorem cyclotomicOrbitSum_eq_primitiveFourierSum {n : ℕ} [NeZero n]
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (x : ℕ) :
    cyclotomicOrbitSum hζ.pow_eq_one (x : ZMod n) = primitiveFourierSum n x := by
  calc
    cyclotomicOrbitSum hζ.pow_eq_one (x : ZMod n) =
        ∑ u : (ZMod n)ˣ, (ζ ^ u.val.val) ^ x := by
      apply Finset.sum_congr rfl
      intro u _
      change AddChar.zmodChar n hζ.pow_eq_one ((u : ZMod n) * x) = _
      rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
      rfl
    _ = primitiveFourierSum n x := by
      apply Finset.sum_bij (fun u _ => ζ ^ u.val.val)
      · intro u _
        exact (mem_primitiveRoots (NeZero.pos n)).mpr
          (hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime u))
      · intro u _ v _ huv
        apply Units.ext
        exact ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt u.val)
          (ZMod.val_lt v.val) huv)
      · intro ξ hξ
        obtain ⟨i, hi, hcop, hpow⟩ := hζ.isPrimitiveRoot_iff.mp
          ((mem_primitiveRoots (NeZero.pos n)).mp hξ)
        refine ⟨ZMod.unitOfCoprime i hcop, Finset.mem_univ _, ?_⟩
        simpa only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi] using hpow
      · intro u _
        rfl

/-- The sum of `x`th powers over all `n`th roots is the finite-character
orthogonality identity: `n` if `n ∣ x`, and zero otherwise. -/
theorem sum_nthRootsFinset_pow (n x : ℕ) (hn : 0 < n) :
    ∑ ξ ∈ nthRootsFinset n (1 : ℂ), ξ ^ x = if n ∣ x then (n : ℂ) else 0 := by
  let : NeZero n := ⟨hn.ne'⟩
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  let χ := AddChar.zmodChar n hζ.pow_eq_one
  have hsum : (∑ k : ZMod n, (χ k) ^ x) =
      ∑ ξ ∈ nthRootsFinset n (1 : ℂ), ξ ^ x := by
    apply Finset.sum_bij (fun k _ => χ k)
    · intro k _
      rw [mem_nthRootsFinset hn]
      change (ζ ^ k.val) ^ n = 1
      rw [pow_right_comm, hζ.pow_eq_one, one_pow]
    · intro k _ l _ hkl
      exact ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt k) (ZMod.val_lt l) hkl)
    · intro ξ hξ
      obtain ⟨i, _, hpow⟩ := hζ.eq_pow_of_pow_eq_one
        ((mem_nthRootsFinset hn (1 : ℂ)).mp hξ)
      refine ⟨(i : ZMod n), Finset.mem_univ _, ?_⟩
      simpa only [χ, AddChar.zmodChar_apply'] using hpow
    · intro k _
      rfl
  rw [← hsum]
  have hshift : (∑ k : ZMod n, (χ k) ^ x) =
      ∑ k : ZMod n, χ.mulShift (x : ZMod n) k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [AddChar.mulShift_apply, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [hshift]
  by_cases hx : n ∣ x
  · rw [ite_eq_left hx, (ZMod.natCast_eq_zero_iff x n).mpr hx]
    simp only [AddChar.mulShift_zero, AddChar.one_apply, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ZMod.card]
  · rw [ite_eq_right hx]
    apply AddChar.sum_eq_zero_of_ne_one
    have hcast : (x : ZMod n) ≠ 0 := fun hz =>
      hx ((ZMod.natCast_eq_zero_iff x n).mp hz)
    exact (AddChar.zmodChar_primitive_of_primitive_root n hζ)
      hcast

/-- Partitioning all roots by their exact order gives the divisor-sum identity. -/
theorem primitiveFourierSum_divisor_sum (n x : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, primitiveFourierSum d x = if n ∣ x then (n : ℂ) else 0 := by
  calc
    ∑ d ∈ n.divisors, primitiveFourierSum d x =
        ∑ ξ ∈ nthRootsFinset n (1 : ℂ), ξ ^ x := by
      rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
      exact (Finset.sum_biUnion (fun d _ e _ hde => IsPrimitiveRoot.disjoint hde)).symm
    _ = _ := sum_nthRootsFinset_pow n x hn

/-- The classical Möbius formula for the actual complex Ramanujan sum.
The right side is an explicit integer, not an assumed integrality witness. -/
theorem primitiveFourierSum_moebius (n x : ℕ) (hn : 0 < n) :
    primitiveFourierSum n x =
      ((∑ d ∈ (n.gcd x).divisors, (d : ℤ) * ArithmeticFunction.moebius (n / d)) : ℂ) := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun m hm => primitiveFourierSum_divisor_sum m x hm)) n hn
  have hfilter : n.divisors.filter (fun d => d ∣ x) = (n.gcd x).divisors := by
    ext d
    have hgcd : n.gcd x ≠ 0 := (Nat.gcd_pos_of_pos_left x hn).ne'
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, hgcd⟩,
      fun h => ⟨⟨h.1.1, hn.ne'⟩, h.1.2⟩⟩
  calc
    primitiveFourierSum n x =
        ∑ a ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius a.1 : ℂ) *
            (if a.2 ∣ x then (a.2 : ℂ) else 0) := hinv.symm
    _ = ∑ d ∈ n.divisors,
          (ArithmeticFunction.moebius (n / d) : ℂ) * (if d ∣ x then (d : ℂ) else 0) :=
      Nat.sum_divisorsAntidiagonal' (n := n)
        (fun a d => (ArithmeticFunction.moebius a : ℂ) *
          (if d ∣ x then (d : ℂ) else 0))
    _ = ∑ d ∈ n.divisors.filter (fun d => d ∣ x),
          (ArithmeticFunction.moebius (n / d) : ℂ) * (d : ℂ) := by
      simp only [Finset.sum_filter, mul_ite, mul_zero]
    _ = ((∑ d ∈ (n.gcd x).divisors,
          (d : ℤ) * ArithmeticFunction.moebius (n / d)) : ℂ) := by
      rw [hfilter]
      push_cast
      apply Finset.sum_congr rfl
      intro d _
      exact mul_comm _ _

/-- The unit-indexed complex Fourier sum has the same exact integer divisor formula. -/
theorem cyclotomicOrbitSum_moebius {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (x : ℕ) :
    cyclotomicOrbitSum hζ.pow_eq_one (x : ZMod n) =
      ((∑ d ∈ (n.gcd x).divisors, (d : ℤ) * ArithmeticFunction.moebius (n / d)) : ℂ) := by
  rw [cyclotomicOrbitSum_eq_primitiveFourierSum hζ x]
  exact primitiveFourierSum_moebius n x (NeZero.pos n)

end Ramanujan

section Twelve

open InfoGeometry.Canonical.TwelveFoldCyclotomicNative

local instance : NeZero (12 : ℚ) := ⟨by norm_num⟩

local instance : IsCyclotomicExtension {12} ℚ (CyclotomicField 12 ℚ) :=
  CyclotomicField.isCyclotomicExtension 12 ℚ

/-- The actual automorphism of `ℚ(ζ₁₂)` associated to the unit five. -/
def cyclotomicSigma5 : Gal(CyclotomicField 12 ℚ / ℚ) :=
  cyclotomic12_galEquivUnits.symm (Units.mkOfMulEqOne (5 : ZMod 12) 5 (by decide))

/-- Native field automorphism values, rather than unconnected modular computations. -/
theorem cyclotomicSigma5_harmonics {ζ : CyclotomicField 12 ℚ} (hζ : ζ ^ 12 = 1) :
    cyclotomicSigma5 ζ = ζ ^ 5 ∧
    cyclotomicSigma5 (ζ ^ 5) = ζ ∧
    cyclotomicSigma5 (ζ ^ 3) = ζ ^ 3 ∧
    cyclotomicSigma5 (ζ ^ 6) = ζ ^ 6 := by
  have h5 : cyclotomicSigma5 ζ = ζ ^ 5 := by
    simpa only [cyclotomicSigma5, MulEquiv.apply_symm_apply, Units.val_mkOfMulEqOne,
      ZMod.val_ofNat, Nat.reduceMod] using
      cyclotomic12_gal_action_on_twelfth_root cyclotomicSigma5 hζ
  refine ⟨h5, ?_, ?_, ?_⟩
  · rw [map_pow, h5, ← pow_mul, pow_eq_pow_mod _ hζ]
    norm_num
  · rw [map_pow, h5, ← pow_mul, pow_eq_pow_mod _ hζ]
  · rw [map_pow, h5, ← pow_mul, pow_eq_pow_mod _ hζ]

/-- The fundamental and fifth harmonics are genuinely distinct for a primitive root. -/
theorem cyclotomicSigma5_moves_primitive_root {ζ : CyclotomicField 12 ℚ}
    (hζ : IsPrimitiveRoot ζ 12) : cyclotomicSigma5 ζ ≠ ζ := by
  rw [(cyclotomicSigma5_harmonics hζ.pow_eq_one).1]
  intro heq
  have h51 : (5 : ℕ) = 1 := hζ.pow_inj (by decide) (by decide) (by simpa using heq)
  norm_num at h51

/-- Exact order-shell sizes for twelve frequency indices. -/
theorem twelve_frequencyShell_cards :
    (frequencyShell 12 1).card = 1 ∧ (frequencyShell 12 2).card = 1 ∧
    (frequencyShell 12 3).card = 2 ∧ (frequencyShell 12 4).card = 2 ∧
    (frequencyShell 12 6).card = 2 ∧ (frequencyShell 12 12).card = 4 := by
  rw [frequencyShell_card (show 1 ∣ 12 by decide),
    frequencyShell_card (show 2 ∣ 12 by decide),
    frequencyShell_card (show 3 ∣ 12 by decide),
    frequencyShell_card (show 4 ∣ 12 by decide),
    frequencyShell_card (show 6 ∣ 12 by decide),
    frequencyShell_card (show 12 ∣ 12 by decide)]
  decide

end Twelve

end InfoGeometry.LLM.LanguageSymmetry
