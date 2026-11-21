/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Finite-place completions of Dedekind fraction fields

These results specialize the valuation-theoretic completion API to the residue field and
compactness properties needed for local Euler factors. The residue-field comparison follows the
proof in `external_refs/riemann-masullo/RiemannMasullo/ForMathlib/NumberTheory/NumberField/Completion/FinitePlace.lean`
(Apache-2.0, revision `06401fe6623e9557320ab57cd57e27990579cbda`); the theorem is proved here
against the repository's pinned Mathlib rather than imported from that newer package.
-/

public section

namespace InfoGeometry.Arithmetic.NumberFieldCompletionFinitePlace

open Filter IsDedekindDomain IsLocalRing Topology
open scoped WithZero
open Valued.integer

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

open NumberField in
/-- The residue field of the completed DVR at a height-one prime agrees with the residue field
of the original Dedekind domain. -/
theorem nonempty_residueFieldEquiv_adicCompletion (v : HeightOneSpectrum R) :
    Nonempty ((R ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers K)) := by
  let O := v.adicCompletionIntegers K
  let f := (residue O).comp (algebraMap R O)
  let q : R ⧸ v.asIdeal →+* ResidueField O := Ideal.Quotient.lift v.asIdeal f (by
    intro r hr
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff _
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).2
    change Valued.v (algebraMap R (v.adicCompletion K) r) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
    exact (v.valuation_lt_one_iff_mem r).2 hr)
  let := Ideal.Quotient.field v.asIdeal
  refine ⟨RingEquiv.ofBijective q ⟨q.injective, ?_⟩⟩
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  let ν : Valuation (v.adicCompletion K) ℤᵐ⁰ := Valued.v
  have hn : {z | ν (z - (x : v.adicCompletion K)) < 1} ∈ 𝓝 (x : v.adicCompletion K) := by
    refine Valued.mem_nhds.mpr ⟨1, ?_⟩
    intro z hz
    simpa only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_iff_lt_embedding,
      map_one] using hz
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap K).mem_nhds hn
  change ν (algebraMap K (v.adicCompletion K) a - x) < 1 at ha
  have ha' : v.valuation K a ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change ν (algebraMap K (v.adicCompletion K) a) ≤ 1
    simpa only [sub_add_cancel] using ν.map_add_le ha.le x.property
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer ha' 1
  have hr' : ν (algebraMap R (v.adicCompletion K) r -
      algebraMap K (v.adicCompletion K) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub]
    change Valued.v (((algebraMap R K) r - a : K) : v.adicCompletion K) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [Units.val_one] using hr
  refine ⟨Ideal.Quotient.mk _ r, sub_eq_zero.mp ?_⟩
  change residue O (algebraMap R O r) - residue O x = 0
  rw [← map_sub, residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff _ ν).2
  change ν (algebraMap R (v.adicCompletion K) r - x) < 1
  simpa only [sub_add_sub_cancel] using ν.map_add_lt hr' ha

variable [Infinite R]

/-- The completed residue field at a height-one prime has cardinality equal to the absolute
norm of that prime. -/
theorem card_residueField_adicCompletion (v : HeightOneSpectrum R) :
    Nat.card (ResidueField (v.adicCompletionIntegers K)) = v.asIdeal.absNorm := by
  obtain ⟨e⟩ := nonempty_residueFieldEquiv_adicCompletion (K := K) v
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr e.toEquiv).symm

variable [Ring.HasFiniteQuotients R]

/-- Closed balls in the completed fraction field are compact. -/
theorem properSpace_adicCompletion (v : HeightOneSpectrum R) :
    ProperSpace (v.adicCompletion K) := by
  have hDVR : IsDiscreteValuationRing (v.adicCompletionIntegers K) := inferInstance
  have hFinite : Finite (ResidueField (v.adicCompletionIntegers K)) := by
    obtain ⟨e⟩ := nonempty_residueFieldEquiv_adicCompletion (K := K) v
    have hQuot : Finite (R ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    exact Finite.of_equiv (R ⧸ v.asIdeal) e.toEquiv
  exact (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (Γ₀ := ℤᵐ⁰)).2 ⟨inferInstance, hDVR, hFinite⟩

/-- The valuation ring inside a finite-place completion is compact. -/
theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum R) :
    CompactSpace (v.adicCompletionIntegers K) := by
  have hFinite : Finite (ResidueField (v.adicCompletionIntegers K)) := by
    obtain ⟨e⟩ := nonempty_residueFieldEquiv_adicCompletion (K := K) v
    have hQuot : Finite (R ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    exact Finite.of_equiv (R ⧸ v.asIdeal) e.toEquiv
  have hClosed : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isClosed_valuationSubring _
  have hComplete : CompleteSpace (v.adicCompletionIntegers K) := IsClosed.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hComplete, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)), hFinite⟩

open Function NumberField in
/-- A chosen normalized uniformizer identifies the unit group of the completion with the
product of the discrete valuation direction and the units in its valuation ring. -/
theorem finitePlace_unitDecomposition (v : HeightOneSpectrum R)
    (π : (v.adicCompletion K)ˣ)
    (hπ : ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹) :
    let ι := Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom
    ∃ e : (v.adicCompletion K)ˣ ≃ₜ* (Multiplicative ℤ × (v.adicCompletionIntegers K)ˣ),
      e π = (Multiplicative.ofAdd 1, 1) ∧ ∀ u, e (ι u) = (1, u) := by
  let O := v.adicCompletionIntegers K
  let ι : Oˣ →* (v.adicCompletion K)ˣ := Units.map O.subtype.toMonoidHom
  have hι : Continuous ι := continuous_subtype_val.units_map O.subtype.toMonoidHom
  let valUnits := Units.map (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).toMonoidHom
  let ord := (WithZero.unitsWithZeroEquiv.toMonoidHom.comp valUnits)⁻¹
  have hord (x : (v.adicCompletion K)ˣ) : (ord x).toAdd = -WithZero.log (Valued.v x.val) :=
    congrArg Neg.neg (WithZero.logEquiv_apply (valUnits x))
  have hker (x : (v.adicCompletion K)ˣ) : ord x = 1 ↔ x ∈ O.units := by
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    change (ord x).toAdd = 0 ↔ _
    rw [hord, neg_eq_zero, ← WithZero.exp_eq_one,
      WithZero.exp_log (by simp [x.ne_zero])]
  have hcont : Continuous ord := by
    apply continuous_of_continuousAt_one ord
    apply Filter.EventuallyEq.continuousAt (y := 1)
    filter_upwards [(Submonoid.isOpen_units (Valued.isOpen_valuationSubring
      (v.adicCompletion K))).mem_nhds O.units.one_mem] with x hx
    exact (hker x).mpr hx
  have hordπ : (ord π).toAdd = 1 := by
    have hq : (1 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ (by simp [π.ne_zero]),
      NNReal.coe_zpow] at hπ
    have hlog : WithZero.log (Valued.v π.val) = -1 :=
      zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne' (by simpa using hπ)
    rw [hord, hlog, neg_neg]
  let sec : Multiplicative ℤ →* (v.adicCompletion K)ˣ :=
    { toFun := fun k ↦ π ^ k.toAdd
      map_one' := zpow_zero _
      map_mul' := fun x y ↦ zpow_add _ _ _ }
  have hsec : RightInverse sec ord := by
    intro k
    change ord (π ^ k.toAdd) = k
    rw [map_zpow]
    change k.toAdd • (ord π).toAdd = k.toAdd
    simp [hordπ]
  let strip := (MonoidHom.id (v.adicCompletion K)ˣ) / (sec.comp ord)
  have hstrip (x : (v.adicCompletion K)ˣ) : strip x ∈ O.units := by
    apply (hker _).mp
    change ord (x / sec (ord x)) = 1
    rw [map_div, hsec, div_self']
  let res := O.toSubmonoid.unitsEquivUnitsType.toMonoidHom.comp
    (strip.codRestrict O.units hstrip)
  have hsec_cont : Continuous sec := continuous_of_discreteTopology
  have hstrip_cont : Continuous strip := continuous_id.div' (hsec_cont.comp hcont)
  have hres : Continuous res := by
    apply Units.continuous_iff.mpr
    exact ⟨(Units.continuous_val.comp hstrip_cont).subtype_mk (fun x ↦ (hstrip x).1),
      (Units.continuous_val.comp hstrip_cont.inv).subtype_mk (fun x ↦ (hstrip x).2)⟩
  have hresval (x : (v.adicCompletion K)ˣ) : ι (res x) = x / sec (ord x) := Units.ext rfl
  have hιinj : Injective ι := Units.map_injective Subtype.val_injective
  have hordι (u : Oˣ) : ord (ι u) = 1 := (hker _).mpr ⟨u.val.prop, u.inv.prop⟩
  let e : (v.adicCompletion K)ˣ ≃ₜ* (Multiplicative ℤ × Oˣ) :=
    { toFun := fun x ↦ (ord x, res x)
      invFun := fun p ↦ sec p.1 * ι p.2
      map_mul' := fun x y ↦ Prod.ext (map_mul ord x y) (map_mul res x y)
      left_inv := fun x ↦ by
        change sec (ord x) * ι (res x) = x
        rw [hresval, mul_div_cancel]
      right_inv := fun p ↦ by
        have ho : ord (sec p.1 * ι p.2) = p.1 := by
          rw [map_mul, hsec, hordι, mul_one]
        exact Prod.ext ho (hιinj (by rw [hresval, ho]; exact mul_div_cancel_left _ _))
      continuous_toFun := hcont.prodMk hres
      continuous_invFun := (hsec_cont.comp continuous_fst).mul (hι.comp continuous_snd) }
  refine ⟨e, Prod.ext hordπ (hιinj ?_), fun u ↦ Prod.ext (hordι u) (hιinj ?_)⟩
  · change ι (res π) = ι 1
    rw [hresval, map_one]
    change π / π ^ (ord π).toAdd = 1
    rw [hordπ, zpow_one, div_self']
  · change ι (res (ι u)) = ι u
    rw [hresval, hordι, map_one, div_one]

end InfoGeometry.Arithmetic.NumberFieldCompletionFinitePlace
