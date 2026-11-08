/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
import InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
import InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter
import InfoGeometry.Canonical.ExteriorAlgebraFiniteGeneration
import InfoGeometry.Canonical.SplitCliffordCurrentCommutator

/-!
# Fermionic Cutoff Currents, Support Stabilization, and Charged-Fock Intertwiner

This module proves finite one-particle support bounds for the exterior Fock
space `FermionicFock`, pointwise stabilization of the normal-ordered CAR cutoff
currents `fermionicCutoffCurrent` to `fermionicCurrentMode`, vanishing of the
cutoff boundary commutator terms, and the level-1 Heisenberg and Sugawara
Virasoro representations on `FermionicFock` and `ChargedFockSpace`.

- BUCKET 1 (Real Math in This File):
  - `FermionicFock`, `FermionicEnd`, `fermionicRawCAR`
  - `finsupp_support_subset_integerWindow`,
    `exteriorFock_exists_finite_mode_support`,
    `normalMatrixUnit_apply_eq_zero_of_outside_exceptional_support`
  - `fermionicBulkBoundaryTerm_apply_eventually_zero`,
    `fermionicEndomorphismBoundaryTerm_apply_eventually_zero`
  - `fermionicCutoffCurrent`, `fermionicCurrentMode`,
    `fermionicCutoffCurrent_eventually_eq_fermionicCurrentMode`,
    `fermionicCurrentMode_commutator`, `fermionicCurrentHeisenbergRep`,
    `fermionicCurrentSugawaraRepresentation`
  - `fermionToBosonCurrent`, `fermionToBosonCurrent_commutator`,
    `virasoro_acts_on_bosonizedFermionicCurrent`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.Canonical.ExteriorAlgebraFiniteGeneration`
  - `InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter`
  - `InfoGeometry.Canonical.SplitCliffordCurrentCommutator`
  - `InfoGeometry.Canonical.CompletedCurrentRepresentationBridge`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

noncomputable section
namespace InfoGeometry.Canonical.FermionicCurrentChargedFockIntertwiner

attribute [local instance 100] LieRing.ofAssociativeRing

open VirasoroProject
open InfoGeometry.Canonical.CanonicalNormalOrdering
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
open InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
open InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter
open InfoGeometry.Canonical.ExteriorAlgebraFiniteGeneration

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Exterior Fock space over the integer mode space `IntModeSpace 𝕜`. -/
abbrev FermionicFock : Type _ :=
  CanonicalNormalOrdering.Fock (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)

/-- Linear endomorphism ring of `FermionicFock`. -/
abbrev FermionicEnd : Type _ :=
  CanonicalNormalOrdering.EndFock (R := 𝕜)
    (M := CanonicalNormalOrdering.IntModeSpace 𝕜)

/-- Canonical raw CAR mode completion on `FermionicEnd`. -/
abbrev fermionicRawCAR :
    RawCARModeCompletion (FermionicEnd (𝕜 := 𝕜)) :=
  canonicalExteriorFockRawCAR (𝕜 := 𝕜)

/-- Every finitely supported one-particle mode vector has support contained in a
symmetric integer cutoff window `integerWindow N`. -/
theorem finsupp_support_subset_integerWindow
    (v : CanonicalNormalOrdering.IntModeSpace 𝕜) :
    ∃ N : ℕ, v.support ⊆ integerWindow N := by
  let N : ℕ := v.support.sup Int.natAbs
  refine ⟨N, ?_⟩
  intro a ha
  rw [mem_integerWindow_iff]
  have hle : Int.natAbs a ≤ N := by
    exact Finset.le_sup (f := Int.natAbs) ha
  have hle' : (Int.natAbs a : ℤ) ≤ (N : ℤ) := by
    exact_mod_cast hle
  constructor
  · by_cases hnonneg : 0 ≤ a
    · linarith
    · have hnonpos : a ≤ 0 := le_of_not_ge hnonneg
      have haabs : (Int.natAbs a : ℤ) = -a :=
        Int.ofNat_natAbs_of_nonpos hnonpos
      linarith

  · by_cases hnonneg : 0 ≤ a
    · have haabs : (Int.natAbs a : ℤ) = a :=
        Int.ofNat_natAbs_of_nonneg hnonneg
      linarith
    · have hnonpos : a ≤ 0 := le_of_not_ge hnonneg
      linarith

/-- The coordinate functional of the canonical direct-sum basis vanishes at any
index `a` outside a finite superset `S` of `v.support`. -/
theorem intModeDual_eq_zero_of_support_subset_of_not_mem
    (a : ℤ) (v : CanonicalNormalOrdering.IntModeSpace 𝕜)
    (S : Finset ℤ) (hv : v.support ⊆ S) (ha : a ∉ S) :
    CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a v = 0 := by
  have hav : a ∉ v.support := fun hav => ha (hv hav)
  have hcoef : v a = 0 := by
    dsimp; simpa [Finsupp.mem_support_iff] using hav
  simpa [CanonicalNormalOrdering.modeDual,
    CanonicalNormalOrdering.intModeBasis, Module.Basis.coord_apply] using hcoef

/-- Every exterior-Fock vector `x` lies in the subalgebra generated by one-particle
vectors supported in some finite mode set `S : Finset ℤ`. -/
theorem exteriorFock_exists_finite_mode_support
    (x : FermionicFock (𝕜 := 𝕜)) :
    ∃ S : Finset ℤ,
      x ∈ Algebra.adjoin 𝕜
        (ExteriorAlgebra.ι 𝕜 ''
          {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
            v.support ⊆ S}) := by
  rcases
      InfoGeometry.Canonical.ExteriorAlgebraFiniteGeneration.exists_finite_generating_set x with
    ⟨T, hT, hx⟩
  let U : Finset ℤ := hT.toFinset.biUnion (fun v => v.support)
  refine ⟨U, ?_⟩
  apply (Algebra.adjoin_mono ?_) hx
  intro y hy
  rcases hy with ⟨v, hvT, rfl⟩
  apply Set.mem_image_of_mem _
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨v, hT.mem_toFinset.mpr hvT, ha⟩

/-- Every finite integer set `S : Finset ℤ` is contained in `integerWindow N`
for `N = S.sup Int.natAbs`. -/
theorem finite_mode_set_subset_integerWindow (S : Finset ℤ) :
    ∃ N : ℕ, (S : Set ℤ) ⊆ integerWindow N := by
  let N : ℕ := S.sup Int.natAbs
  refine ⟨N, ?_⟩
  intro a ha
  change a ∈ integerWindow N
  rw [mem_integerWindow_iff]
  have hle : Int.natAbs a ≤ N := Finset.le_sup (f := Int.natAbs) ha
  have hle' : (Int.natAbs a : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
  constructor
  · by_cases h : 0 ≤ a
    · linarith
    · have h' : a ≤ 0 := le_of_not_ge h
      have ha' : (Int.natAbs a : ℤ) = -a := Int.ofNat_natAbs_of_nonpos h'
      linarith
  · by_cases h : 0 ≤ a
    · have ha' : (Int.natAbs a : ℤ) = a := Int.ofNat_natAbs_of_nonneg h
      linarith
    · linarith

/-- Every finite integer set `S : Finset ℤ` is eventually contained in `integerWindow N`. -/
theorem finite_mode_set_eventually_subset_integerWindow (S : Finset ℤ) :
    ∀ᶠ N : ℕ in Filter.atTop, (S : Set ℤ) ⊆ integerWindow N := by
  rcases finite_mode_set_subset_integerWindow S with ⟨N, hN⟩
  exact Filter.eventually_atTop.2 ⟨N, fun M hM => by
    intro a ha
    have haN : a ∈ integerWindow N := hN ha
    change a ∈ integerWindow M
    rw [mem_integerWindow_iff] at haN
    rw [mem_integerWindow_iff]
    rcases haN with ⟨hlo, hhi⟩
    constructor <;> linarith⟩

/-- Every exterior-Fock vector lies in the subalgebra generated by one-particle
vectors supported in some symmetric cutoff `integerWindow N`. -/
theorem exteriorFock_exists_finite_integerWindow_support
    (x : FermionicFock (𝕜 := 𝕜)) :
    ∃ N : ℕ,
      x ∈ Algebra.adjoin 𝕜
        (ExteriorAlgebra.ι 𝕜 ''
          {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
            v.support ⊆ integerWindow N}) := by
  rcases exteriorFock_exists_finite_mode_support x with ⟨S, hx⟩
  rcases finite_mode_set_subset_integerWindow S with ⟨N, hSN⟩
  refine ⟨N, ?_⟩
  apply (Algebra.adjoin_mono ?_) hx
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  exact Set.mem_image_of_mem _ (fun a ha => hSN (hv ha))

/-- Stability of finite integer-window support under cutoff enlargement `N0 ≤ N`. -/
theorem exteriorFock_eventually_mem_integerWindow_adjoin
    (x : FermionicFock (𝕜 := 𝕜)) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      x ∈ Algebra.adjoin 𝕜
        (ExteriorAlgebra.ι 𝕜 ''
          {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
            v.support ⊆ integerWindow N}) := by
  rcases exteriorFock_exists_finite_integerWindow_support x with ⟨N0, hx⟩
  refine ⟨N0, ?_⟩
  intro N hN
  apply (Algebra.adjoin_mono ?_) hx
  rintro y ⟨v, hv, rfl⟩
  exact Set.mem_image_of_mem _ (fun a ha => by
    apply SplitCliffordFiniteCAR.integerWindow_mono hN a
    exact hv ha)

/-- A mode dual at index `a ∉ S` annihilates the exterior subalgebra generated by
one-particle vectors supported in `S`. -/
theorem contractLeft_intModeDual_eq_zero_of_mem_adjoin_support
    (a : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (ha : a ∉ S) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm 𝕜
      (CanonicalNormalOrdering.IntModeSpace 𝕜)))
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a) x = 0 := by
  apply contractLeft_eq_zero_of_mem_adjoin_of_forall_mem
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a)
      {v : CanonicalNormalOrdering.IntModeSpace 𝕜 | v.support ⊆ S}
      ?_ hx
  intro v hv
  exact intModeDual_eq_zero_of_support_subset_of_not_mem a v S hv ha

/-- Every fixed Fock vector `x` has a finite one-particle support `S` outside
which all canonical mode contractions vanish. -/
theorem exists_finite_mode_support_annihilation_boundary
    (x : FermionicFock (𝕜 := 𝕜)) :
    ∃ S : Finset ℤ,
      x ∈ Algebra.adjoin 𝕜
        (ExteriorAlgebra.ι 𝕜 ''
          {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
            v.support ⊆ S}) ∧
      ∀ a : ℤ, a ∉ S →
        CliffordAlgebra.contractLeft
            (Q := (0 : QuadraticForm 𝕜
              (CanonicalNormalOrdering.IntModeSpace 𝕜)))
            (CanonicalNormalOrdering.modeDual
              (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a) x = 0 := by
  rcases exteriorFock_exists_finite_mode_support x with ⟨S, hx⟩
  refine ⟨S, hx, ?_⟩
  intro a ha
  exact contractLeft_intModeDual_eq_zero_of_mem_adjoin_support a S hx ha

/-- Nonnegative sink modes `b ≥ 0` outside the finite support `S` contribute zero
to a raw CAR matrix unit `rawMatrixUnit`. -/
theorem rawMatrixUnit_apply_eq_zero_of_not_mem_support_of_nonneg
    (a b : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (hb : 0 ≤ b) (hnot : b ∉ S) :
    (CanonicalNormalOrdering.rawMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x = 0 := by
  have hb' : ¬ b < 0 := not_lt.mpr hb
  rw [CanonicalNormalOrdering.rawMatrixUnit]
  rw [CanonicalNormalOrdering.psiMinusNeg, if_neg hb']
  have hzero := contractLeft_intModeDual_eq_zero_of_mem_adjoin_support
    b S hx hnot
  change CanonicalNormalOrdering.psiPlus
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a
      (CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm 𝕜
          (CanonicalNormalOrdering.IntModeSpace 𝕜)))
        (CanonicalNormalOrdering.modeDual
          (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) b) x) = 0
  rw [hzero]
  simp

/-- Nonnegative sink modes `b ≥ 0` outside the finite support `S` contribute zero
to a normal-ordered matrix unit `normalMatrixUnit`. -/
theorem normalMatrixUnit_apply_eq_zero_of_not_mem_support_of_nonneg
    (a b : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (hb : 0 ≤ b) (hnot : b ∉ S) :
    (CanonicalNormalOrdering.normalMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x = 0 := by
  rw [CanonicalNormalOrdering.normalMatrixUnit]
  have hraw := rawMatrixUnit_apply_eq_zero_of_not_mem_support_of_nonneg
    a b S hx hb hnot
  change (CanonicalNormalOrdering.rawMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x -
    (CanonicalNormalOrdering.contractionCoeff
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) •
      ((1 : FermionicEnd (𝕜 := 𝕜)) x) = 0
  rw [hraw]
  by_cases ha : a < 0
  · have hab : a ≠ b := by omega
    have hcoeff : CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a
        (CanonicalNormalOrdering.modeVec
          (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) b) = 0 := by
      dsimp; simp [CanonicalNormalOrdering.modeDual_modeVec, hab]
    simp [CanonicalNormalOrdering.contractionCoeff, ha, hcoeff]
  · simp [CanonicalNormalOrdering.contractionCoeff, ha]

/-- For distinct negative indices `a < 0, b < 0, a ≠ b` with `a ∉ S`, the raw
matrix unit `rawMatrixUnit a b` vanishes on vectors supported in `S`. -/
theorem rawMatrixUnit_apply_eq_zero_of_negative_distinct_outside_support
    (a b : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (ha : a < 0) (hb : b < 0)
    (hab : a ≠ b) (haS : a ∉ S) :
    (CanonicalNormalOrdering.rawMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x = 0 := by
  rw [CanonicalNormalOrdering.rawMatrixUnit,
    CanonicalNormalOrdering.psiPlus, if_pos ha,
    CanonicalNormalOrdering.psiMinusNeg, if_pos hb]
  have hzero := contractLeft_intModeDual_eq_zero_of_mem_adjoin_support
    a S hx haS
  have hCAR := congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x)
    (CanonicalNormalOrdering.annih_create_anticomm
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a)
      (CanonicalNormalOrdering.modeVec
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) b))
  rw [CanonicalNormalOrdering.modeDual_modeVec] at hCAR
  have hzero' : CanonicalNormalOrdering.annih
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a) x = 0 := hzero
  have hCAR' : CanonicalNormalOrdering.annih
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a)
      (CanonicalNormalOrdering.create
        (CanonicalNormalOrdering.modeVec
          (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) b) x) +
      CanonicalNormalOrdering.create
        (CanonicalNormalOrdering.modeVec
          (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) b)
        (CanonicalNormalOrdering.annih
          (CanonicalNormalOrdering.modeDual
            (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a) x) =
      (if a = b then x else 0) := by
    by_cases h : a = b
    · subst b
      simpa [LinearMap.add_apply, LinearMap.comp_apply, Algebra.smul_def] using hCAR
    · simpa [h, LinearMap.add_apply, LinearMap.comp_apply, Algebra.smul_def] using hCAR
  rw [hzero'] at hCAR'
  simpa [hab] using hCAR'

/-- For distinct negative indices `a < 0, b < 0, a ≠ b` with `a ∉ S`, the
normal-ordered matrix unit `normalMatrixUnit a b` vanishes on vectors supported in `S`. -/
theorem normalMatrixUnit_apply_eq_zero_of_negative_distinct_outside_support
    (a b : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (ha : a < 0) (hb : b < 0)
    (hab : a ≠ b) (haS : a ∉ S) :
    (CanonicalNormalOrdering.normalMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x = 0 := by
  rw [CanonicalNormalOrdering.normalMatrixUnit]
  change (CanonicalNormalOrdering.rawMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x -
    (CanonicalNormalOrdering.contractionCoeff
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) •
      ((1 : FermionicEnd (𝕜 := 𝕜)) x) = 0
  have hraw := rawMatrixUnit_apply_eq_zero_of_negative_distinct_outside_support
    a b S hx ha hb hab haS
  have hcoeff : CanonicalNormalOrdering.contractionCoeff
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b = 0 := by
    dsimp; simp [CanonicalNormalOrdering.contractionCoeff_eq_delta_occ, hab]
  rw [hraw, hcoeff]
  simp

/-- Diagonal normal-ordered matrix unit `normalMatrixUnit a a` vanishes for
`a < 0` with `a ∉ S` on vectors supported in `S`. -/
theorem normalMatrixUnit_apply_eq_zero_of_negative_outside_support
    (a : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (ha : a < 0) (haS : a ∉ S) :
    (CanonicalNormalOrdering.normalMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a a) x = 0 := by
  rw [CanonicalNormalOrdering.normalMatrixUnit,
    CanonicalNormalOrdering.contractionCoeff_eq_delta_occ,
    if_pos rfl]
  rw [CanonicalNormalOrdering.rawMatrixUnit]
  rw [CanonicalNormalOrdering.psiPlus, if_pos ha,
    CanonicalNormalOrdering.psiMinusNeg, if_pos ha]
  have hzero := contractLeft_intModeDual_eq_zero_of_mem_adjoin_support
    a S hx haS
  have hCAR := congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x)
    (CanonicalNormalOrdering.annih_create_anticomm
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a)
      (CanonicalNormalOrdering.modeVec
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a))
  have hzero' : CanonicalNormalOrdering.annih
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a) x = 0 := hzero
  rw [CanonicalNormalOrdering.modeDual_modeVec] at hCAR
  have hCAR' : CanonicalNormalOrdering.annih
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a)
      (CanonicalNormalOrdering.create
        (CanonicalNormalOrdering.modeVec
          (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a) x) +
      CanonicalNormalOrdering.create
        (CanonicalNormalOrdering.modeVec
          (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a)
        (CanonicalNormalOrdering.annih
          (CanonicalNormalOrdering.modeDual
            (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a) x) = x := by
    dsimp; simpa [LinearMap.add_apply, LinearMap.comp_apply, Algebra.smul_def] using hCAR
  rw [hzero'] at hCAR'
  simpa [ha, CanonicalNormalOrdering.occMinus] using sub_eq_zero.mpr hCAR'

/-- For `a < 0` and `0 ≤ b` with `a ∉ S`, the raw matrix unit `rawMatrixUnit a b`
vanishes on vectors supported in `S`. -/
theorem rawMatrixUnit_apply_eq_zero_of_negative_nonnegative_outside_support
    (a b : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (ha : a < 0) (hb : 0 ≤ b) (haS : a ∉ S) :
    (CanonicalNormalOrdering.rawMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x = 0 := by
  have hb' : ¬ b < 0 := not_lt.mpr hb
  rw [CanonicalNormalOrdering.rawMatrixUnit,
    CanonicalNormalOrdering.psiPlus, if_pos ha,
    CanonicalNormalOrdering.psiMinusNeg, if_neg hb']
  have hzero := contractLeft_intModeDual_eq_zero_of_mem_adjoin_support
    a S hx haS
  have hCAR := congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x)
    (CanonicalNormalOrdering.annih_annih_anticomm
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a)
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) b))
  have hzero' : CanonicalNormalOrdering.annih
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a) x = 0 := hzero
  have hCAR' : CanonicalNormalOrdering.annih
      (CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a)
      (CanonicalNormalOrdering.annih
        (CanonicalNormalOrdering.modeDual
          (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) b) x) +
      CanonicalNormalOrdering.annih
        (CanonicalNormalOrdering.modeDual
          (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) b)
        (CanonicalNormalOrdering.annih
          (CanonicalNormalOrdering.modeDual
            (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a) x) = 0 := by
    dsimp; simpa [LinearMap.add_apply, LinearMap.comp_apply] using hCAR
  rw [hzero'] at hCAR'
  simpa using hCAR'

/-- For `a < 0` and `0 ≤ b` with `a ∉ S`, the normal-ordered matrix unit
`normalMatrixUnit a b` vanishes on vectors supported in `S`. -/
theorem normalMatrixUnit_apply_eq_zero_of_negative_nonnegative_outside_support
    (a b : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (ha : a < 0) (hb : 0 ≤ b) (haS : a ∉ S) :
    (CanonicalNormalOrdering.normalMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x = 0 := by
  rw [CanonicalNormalOrdering.normalMatrixUnit]
  change (CanonicalNormalOrdering.rawMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x -
    (CanonicalNormalOrdering.contractionCoeff
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) •
      ((1 : FermionicEnd (𝕜 := 𝕜)) x) = 0
  have hraw := rawMatrixUnit_apply_eq_zero_of_negative_nonnegative_outside_support
    a b S hx ha hb haS
  have hab : a ≠ b := by omega
  have hcoeff : CanonicalNormalOrdering.contractionCoeff
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b = 0 := by
    dsimp; simp [CanonicalNormalOrdering.contractionCoeff, ha,
      CanonicalNormalOrdering.modeDual_modeVec, hab]
  rw [hraw, hcoeff]
  simp

/-- Any nonnegative index `0 ≤ a` shifted across zero (`a + m < 0`) lies in
`integerWindow m.natAbs`. -/
theorem nonneg_index_shift_neg_mem_integerWindow
    (a m : ℤ) (ha : 0 ≤ a) (hm : a + m < 0) :
    a ∈ integerWindow m.natAbs := by
  have hm0 : m ≤ 0 := by linarith [ha, hm]
  have hmabs : (m.natAbs : ℤ) = -m :=
    Int.ofNat_natAbs_of_nonpos hm0
  rw [mem_integerWindow_iff]
  constructor
  · omega
  · omega

/-- If `a + m ∈ S`, then `a` belongs to the shifted support `S.image (fun b => b - m)`. -/
theorem mem_shifted_support_of_add_mem
    (a m : ℤ) (S : Finset ℤ) (h : a + m ∈ S) :
    a ∈ S.image (fun b => b - m) := by
  exact Finset.mem_image.mpr ⟨a + m, h, by omega⟩

/-- Three-way sign partition of non-crossing index pairs `(a, a + m)` satisfying
`¬ (0 ≤ a ∧ a + m < 0)`. -/
theorem integer_index_sign_partition
    (a m : ℤ) (hcross : ¬ (0 ≤ a ∧ a + m < 0)) :
    (a < 0 ∧ a + m < 0) ∨
      (a < 0 ∧ 0 ≤ a + m) ∨
      (0 ≤ a ∧ 0 ≤ a + m) := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ a + m
    · exact Or.inr (Or.inr ⟨ha, hb⟩)
    · exact False.elim (hcross ⟨ha, lt_of_not_ge hb⟩)
  · have ha' : a < 0 := lt_of_not_ge ha
    by_cases hb : 0 ≤ a + m
    · exact Or.inr (Or.inl ⟨ha', hb⟩)
    · exact Or.inl ⟨ha', lt_of_not_ge hb⟩

/-- Outside the support `S`, its shifted copy `S.image (fun b => b - m)`, and the
sign-crossing window, `normalMatrixUnit a (a + m)` vanishes on `x`. -/
theorem normalMatrixUnit_apply_eq_zero_of_outside_exceptional_support
    (a m : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (haS : a ∉ S)
    (haShift : a ∉ S.image (fun b => b - m))
    (hcross : ¬ (0 ≤ a ∧ a + m < 0)) :
    (CanonicalNormalOrdering.normalMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a (a + m)) x = 0 := by
  rcases integer_index_sign_partition a m hcross with hnn | hnp | hpp
  · rcases hnn with ⟨ha, hb⟩
    by_cases hab : a = a + m
    · have hm : m = 0 := by omega
      subst m
      simpa using normalMatrixUnit_apply_eq_zero_of_negative_outside_support
        a S hx ha haS
    · exact normalMatrixUnit_apply_eq_zero_of_negative_distinct_outside_support
        a (a + m) S hx ha hb hab haS
  · exact normalMatrixUnit_apply_eq_zero_of_negative_nonnegative_outside_support
      a (a + m) S hx hnp.1 hnp.2 haS
  · have hbS : a + m ∉ S := by
      intro hbS
      apply haShift
      exact mem_shifted_support_of_add_mem a m S hbS
    exact normalMatrixUnit_apply_eq_zero_of_not_mem_support_of_nonneg
      a (a + m) S hx hpp.2 hbS

/-- The union of `S`, its shifted copy `S.image (fun b => b - m)`, and
`integerWindow m.natAbs` is eventually contained in `integerWindow N`. -/
theorem exceptional_support_eventually_subset_integerWindow
    (S : Finset ℤ) (m : ℤ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((S ∪ S.image (fun b => b - m)) ∪ integerWindow m.natAbs : Set ℤ)
        ⊆ integerWindow N := by
  let E : Finset ℤ := (S ∪ S.image (fun b => b - m)) ∪ integerWindow m.natAbs
  rcases finite_mode_set_subset_integerWindow E with ⟨N0, hN0⟩
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN a ha
  exact SplitCliffordFiniteCAR.integerWindow_mono hN a
    (hN0 (by simpa [E, Set.union_assoc] using ha))

/-- Every finite support `S` is excluded outside some cutoff window `integerWindow N0`. -/
theorem finite_support_excluded_beyond_window
    (S : Finset ℤ) :
    ∃ N0 : ℕ, ∀ a : ℤ, a ∉ integerWindow N0 → a ∉ S := by
  rcases finite_mode_set_subset_integerWindow S with ⟨N0, hN0⟩
  exact ⟨N0, fun a haW haS => haW (hN0 haS)⟩

/-- Uniform bound `|a - b| ≤ K` for all pairs of indices `a, b ∈ S` in a finite support. -/
theorem finite_support_difference_bound
    (S : Finset ℤ) :
    ∃ K : ℕ, ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ (K : ℤ) := by
  let B : ℕ := S.sup Int.natAbs
  let K : ℕ := 2 * B
  refine ⟨K, ?_⟩
  intro a ha b hb
  have ha' : Int.natAbs a ≤ B := by
    dsimp [B]
    exact Finset.le_sup (f := Int.natAbs) ha
  have hb' : Int.natAbs b ≤ B := by
    dsimp [B]
    exact Finset.le_sup (f := Int.natAbs) hb
  have ha'' : |a| ≤ (B : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast ha'
  have hb'' : |b| ≤ (B : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hb'
  have hab : |a - b| ≤ |a| + |b| := by
    calc
      |a - b| = |a + (-b)| := by rw [sub_eq_add_neg]
      _ ≤ |a| + |-b| := abs_add_le _ _
      _ = |a| + |b| := by rw [abs_neg]
  calc
    |a - b| ≤ |a| + |b| := hab
    _ ≤ (K : ℤ) := by
      dsimp [K]
      omega

/-- If all pairwise differences in `S` are bounded by `K` and `K < |l|`, no
shifted index `a + l` with `a ∈ S` lies in `S`. -/
theorem finite_support_no_shift_of_large_natAbs
    (S : Finset ℤ) (K : ℕ)
    (hK : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ (K : ℤ))
    (l : ℤ) (hl : (K : ℤ) < |l|) :
    ∀ a ∈ S, ∀ b ∈ S, a + l ≠ b := by
  intro a ha b hb hab
  have hlt : |a - b| < |l| := lt_of_le_of_lt (hK a ha b hb) hl
  have heq : a - b = -l := by omega
  rw [heq, abs_neg] at hlt
  exact lt_irrefl _ hlt

/-- Disjointness of `S` and `S.image (fun b => b - l)` for shifts `|l| > K`. -/
theorem finite_support_shifted_disjoint_of_large_natAbs
    (S : Finset ℤ) (K : ℕ)
    (hK : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ (K : ℤ))
    (l : ℤ) (hl : (K : ℤ) < |l|) :
    Disjoint S (S.image (fun b => b - l)) := by
  rw [Finset.disjoint_left]
  intro a ha hshift
  rcases Finset.mem_image.mp hshift with ⟨b, hb, hab⟩
  apply finite_support_no_shift_of_large_natAbs S K hK l hl a ha b hb
  omega

/-- For `a ∈ S` and `|l| > K`, the shifted index `a + l` lies outside `S`. -/
theorem finite_support_add_not_mem_of_large_natAbs
    (S : Finset ℤ) (K : ℕ)
    (hK : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ (K : ℤ))
    (l : ℤ) (hl : (K : ℤ) < |l|) :
    ∀ a ∈ S, a + l ∉ S := by
  intro a ha hb
  exact (finite_support_no_shift_of_large_natAbs S K hK l hl a ha (a + l) hb rfl)

/-- For `a ∈ S` and `0 ≤ l` with `K < l.natAbs`, the shifted index `a + l` lies outside `S`. -/
theorem finite_support_add_not_mem_of_large_positive_mode
    (S : Finset ℤ) (K : ℕ)
    (hK : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ (K : ℤ))
    (l : ℤ) (hl : 0 ≤ l) (hlarge : (K : ℕ) < l.natAbs) :
    ∀ a ∈ S, a + l ∉ S := by
  apply finite_support_add_not_mem_of_large_natAbs S K hK l
  have hlarge' : (K : ℤ) < l := by
    calc
      (K : ℤ) < (l.natAbs : ℤ) := by exact_mod_cast hlarge
      _ = l := Int.ofNat_natAbs_of_nonneg hl
  simpa [abs_of_nonneg hl] using hlarge'

/-- Any `a ∈ integerWindow B` shifted by `l > 2 * B` is nonnegative (`0 ≤ a + l`). -/
theorem nonneg_add_of_mem_integerWindow_of_large_positive_shift
    (B : ℕ) (a l : ℤ) (ha : a ∈ integerWindow B)
    (hl : 0 ≤ l) (hlarge : (2 * B : ℤ) < l) :
    0 ≤ a + l := by
  rw [mem_integerWindow_iff] at ha
  linarith [ha.1, hl, hlarge]

/-- Lower bound `-(B : ℤ) ≤ a` for `a ∈ integerWindow B`. -/
theorem integerWindow_lower_bound
    (B : ℕ) (a : ℤ) (ha : a ∈ integerWindow B) :
    -(B : ℤ) ≤ a := by
  have h := (mem_integerWindow_iff B a).1 ha
  exact h.1

/-- Upper bound `a ≤ (B : ℤ)` for `a ∈ integerWindow B`. -/
theorem integerWindow_upper_bound
    (B : ℕ) (a : ℤ) (ha : a ∈ integerWindow B) :
    a ≤ (B : ℤ) := by
  have h := (mem_integerWindow_iff B a).1 ha
  exact h.2

/-- Conversion from `Int.natAbs a ≤ B` to `|a| ≤ (B : ℤ)`. -/
theorem natAbs_bound_to_abs_bound
    (B : ℕ) (a : ℤ) (ha : Int.natAbs a ≤ B) :
    |a| ≤ (B : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast ha

/-- Vanishing of `normalMatrixUnit a (a + l) x` for `a ∈ S ⊆ integerWindow B`
and large positive shift `l > 2 * B` with `a + l ∉ S`. -/
theorem normalMatrixUnit_apply_eq_zero_of_window_large_positive_shift
    (S : Finset ℤ) (B : ℕ)
    (hS : ∀ a ∈ S, a ∈ integerWindow B)
    (x : FermionicFock (𝕜 := 𝕜))
    (hx : x ∈ Algebra.adjoin 𝕜
      (⇑(ExteriorAlgebra.ι 𝕜) '' {v | v.support ⊆ S}))
    (a l : ℤ) (ha : a ∈ S) (hl : 0 ≤ l)
    (hlarge : (2 * B : ℤ) < l)
    (hshift : a + l ∉ S) :
    CanonicalNormalOrdering.normalMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a (a + l) x = 0 := by
  have haW : a ∈ integerWindow B := hS a ha
  have hnonneg : 0 ≤ a + l :=
    nonneg_add_of_mem_integerWindow_of_large_positive_shift B a l haW hl hlarge
  exact normalMatrixUnit_apply_eq_zero_of_not_mem_support_of_nonneg
    a (a + l) S hx hnonneg hshift

/-- For `0 ≤ a` and `l > 2 * B`, the shifted index `a + l` lies outside any
`S ⊆ integerWindow B`. -/
theorem shifted_index_not_mem_of_nonneg_index_large_positive_shift
    (S : Finset ℤ) (B : ℕ)
    (hS : ∀ b ∈ S, b ∈ integerWindow B)
    (a l : ℤ) (ha : 0 ≤ a) (hl : 0 ≤ l)
    (hlarge : (2 * B : ℤ) < l) :
    a + l ∉ S := by
  intro hb
  have hbW : a + l ∈ integerWindow B := hS (a + l) hb
  rw [mem_integerWindow_iff] at hbW
  linarith [ha, hl, hlarge, hbW.2]

/-- Both sign branches of `a + l` yield `normalMatrixUnit a (a + l) x = 0` when
`a < 0`, `a ∉ S`, and `0 < l`. -/
theorem normalMatrixUnit_apply_eq_zero_of_negative_index_positive_shift
    (S : Finset ℤ) (x : FermionicFock (𝕜 := 𝕜))
    (hx : x ∈ Algebra.adjoin 𝕜
      (⇑(ExteriorAlgebra.ι 𝕜) '' {v | v.support ⊆ S}))
    (a l : ℤ) (ha : a ∉ S) (ha0 : a < 0) (hl : 0 < l) :
    (0 ≤ a + l →
      CanonicalNormalOrdering.normalMatrixUnit
        (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a (a + l) x = 0) ∧
    (a + l < 0 →
      CanonicalNormalOrdering.normalMatrixUnit
        (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a (a + l) x = 0) := by
  constructor
  · intro hb0
    exact normalMatrixUnit_apply_eq_zero_of_negative_nonnegative_outside_support
      a (a + l) S hx ha0 hb0 ha
  · intro hb0
    have hab : a ≠ a + l := by linarith [hl]
    exact normalMatrixUnit_apply_eq_zero_of_negative_distinct_outside_support
      a (a + l) S hx ha0 hb0 hab ha

/-- Vanishing of `normalMatrixUnit a (a + l) x` for `a ∈ S` under a shift `l`
exceeding the diameter bound `K` of `S`. -/
theorem normalMatrixUnit_apply_eq_zero_of_large_positive_shift_on_support
    (S : Finset ℤ) (x : FermionicFock (𝕜 := 𝕜))
    (hx : x ∈ Algebra.adjoin 𝕜
      (⇑(ExteriorAlgebra.ι 𝕜) '' {v | v.support ⊆ S}))
    (a : ℤ) (ha : a ∈ S) (l : ℤ) (hl : 0 ≤ l)
    (hlarge : ∃ K : ℕ, (∀ c ∈ S, ∀ d ∈ S, |c - d| ≤ (K : ℤ)) ∧
      (K : ℕ) < l.natAbs) (hbl : 0 ≤ a + l) :
    CanonicalNormalOrdering.normalMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a (a + l) x = 0 := by
  rcases hlarge with ⟨K, hK, hKl⟩
  have hbS : a + l ∉ S :=
    finite_support_add_not_mem_of_large_positive_mode S K hK l hl hKl a ha
  exact normalMatrixUnit_apply_eq_zero_of_not_mem_support_of_nonneg
    a (a + l) S hx hbl hbS

/-- Uniform vanishing of `normalMatrixUnit a (a + l) x` for all `a : ℤ` when
`S ⊆ integerWindow B` and `l > 2 * B`. -/
theorem normalMatrixUnit_apply_eq_zero_of_positive_shift_window_bound
    (S : Finset ℤ) (B : ℕ)
    (hS : ∀ b ∈ S, b ∈ integerWindow B)
    (x : FermionicFock (𝕜 := 𝕜))
    (hx : x ∈ Algebra.adjoin 𝕜
      (⇑(ExteriorAlgebra.ι 𝕜) '' {v | v.support ⊆ S}))
    (a l : ℤ) (hl : 0 < l) (hlarge : (2 * B : ℤ) < l) :
    CanonicalNormalOrdering.normalMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a (a + l) x = 0 := by
  by_cases ha : a ∈ S
  · have hshift : a + l ∉ S := by
      intro hb
      have haW := hS a ha
      have hbW := hS (a + l) hb
      have haL := integerWindow_lower_bound B a haW
      have hbU := integerWindow_upper_bound B (a + l) hbW
      omega
    exact normalMatrixUnit_apply_eq_zero_of_window_large_positive_shift
      S B hS x hx a l ha (le_of_lt hl) hlarge hshift
  · by_cases ha0 : 0 ≤ a
    · have hshift := shifted_index_not_mem_of_nonneg_index_large_positive_shift
        S B hS a l ha0 (le_of_lt hl) hlarge
      exact normalMatrixUnit_apply_eq_zero_of_not_mem_support_of_nonneg
        a (a + l) S hx (by omega) hshift
    · have hcases := normalMatrixUnit_apply_eq_zero_of_negative_index_positive_shift
        S x hx a l ha (lt_of_not_ge ha0) hl
      by_cases hb0 : 0 ≤ a + l
      · exact hcases.1 hb0
      · exact hcases.2 (lt_of_not_ge hb0)

/-- Eventual inclusion of the two-shift exceptional support set in `integerWindow N`. -/
theorem two_shift_exceptional_support_eventually_subset_integerWindow
    (S : Finset ℤ) (m n : ℤ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (((S ∪ S.image (fun b => b - m)) ∪
          S.image (fun b => b - n)) ∪
          integerWindow (max m.natAbs n.natAbs) : Set ℤ) ⊆
        integerWindow N := by
  let E : Finset ℤ :=
    ((S ∪ S.image (fun b => b - m)) ∪
      S.image (fun b => b - n)) ∪
      integerWindow (max m.natAbs n.natAbs)
  rcases finite_mode_set_subset_integerWindow E with ⟨N0, hN0⟩
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN a ha
  exact SplitCliffordFiniteCAR.integerWindow_mono hN a
    (hN0 (by simpa [E, Set.union_assoc] using ha))

/-- Pointwise eventual vanishing of each bulk-boundary diagonal summand at fixed index `a`. -/
theorem fermionicBulkBoundaryDiagonalTerm_apply_eventually_zero
    (m n a : ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
        (fermionicRawCAR (𝕜 := 𝕜)) N m n a) x = 0 := by
  rcases RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm_eventually_zero
      (fermionicRawCAR (𝕜 := 𝕜)) m n a with ⟨N0, hN0⟩
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN
  exact congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x) (hN0 N hN)

/-- Vanishing of a bulk-boundary diagonal summand when both shifted indices
`a + m` and `a + n` have the same membership in `integerWindow N`. -/
theorem fermionicBulkBoundaryDiagonalTerm_eq_zero_of_same_shift_membership
    (N : ℕ) (m n a : ℤ)
    (hmem : (a + m ∈ integerWindow N) ↔ (a + n ∈ integerWindow N))
    (x : FermionicFock (𝕜 := 𝕜)) :
    (RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
      (fermionicRawCAR (𝕜 := 𝕜)) N m n a) x = 0 := by
  have h := RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm_eq_zero_of_same_shift_membership
    (fermionicRawCAR (𝕜 := 𝕜)) N m n a hmem
  exact congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x) h

/-- Vanishing of a bulk-boundary diagonal summand when the endpoint matrix unit
`matrixUnit a (a + m + n)` annihilates `x`. -/
theorem fermionicBulkBoundaryDiagonalTerm_eq_zero_of_endpoint_vanish
    (N : ℕ) (m n a : ℤ) (x : FermionicFock (𝕜 := 𝕜))
    (hendpoint :
      (RawCARModeCompletion.matrixUnit
        (fermionicRawCAR (𝕜 := 𝕜)) a (a + m + n)) x = 0) :
    (RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
      (fermionicRawCAR (𝕜 := 𝕜)) N m n a) x = 0 := by
  unfold RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
  simp only [add_assoc, add_left_comm, add_comm]
  have hend :
      (RawCARModeCompletion.matrixUnit
        (fermionicRawCAR (𝕜 := 𝕜)) a (m + (n + a))) x = 0 := by
    convert hendpoint using 1 <;> simp [add_assoc, add_comm, add_left_comm]
  by_cases hm : a + m ∈ integerWindow N
  · have hm' : m + a ∈ cutoffWindow N := by
      dsimp; simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hm
    by_cases hn : a + n ∈ integerWindow N
    · have hn' : n + a ∈ cutoffWindow N := by
        dsimp; simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hn
      simp [hm', hn', hend]
    · have hn' : n + a ∉ cutoffWindow N := by
        dsimp; simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hn
      simp [hm', hn', hend]
  · have hm' : m + a ∉ cutoffWindow N := by
      dsimp; simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hm
    by_cases hn : a + n ∈ integerWindow N
    · have hn' : n + a ∈ cutoffWindow N := by
        dsimp; simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hn
      simp [hm', hn', hend]
    · have hn' : n + a ∉ cutoffWindow N := by
        dsimp; simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hn
      simp [hm', hn', hend]

/-- Vanishing of `fermionicRawCAR.matrixUnit a (a + k) x` outside the exceptional
support set for shift `k`. -/
theorem fermionicMatrixUnit_apply_eq_zero_of_outside_exceptional_support
    (a k : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S}))
    (haS : a ∉ S)
    (haShift : a ∉ S.image (fun b => b - k))
    (hcross : ¬ (0 ≤ a ∧ a + k < 0)) :
    (RawCARModeCompletion.matrixUnit
      (fermionicRawCAR (𝕜 := 𝕜)) a (a + k)) x = 0 := by
  have hz := normalMatrixUnit_apply_eq_zero_of_outside_exceptional_support
    a k S hx haS haShift hcross
  change ((exteriorFockRawCAR
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜))).matrixUnit a (a + k)) x = 0
  rw [exteriorFockRawCAR_matrixUnit_eq_normalMatrixUnit]
  exact hz

/-- Vanishing of `cutoffBulkBoundaryDiagonalTerm N m n a x` outside the
exceptional support set for shift `m + n`. -/
theorem fermionicBulkBoundaryDiagonalTerm_apply_eq_zero_of_outside_exceptional_support
    (N : ℕ) (m n a : ℤ) (S : Finset ℤ)
    {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S}))
    (haS : a ∉ S)
    (haShift : a ∉ S.image (fun b => b - (m + n)))
    (hcross : ¬ (0 ≤ a ∧ a + (m + n) < 0)) :
    (RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
      (fermionicRawCAR (𝕜 := 𝕜)) N m n a) x = 0 := by
  have hz := normalMatrixUnit_apply_eq_zero_of_outside_exceptional_support
    a (m + n) S hx haS haShift hcross
  have hend' :
      ((exteriorFockRawCAR
        (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜))).matrixUnit
        a (m + (n + a))) x = 0 := by
    rw [exteriorFockRawCAR_matrixUnit_eq_normalMatrixUnit]
    convert hz using 1 <;> simp [add_assoc, add_comm, add_left_comm]
  by_cases hm : m + a ∈ cutoffWindow N <;>
    by_cases hn : n + a ∈ cutoffWindow N
  all_goals
    have hm' := hm
    have hn' := hn
    simp [RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm, hm', hn',
      fermionicRawCAR, canonicalExteriorFockRawCAR,
      directSumExteriorFockRawCAR, hend', add_assoc, add_comm, add_left_comm]

/-- Eventual inclusion of the boundary exceptional support set in `integerWindow N`. -/
theorem boundary_exceptional_support_eventually_subset_integerWindow
    (S : Finset ℤ) (m n : ℤ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((S ∪ S.image (fun b => b - (m + n))) ∪
          integerWindow (max m.natAbs (m + n).natAbs) : Set ℤ) ⊆ integerWindow N := by
  let E : Finset ℤ :=
    (S ∪ S.image (fun b => b - (m + n))) ∪
      integerWindow (max m.natAbs (m + n).natAbs)
  rcases finite_mode_set_subset_integerWindow E with ⟨N0, hN0⟩
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN a ha
  exact SplitCliffordFiniteCAR.integerWindow_mono hN a
    (hN0 (by simpa [E, Set.union_assoc] using ha))

/-- Pointwise eventual vanishing of the bulk-boundary commutator term
`cutoffBulkBoundaryTerm N m n x`. -/
theorem fermionicBulkBoundaryTerm_apply_eventually_zero
    (m n : ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (RawCARModeCompletion.cutoffBulkBoundaryTerm
        (fermionicRawCAR (𝕜 := 𝕜)) N m n) x = 0 := by
  rcases exteriorFock_exists_finite_mode_support x with ⟨S, hx⟩
  let E : Finset ℤ :=
    (S ∪ S.image (fun b => b - (m + n))) ∪
      integerWindow (max m.natAbs (m + n).natAbs)
  rcases finite_mode_set_subset_integerWindow E with ⟨N0, hE⟩
  rcases RawCARModeCompletion.cutoffBulkBoundaryDiagonalSum_eventually_zero_on_finset
      (fermionicRawCAR (𝕜 := 𝕜)) m n E with ⟨N1, hN1⟩
  filter_upwards [Filter.eventually_ge_atTop (max N0 N1)] with N hN
  rw [RawCARModeCompletion.cutoffBulkBoundaryTerm_eq_reindexedBulkBoundaryTerm]
  unfold RawCARModeCompletion.cutoffReindexedBulkBoundaryTerm
  have hsub : E ⊆ integerWindow N := by
    intro a ha
    exact SplitCliffordFiniteCAR.integerWindow_mono
      (Nat.le_trans (Nat.le_max_left _ _) hN) a (hE ha)
  have hsum :
      (∑ a ∈ E,
        RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
          (fermionicRawCAR (𝕜 := 𝕜)) N m n a) x =
      (∑ a ∈ integerWindow N,
        RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
          (fermionicRawCAR (𝕜 := 𝕜)) N m n a) x := by
    dsimp; simp only [LinearMap.sum_apply]
    apply Finset.sum_subset hsub
    intro a haN haE
    have haS : a ∉ S := by
      intro ha
      exact haE (by simp [E, ha])
    have haShift : a ∉ S.image (fun b => b - (m + n)) := by
      intro ha
      exact haE (by simp [E, ha])
    have hcross : ¬ (0 ≤ a ∧ a + (m + n) < 0) := by
      intro hc
      have hw := nonneg_index_shift_neg_mem_integerWindow a (m + n) hc.1 hc.2
      exact haE (Finset.mem_union_right _
        (SplitCliffordFiniteCAR.integerWindow_mono
          (Nat.le_max_right _ _) a hw))
    exact fermionicBulkBoundaryDiagonalTerm_apply_eq_zero_of_outside_exceptional_support
      N m n a S hx haS haShift hcross
  calc
    (∑ a ∈ integerWindow N,
        RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
          (fermionicRawCAR (𝕜 := 𝕜)) N m n a) x =
        (∑ a ∈ E,
          RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
            (fermionicRawCAR (𝕜 := 𝕜)) N m n a) x := by
      exact hsum.symm
    _ = 0 := by
      dsimp; simpa using congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x)
        (hN1 N (Nat.le_trans (Nat.le_max_right _ _) hN))

/-- Pointwise eventual vanishing of the cutoff boundary term when `m + n ≠ 0`. -/
theorem fermionicBoundaryTerm_apply_eventually_zero_of_add_ne_zero
    (m n : ℤ) (hmn : m + n ≠ 0) (x : FermionicFock (𝕜 := 𝕜)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (RawCARModeCompletion.cutoffBoundaryTerm
        (fermionicRawCAR (𝕜 := 𝕜)) N m n) x = 0 := by
  filter_upwards [fermionicBulkBoundaryTerm_apply_eventually_zero m n x]
    with N hbulk
  unfold RawCARModeCompletion.cutoffBoundaryTerm
  rw [RawCARModeCompletion.cutoffActualCentralTerm_eq_zero_of_add_ne_zero
    (fermionicRawCAR (𝕜 := 𝕜)) N m n hmn]
  simp [RawCARModeCompletion.cutoffWindowCrossingTerm, hmn, hbulk]

/-- Reduction of `cutoffActualCentralTerm N m n` to a single sum over
`integerWindow N` when `m + n = 0`. -/
theorem cutoffActualCentralTerm_eq_restrictedCrossing_of_add_eq_zero
    (N : ℕ) (m n : ℤ) (hmn : m + n = 0) :
    RawCARModeCompletion.cutoffActualCentralTerm
        (fermionicRawCAR (𝕜 := 𝕜)) N m n =
      ∑ a ∈ integerWindow N,
        if a + m ∈ integerWindow N then
          (occ a - occ (a + m)) •
            (fermionicRawCAR (𝕜 := 𝕜)).central
        else 0 := by
  have hn : n = -m := eq_neg_of_add_eq_zero_right hmn
  rw [hn]
  unfold RawCARModeCompletion.cutoffActualCentralTerm
  apply Finset.sum_congr rfl
  intro a ha
  have hinner :
      (∑ b ∈ cutoffWindow N,
        if a + m = b ∧ a = b + -m then
          (occ a - occ (a + m)) • (fermionicRawCAR (𝕜 := 𝕜)).central
        else 0) =
      if a + m ∈ cutoffWindow N then
        (occ a - occ (a + m)) • (fermionicRawCAR (𝕜 := 𝕜)).central
      else 0 := by
    rw [show (∑ b ∈ cutoffWindow N,
        if a + m = b ∧ a = b + -m then
          (occ a - occ (a + m)) • (fermionicRawCAR (𝕜 := 𝕜)).central
        else 0) =
        ∑ b ∈ cutoffWindow N,
          if a + m = b then
            (occ a - occ (a + m)) • (fermionicRawCAR (𝕜 := 𝕜)).central
          else 0 by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : a + m = b <;> simp [h] <;> omega]
    rw [Finset.sum_ite_eq]
  rw [hinner]
  rfl

/-- Agreement of the actual central term and the window-crossing term for
cutoff `N ≥ m.natAbs`. -/
theorem fermionicActualCentralTerm_eq_crossing_of_large_cutoff
    (N : ℕ) (m : ℤ) (hN : m.natAbs ≤ N) :
    (RawCARModeCompletion.cutoffActualCentralTerm
      (fermionicRawCAR (𝕜 := 𝕜)) N m (-m) -
      RawCARModeCompletion.cutoffWindowCrossingTerm
        (fermionicRawCAR (𝕜 := 𝕜)) N m (-m)) = 0 := by
  have hbal :=
    InfoGeometry.Canonical.SplitCliffordCurrentCommutator.RawCARModeCompletion.edge_occ_balance_of_natAbs_le N m hN
  exact
    InfoGeometry.Canonical.SplitCliffordCurrentCommutator.RawCARModeCompletion.current_central_edge_correction_eq_zero_of_edge_occ_balance
      (fermionicRawCAR (𝕜 := 𝕜)) N m hbal

/-- Pointwise eventual vanishing of the cutoff boundary term when `m + n = 0`. -/
theorem fermionicBoundaryTerm_apply_eventually_zero_of_add_eq_zero
    (m n : ℤ) (hmn : m + n = 0) (x : FermionicFock (𝕜 := 𝕜)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (RawCARModeCompletion.cutoffBoundaryTerm
        (fermionicRawCAR (𝕜 := 𝕜)) N m n) x = 0 := by
  have hn : n = -m := eq_neg_of_add_eq_zero_right hmn
  rw [hn]
  filter_upwards [fermionicBulkBoundaryTerm_apply_eventually_zero m (-m) x,
    Filter.eventually_ge_atTop m.natAbs] with N hbulk hN
  unfold RawCARModeCompletion.cutoffBoundaryTerm
  rw [fermionicActualCentralTerm_eq_crossing_of_large_cutoff N m hN]
  simp [hbulk]

/-- Pointwise eventual vanishing of the represented cutoff boundary term for all
mode pairs `(m, n)`. -/
theorem fermionicEndomorphismBoundaryTerm_apply_eventually_zero
    (m n : ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (RingHom.id _)
          (RawCARModeCompletion.cutoffBoundaryTerm
            (fermionicRawCAR (𝕜 := 𝕜)) N m n) x = 0 := by
  by_cases hmn : m + n = 0
  · simpa using
      (fermionicBoundaryTerm_apply_eventually_zero_of_add_eq_zero m n hmn x)
  · simpa using
      (fermionicBoundaryTerm_apply_eventually_zero_of_add_ne_zero m n hmn x)

/-- Eventual vanishing of the bulk-boundary diagonal sum over a fixed cutoff
window `integerWindow K`. -/
theorem fermionicBulkBoundaryDiagonalSum_apply_eventually_zero_on_window
    (m n : ℤ) (K : ℕ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (∑ a ∈ integerWindow K,
        (RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
          (fermionicRawCAR (𝕜 := 𝕜)) N m n a)) x = 0 := by
  rcases RawCARModeCompletion.cutoffBulkBoundaryDiagonalSum_eventually_zero_on_finset
      (fermionicRawCAR (𝕜 := 𝕜)) m n (integerWindow K) with ⟨N0, hN0⟩
  exact ⟨N0, fun N hN => by
    simpa using congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x) (hN0 N hN)⟩

/-- Eventual vanishing of the bulk-boundary diagonal sum over an arbitrary finite
set `S : Finset ℤ`. -/
theorem fermionicBulkBoundaryDiagonalSum_apply_eventually_zero_on_finset
    (m n : ℤ) (S : Finset ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (∑ a ∈ S,
        (RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
          (fermionicRawCAR (𝕜 := 𝕜)) N m n a)) x = 0 := by
  rcases RawCARModeCompletion.cutoffBulkBoundaryDiagonalSum_eventually_zero_on_finset
      (fermionicRawCAR (𝕜 := 𝕜)) m n S with ⟨N0, hN0⟩
  exact ⟨N0, fun N hN => by
    simpa using congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x) (hN0 N hN)⟩

/-- Finite-cutoff normal-ordered fermionic current `fermionicRawCAR.cutoffCurrent N m`. -/
def fermionicCutoffCurrent (N : ℕ) (m : ℤ) : FermionicEnd (𝕜 := 𝕜) :=
  (fermionicRawCAR (𝕜 := 𝕜)).cutoffCurrent N m

/-- Expansion of `fermionicCutoffCurrent N m` as a finite sum over `integerWindow N`. -/
theorem fermionicCutoffCurrent_eq_sum (N : ℕ) (m : ℤ) :
    fermionicCutoffCurrent (𝕜 := 𝕜) N m =
      ∑ a ∈ integerWindow N,
        (fermionicRawCAR (𝕜 := 𝕜)).matrixUnit a (a + m) := by
  unfold fermionicCutoffCurrent RawCARModeCompletion.cutoffCurrent
  rfl

/-- Expansion of `fermionicCutoffCurrent N m` in terms of `normalMatrixUnit`. -/
theorem fermionicCutoffCurrent_eq_normalMatrixUnit_sum (N : ℕ) (m : ℤ) :
    fermionicCutoffCurrent (𝕜 := 𝕜) N m =
      ∑ a ∈ integerWindow N,
        CanonicalNormalOrdering.normalMatrixUnit
          (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
          (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a (a + m) := by
  rw [fermionicCutoffCurrent_eq_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simpa [fermionicRawCAR, canonicalExteriorFockRawCAR, directSumExteriorFockRawCAR] using
    (exteriorFockRawCAR_matrixUnit_eq_normalMatrixUnit
    (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
    (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a (a + m))

/-- Pointwise stabilization of `fermionicCutoffCurrent N m x` for `N ≥ N0`. -/
theorem fermionicCutoffCurrent_apply_stabilizes_of_finite_support
    (m : ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (fermionicCutoffCurrent (𝕜 := 𝕜) N m) x =
        (fermionicCutoffCurrent (𝕜 := 𝕜) N0 m) x := by
  rcases exteriorFock_exists_finite_mode_support x with ⟨S, hx⟩
  let E : Finset ℤ := (S ∪ S.image (fun b => b - m)) ∪ integerWindow m.natAbs
  rcases finite_mode_set_subset_integerWindow E with ⟨N0, hE⟩
  refine ⟨N0, ?_⟩
  intro N hN
  rw [fermionicCutoffCurrent_eq_normalMatrixUnit_sum,
    fermionicCutoffCurrent_eq_normalMatrixUnit_sum]
  simp only [LinearMap.sum_apply]
  symm
  apply Finset.sum_subset
  · exact SplitCliffordFiniteCAR.integerWindow_mono hN
  · intro a haN haN0
    by_cases haE : a ∈ E
    · exact False.elim (haN0 (hE haE))
    · apply normalMatrixUnit_apply_eq_zero_of_outside_exceptional_support
        a m S hx
      · intro haS
        exact haE (by simp [E, haS])
      · intro haShift
        exact haE (by simp [E, haShift])
      · intro hcross
        exact haE (by
          rcases hcross with ⟨ha, hb⟩
          simp [E, ha,
            nonneg_index_shift_neg_mem_integerWindow a m ha hb])

/-- Eventual stabilization of `fermionicCutoffCurrent N m x` along `Filter.atTop`. -/
theorem fermionicCutoffCurrent_apply_eventually_eq_stabilized
    (m : ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∃ N0 : ℕ, ∀ᶠ N : ℕ in Filter.atTop,
      (fermionicCutoffCurrent (𝕜 := 𝕜) N m) x =
        (fermionicCutoffCurrent (𝕜 := 𝕜) N0 m) x := by
  rcases fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x with
    ⟨N0, hN0⟩
  exact ⟨N0, Filter.eventually_atTop.2 ⟨N0, hN0⟩⟩

/-- Stabilized fermionic current mode endomorphism `fermionicCurrentMode m` on
`FermionicFock`. -/
noncomputable def fermionicCurrentMode (m : ℤ) : FermionicEnd (𝕜 := 𝕜) :=
  { toFun := fun x =>
      (fermionicCutoffCurrent (𝕜 := 𝕜)
        (Classical.choose
          (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x)) m) x
    map_add' := by
      intro x y
      let Nx := Classical.choose
        (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x)
      let Ny := Classical.choose
        (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m y)
      let Nxy := Classical.choose
        (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m (x + y))
      let M := max (max Nx Ny) Nxy
      have hx := Classical.choose_spec
        (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x)
        M (le_max_of_le_left (le_max_left _ _))
      have hy := Classical.choose_spec
        (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m y)
        M (le_max_of_le_left (le_max_right _ _))
      have hxy := Classical.choose_spec
        (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m (x + y))
        M (le_max_right _ _)
      rw [← hx, ← hy, ← hxy]
      exact (fermionicCutoffCurrent (𝕜 := 𝕜) M m).map_add x y
    map_smul' := by
      intro c x
      let Nx := Classical.choose
        (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x)
      let Ncx := Classical.choose
        (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m (c • x))
      let M := max Nx Ncx
      have hx := Classical.choose_spec
        (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x)
        M (le_max_left _ _)
      have hcx := Classical.choose_spec
        (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m (c • x))
        M (le_max_right _ _)
      rw [← hx, ← hcx]
      exact (fermionicCutoffCurrent (𝕜 := 𝕜) M m).map_smul c x
  }

/-- Pointwise evaluation formula for `fermionicCurrentMode m x`. -/
@[simp] theorem fermionicCurrentMode_apply (m : ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    fermionicCurrentMode (𝕜 := 𝕜) m x =
      (fermionicCutoffCurrent (𝕜 := 𝕜)
        (Classical.choose
          (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x)) m) x := by
  unfold fermionicCurrentMode
  rfl

/-- Pointwise eventual agreement of `fermionicCutoffCurrent N m x` with
`fermionicCurrentMode m x`. -/
theorem fermionicCutoffCurrent_eventually_eq_fermionicCurrentMode
    (m : ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (fermionicCutoffCurrent (𝕜 := 𝕜) N m) x =
        fermionicCurrentMode (𝕜 := 𝕜) m x := by
  let N0 := Classical.choose
    (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x)
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN
  rw [fermionicCurrentMode_apply]
  exact Classical.choose_spec
    (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x) N hN

/-- Vacuum expectation value of `fermionicCurrentMode m` vanishes. -/
theorem fermionicCurrentMode_vacuumExpect_zero (m : ℤ) :
    vacuumExpectEnd (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (fermionicCurrentMode (𝕜 := 𝕜) m) = 0 := by
  change vacuumCoeff (R := 𝕜)
    (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      ((fermionicCurrentMode (𝕜 := 𝕜) m) 1) = 0
  rw [fermionicCurrentMode_apply]
  rw [fermionicCutoffCurrent_eq_normalMatrixUnit_sum]
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  exact normalMatrixUnit_vacuumCoeff_apply_vacuum_zero_directSum 𝕜 a (a + m)

/-- Vacuum expectation value of the finite cutoff current `fermionicCutoffCurrent N m`
vanishes for every cutoff `N`. -/
theorem fermionicCutoffCurrent_vacuumExpect_zero (N : ℕ) (m : ℤ) :
    vacuumExpectEnd (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
        (fermionicCutoffCurrent (𝕜 := 𝕜) N m) = 0 := by
  rw [fermionicCutoffCurrent_eq_normalMatrixUnit_sum]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  exact normalMatrixUnit_vacuumExpect_zero_directSum 𝕜 a (a + m)

/-- Eventual vanishing of the vacuum expectation of `fermionicCutoffCurrent N m`. -/
theorem fermionicCutoffCurrent_vacuumExpect_eventually_eq (m : ℤ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      vacuumExpectEnd (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
        (fermionicCutoffCurrent (𝕜 := 𝕜) N m) = 0 := by
  apply Filter.Eventually.of_forall
  intro N
  exact fermionicCutoffCurrent_vacuumExpect_zero N m

/-- Coefficientwise stabilization of `cutoffDiagonalCurrent N m` to `completedCurrent m`. -/
theorem fermionicCurrent_coefficientwise_completion (m : ℤ) :
    ∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j := by
  intro i j
  exact cutoffDiagonalCurrent_coeff_eventually_eq_completed m i j

/-- Filter form of coefficientwise stabilization of `cutoffDiagonalCurrent N m`. -/
theorem fermionicCurrent_coefficientwise_eventually_eq (m i j : ℤ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j := by
  rcases fermionicCurrent_coefficientwise_completion m i j with ⟨N0, hN0⟩
  exact Filter.eventually_atTop.2 ⟨N0, hN0⟩

/-- Joint coefficientwise stabilization and completed CCR commutator identity for
modes `m` and `n`. -/
theorem fermionicCurrent_completion_summary (m n : ℤ) :
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j) ∧
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N n).coeff i j = (completedCurrent n).coeff i j) ∧
    CCRBracketCompleted (canonicalExteriorFockRawCAR (𝕜 := 𝕜))
      (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) m)
      (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) n) =
      if m + n = 0 then m • (1 : FermionicEnd (𝕜 := 𝕜)) else 0 := by
  rcases constructiveHeisenbergCurrent_from_completedCurrent
      (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) m n with ⟨hm, hn, _, _, hbr⟩
  exact ⟨hm, hn, hbr⟩

section ChargedFock

/-- Bosonic Fock carrier `ChargedFockSpace 𝕜 α`. -/
abbrev BosonicFock (α : 𝕜) : Type _ := ChargedFockSpace 𝕜 α

/-- Linear endomorphism space of `BosonicFock α`. -/
abbrev BosonicEnd (α : 𝕜) : Type _ := BosonicFock (𝕜 := 𝕜) α →ₗ[𝕜] BosonicFock (𝕜 := 𝕜) α

/-- Representation of `CompletedCurrentModeCarrier` on `BosonicFock α`. -/
noncomputable def fermionToBosonCurrent (α : 𝕜)
    (X : CompletedCurrentModeCarrier) : BosonicEnd (𝕜 := 𝕜) α :=
  representedCompletedCurrentMode α X

/-- `fermionToBosonCurrent α` sends `completedCurrentPoint m` to
`(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m`. -/
theorem fermionToBosonCurrent_mode (α : 𝕜) (m : ℤ) :
    fermionToBosonCurrent α (completedCurrentPoint m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m := by
  unfold fermionToBosonCurrent
  exact representedCompletedCurrentMode_point α m

/-- Agreement of `fermionToBosonCurrent α` with `chargedFockSpaceHeisenbergMode`. -/
theorem fermionToBosonCurrent_eq_heisenbergRepresentation (α : 𝕜)
    (X : CompletedCurrentModeCarrier) :
    fermionToBosonCurrent α X =
      chargedFockSpaceHeisenbergMode 𝕜 α
        (completedCurrentModeEquiv.symm X) := by
  unfold fermionToBosonCurrent
  exact representedCompletedCurrentMode_eq_heisenbergRepresentation α X

/-- Heisenberg mode commutator of `fermionToBosonCurrent α (completedCurrentPoint m)`
and `fermionToBosonCurrent α (completedCurrentPoint n)`. -/
theorem fermionToBosonCurrent_commutator (α : 𝕜) (m n : ℤ) :
    (fermionToBosonCurrent α (completedCurrentPoint m)).commutator
      (fermionToBosonCurrent α (completedCurrentPoint n)) =
      if m + n = 0 then (m : 𝕜) • (1 : BosonicEnd (𝕜 := 𝕜) α) else 0 := by
  unfold fermionToBosonCurrent
  exact representedCompletedCurrentMode_commutator α m n

/-- Sugawara Virasoro mode-shift action on `fermionToBosonCurrent α (completedCurrentPoint m)`. -/
theorem virasoro_acts_on_bosonizedFermionicCurrent (α : 𝕜) (r m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      (fermionToBosonCurrent α (completedCurrentPoint m)) =
      -m • fermionToBosonCurrent α (completedCurrentPoint (r + m)) := by
  unfold fermionToBosonCurrent
  exact virasoro_lgen_acts_on_completedCurrent α r m

/-- Uniform vanishing of `fermionicCutoffCurrent N l x` for all `N` when `x` is
supported in `S ⊆ integerWindow B` and `l > 2 * B`. -/
theorem fermionicCutoffCurrent_apply_eq_zero_of_positive_shift_window_bound_final
    (S : Finset ℤ) (B : ℕ) (hS : ∀ b ∈ S, b ∈ integerWindow B)
    (x : FermionicFock (𝕜 := 𝕜))
    (hx : x ∈ Algebra.adjoin 𝕜
      (⇑(ExteriorAlgebra.ι 𝕜) '' {v | v.support ⊆ S}))
    (l : ℤ) (hl : 0 < l) (hlarge : (2 * B : ℤ) < l) :
    ∀ N : ℕ, (fermionicCutoffCurrent (𝕜 := 𝕜) N l) x = 0 := by
  intro N
  rw [fermionicCutoffCurrent_eq_normalMatrixUnit_sum]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  exact normalMatrixUnit_apply_eq_zero_of_positive_shift_window_bound
    S B hS x hx a l hl hlarge

/-- Uniform vanishing of `fermionicCutoffCurrent N l x` from an existential
window bound witness. -/
theorem fermionicCutoffCurrent_apply_eq_zero_of_large_positive_mode_final
    (l : ℤ) (hl : 0 < l) (x : FermionicFock (𝕜 := 𝕜))
    (hlarge : ∃ S : Finset ℤ, ∃ B : ℕ,
      x ∈ Algebra.adjoin 𝕜
        (⇑(ExteriorAlgebra.ι 𝕜) '' {v | v.support ⊆ S}) ∧
      (∀ b ∈ S, b ∈ integerWindow B) ∧ (2 * B : ℤ) < l) :
    ∀ N : ℕ, (fermionicCutoffCurrent (𝕜 := 𝕜) N l) x = 0 := by
  rcases hlarge with ⟨S, B, hx, hB, hBl⟩
  exact fermionicCutoffCurrent_apply_eq_zero_of_positive_shift_window_bound_final
    S B hB x hx l hl hBl

/-- For every `x : FermionicFock`, `fermionicCutoffCurrent N l x = 0` for all `N`
and all sufficiently large positive modes `l`. -/
theorem fermionicCutoffCurrent_apply_eq_zero_eventually_positive_mode
    (x : FermionicFock (𝕜 := 𝕜)) :
    ∀ᶠ l : ℤ in Filter.atTop,
      ∀ N : ℕ, (fermionicCutoffCurrent (𝕜 := 𝕜) N l) x = 0 := by
  rcases exteriorFock_exists_finite_mode_support x with ⟨S, hx⟩
  let B : ℕ := S.sup Int.natAbs
  have hB : ∀ b ∈ S, b ∈ integerWindow B := by
    intro b hb
    change b ∈ integerWindow B
    rw [mem_integerWindow_iff]
    have hle : Int.natAbs b ≤ B := by
      dsimp [B]
      exact Finset.le_sup (f := Int.natAbs) hb
    have hle' : (Int.natAbs b : ℤ) ≤ (B : ℤ) := by exact_mod_cast hle
    constructor <;> by_cases h : 0 ≤ b
    · linarith
    · have h' : b ≤ 0 := le_of_not_ge h
      have hb' : (Int.natAbs b : ℤ) = -b := Int.ofNat_natAbs_of_nonpos h'
      linarith
    · have hb' : (Int.natAbs b : ℤ) = b := Int.ofNat_natAbs_of_nonneg h
      linarith
    · linarith
  filter_upwards [Filter.eventually_ge_atTop (2 * B + 1 : ℤ)] with l hl
  have hlpos : 0 < l := by omega
  have hlarge : (2 * B : ℤ) < l := by omega
  exact fermionicCutoffCurrent_apply_eq_zero_of_positive_shift_window_bound_final
    S B hB x hx l hlpos hlarge

/-- Eventual positive-mode truncation `∀ᶠ l in Filter.atTop, fermionicCurrentMode l x = 0`
for every `x : FermionicFock`. -/
theorem fermionicCurrentMode_apply_eventually_zero
    (x : FermionicFock (𝕜 := 𝕜)) :
    ∀ᶠ l : ℤ in Filter.atTop,
      (fermionicCurrentMode (𝕜 := 𝕜) l) x = 0 := by
  rcases exteriorFock_exists_finite_mode_support x with ⟨S, hx⟩
  let B : ℕ := S.sup Int.natAbs
  have hB : ∀ b ∈ S, b ∈ integerWindow B := by
    intro b hb
    change b ∈ integerWindow B
    rw [mem_integerWindow_iff]
    have hle : Int.natAbs b ≤ B := by
      dsimp [B]
      exact Finset.le_sup (f := Int.natAbs) hb
    have hle' : (Int.natAbs b : ℤ) ≤ (B : ℤ) := by exact_mod_cast hle
    constructor <;> by_cases h : 0 ≤ b
    · linarith
    · have h' : b ≤ 0 := le_of_not_ge h
      have hb' : (Int.natAbs b : ℤ) = -b := Int.ofNat_natAbs_of_nonpos h'
      linarith
    · have hb' : (Int.natAbs b : ℤ) = b := Int.ofNat_natAbs_of_nonneg h
      linarith
    · linarith
  filter_upwards [Filter.eventually_ge_atTop (2 * B + 1 : ℤ)] with l hl
  have hlpos : 0 < l := by omega
  have hlarge : (2 * B : ℤ) < l := by omega
  let N0 := Classical.choose
    (fermionicCutoffCurrent_apply_stabilizes_of_finite_support l x)
  have hEq := Classical.choose_spec
    (fermionicCutoffCurrent_apply_stabilizes_of_finite_support l x)
    N0 (le_rfl)
  rw [fermionicCurrentMode_apply]
  rw [← hEq]
  exact fermionicCutoffCurrent_apply_eq_zero_of_positive_shift_window_bound_final
    S B hB x hx l hlpos hlarge N0

/-- `StabilizedCurrentSource` instance for the exterior-Fock CAR completion and
`fermionicCurrentMode`. -/
noncomputable def fermionicStabilizedCurrentSource :
    StabilizedCurrentSource 𝕜 (FermionicEnd (𝕜 := 𝕜))
      (FermionicFock (𝕜 := 𝕜)) where
  source := fermionicRawCAR (𝕜 := 𝕜)
  ρ := RingHom.id _
  J := fermionicCurrentMode (𝕜 := 𝕜)
  trunc := fermionicCurrentMode_apply_eventually_zero
  cutoff_eventually_constant := by
    intro m x
    simpa [endomorphismCutoffCurrent, fermionicCutoffCurrent] using
      (fermionicCutoffCurrent_eventually_eq_fermionicCurrentMode m x)
  boundary_eventually_zero := by
    intro m n x
    simpa [endomorphismCutoffCurrent, fermionicCutoffCurrent] using
      (fermionicEndomorphismBoundaryTerm_apply_eventually_zero m n x)

/-- Level-1 Heisenberg mode commutator law for `fermionicCurrentMode` on `FermionicFock`. -/
theorem fermionicCurrentMode_commutator (m n : ℤ) :
    (fermionicCurrentMode (𝕜 := 𝕜) m).commutator
        (fermionicCurrentMode (𝕜 := 𝕜) n) =
      if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 (FermionicFock (𝕜 := 𝕜)))
      else 0 := by
  have h := StabilizedCurrentSource.current_commutator
    (fermionicStabilizedCurrentSource (𝕜 := 𝕜)) m n
  exact h

/-- `CurrentHeisenbergRep` on `FermionicFock` built from `fermionicCurrentMode`. -/
noncomputable def fermionicCurrentHeisenbergRep :
    CurrentHeisenbergRep 𝕜 (FermionicFock (𝕜 := 𝕜)) :=
  ⟨fermionicCurrentMode (𝕜 := 𝕜),
   fermionicCurrentMode_apply_eventually_zero,
   fermionicCurrentMode_commutator⟩

/-- Sugawara Virasoro Lie algebra representation on `FermionicFock` induced by
`fermionicCurrentHeisenbergRep`. -/
noncomputable def fermionicCurrentSugawaraRepresentation :
    VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
      Module.End 𝕜 (FermionicFock (𝕜 := 𝕜)) :=
  (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).currentSugawaraRepresentation

/-- Action of `fermionicCurrentSugawaraRepresentation` on `VirasoroAlgebra.lgen 𝕜 r`. -/
theorem fermionicCurrentSugawaraRepresentation_apply_lgen (r : ℤ) :
    fermionicCurrentSugawaraRepresentation (𝕜 := 𝕜)
        (VirasoroAlgebra.lgen 𝕜 r) =
      (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).sugawaraStressMode r := by
  unfold fermionicCurrentSugawaraRepresentation
  exact (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).currentSugawaraRepresentation_lgen_apply r

/-- Action of `fermionicCurrentSugawaraRepresentation` on `VirasoroAlgebra.cgen 𝕜`. -/
theorem fermionicCurrentSugawaraRepresentation_apply_cgen :
    fermionicCurrentSugawaraRepresentation (𝕜 := 𝕜)
        (VirasoroAlgebra.cgen 𝕜) =
      (1 : Module.End 𝕜 (FermionicFock (𝕜 := 𝕜))) := by
  unfold fermionicCurrentSugawaraRepresentation
  exact (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).currentSugawaraRepresentation_central

/-- Virasoro mode commutator identity for the Sugawara stress modes on `FermionicFock`. -/
theorem fermionicCurrentSugawara_stressMode_commutator (m n : ℤ) :
    ((fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).sugawaraStressMode m).commutator
        ((fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).sugawaraStressMode n) =
      (m - n) • (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).sugawaraStressMode (m + n) +
        (if m + n = 0 then
          ((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
            (1 : Module.End 𝕜 (FermionicFock (𝕜 := 𝕜)))
        else 0) := by
  dsimp; simpa using (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).sugawaraStressMode_virasoroBracket m n

/-- Joint summary of coefficientwise completion, charged-Fock current mode
identification, and Virasoro mode-shift action. -/
theorem fermionic_to_bosonic_current_intertwiner_summary (α : 𝕜) (r m : ℤ) :
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j) ∧
    fermionToBosonCurrent α (completedCurrentPoint m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m ∧
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      (fermionToBosonCurrent α (completedCurrentPoint m)) =
      -m • fermionToBosonCurrent α (completedCurrentPoint (r + m)) := by
  constructor
  · exact fermionicCurrent_coefficientwise_completion m
  · constructor
    · exact fermionToBosonCurrent_mode α m
    · exact virasoro_acts_on_bosonizedFermionicCurrent α r m

end ChargedFock
end InfoGeometry.Canonical.FermionicCurrentChargedFockIntertwiner
