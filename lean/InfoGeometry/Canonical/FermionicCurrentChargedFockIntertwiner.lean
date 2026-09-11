import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
import InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
import InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter
import InfoGeometry.Canonical.ExteriorAlgebraFiniteGeneration
import InfoGeometry.Canonical.SplitCliffordCurrentCommutator

/-! Fermionic cutoff currents and their native charged-Fock readout. -/

noncomputable section
namespace InfoGeometry.Canonical.FermionicCurrentChargedFockIntertwiner

open VirasoroProject
open InfoGeometry.Canonical.CanonicalNormalOrdering
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
open InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
open InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter
open InfoGeometry.Canonical.ExteriorAlgebraFiniteGeneration

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

abbrev FermionicFock : Type _ :=
  CanonicalNormalOrdering.Fock (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
abbrev FermionicEnd : Type _ :=
  CanonicalNormalOrdering.EndFock (R := 𝕜)
    (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
abbrev fermionicRawCAR :
    RawCARModeCompletion (FermionicEnd (𝕜 := 𝕜)) :=
  canonicalExteriorFockRawCAR (𝕜 := 𝕜)

/- Every finitely supported one-particle mode vector is contained in a
   symmetric integer cutoff.  This is the support leaf needed before proving
   stabilization on exterior monomials. -/
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

/- The coordinate functional of the canonical direct-sum basis sees only the
   finitely supported coefficient at its own index. -/
theorem intModeDual_eq_zero_of_support_subset_of_not_mem
    (a : ℤ) (v : CanonicalNormalOrdering.IntModeSpace 𝕜)
    (S : Finset ℤ) (hv : v.support ⊆ S) (ha : a ∉ S) :
    CanonicalNormalOrdering.modeDual
        (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a v = 0 := by
  have hav : a ∉ v.support := fun hav => ha (hv hav)
  have hcoef : v a = 0 := by
    simpa [Finsupp.mem_support_iff] using hav
  simpa [CanonicalNormalOrdering.modeDual,
    CanonicalNormalOrdering.intModeBasis, Module.Basis.coord_apply] using hcoef

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

/- The finite window witness is stable under enlargement of the cutoff.  This
   is the exact filter-level support statement needed before applying any
   operator to a fixed exterior-Fock vector. -/
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

/- A mode dual outside a finite one-particle support annihilates the whole
   exterior subalgebra generated by that support. -/
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

/- Every fixed Fock vector has a finite one-particle support outside which all
   canonical mode contractions vanish. -/
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

/- Nonnegative sink modes outside the finite support contribute zero to a raw
   normal-ordered matrix unit. -/
theorem rawMatrixUnit_apply_eq_zero_of_not_mem_support_of_nonneg
    (a b : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (hb : 0 ≤ b) (hnot : b ∉ S) :
    (CanonicalNormalOrdering.rawMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x = 0 := by
  rw [CanonicalNormalOrdering.rawMatrixUnit]
  rw [CanonicalNormalOrdering.psiMinusNeg, if_neg (by omega)]
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

/- Normal ordering does not add a vacuum-contraction term when the right
   index is nonnegative.  This is the normal-ordered form of the preceding
   support vanishing lemma. -/
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
      simp [CanonicalNormalOrdering.modeDual_modeVec, hab]
    simp [CanonicalNormalOrdering.contractionCoeff, ha, hcoeff]
  · simp [CanonicalNormalOrdering.contractionCoeff, ha]

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

/- For two distinct negative indices the vacuum contraction is also zero, so
   the normal-ordered bilinear has the same support vanishing as its raw CAR
   representative. -/
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
    simp [CanonicalNormalOrdering.contractionCoeff_eq_delta_occ, hab]
  rw [hraw, hcoeff]
  simp

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
    simpa [LinearMap.add_apply, LinearMap.comp_apply, Algebra.smul_def] using hCAR
  rw [hzero'] at hCAR'
  simpa [ha, CanonicalNormalOrdering.occMinus] using sub_eq_zero.mpr hCAR'

theorem rawMatrixUnit_apply_eq_zero_of_negative_nonnegative_outside_support
    (a b : ℤ) (S : Finset ℤ) {x : FermionicFock (𝕜 := 𝕜)}
    (hx : x ∈ Algebra.adjoin 𝕜
      (ExteriorAlgebra.ι 𝕜 ''
        {v : CanonicalNormalOrdering.IntModeSpace 𝕜 |
          v.support ⊆ S})) (ha : a < 0) (hb : 0 ≤ b) (haS : a ∉ S) :
    (CanonicalNormalOrdering.rawMatrixUnit
      (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
      (CanonicalNormalOrdering.intModeBasis (R := 𝕜)) a b) x = 0 := by
  rw [CanonicalNormalOrdering.rawMatrixUnit,
    CanonicalNormalOrdering.psiPlus, if_pos ha,
    CanonicalNormalOrdering.psiMinusNeg, if_neg (by omega)]
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
    simpa [LinearMap.add_apply, LinearMap.comp_apply] using hCAR
  rw [hzero'] at hCAR'
  simpa using hCAR'

/- In the negative-to-nonnegative branch the normal-ordering correction
   vanishes by sign alone. -/
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
    simp [CanonicalNormalOrdering.contractionCoeff, ha,
      CanonicalNormalOrdering.modeDual_modeVec, hab]
  rw [hraw, hcoeff]
  simp

/- The only potentially non-annihilating mixed-sign branch is confined to the
   finite crossing window determined by the current shift. -/
theorem nonneg_index_shift_neg_mem_integerWindow
    (a m : ℤ) (ha : 0 ≤ a) (hm : a + m < 0) :
    a ∈ integerWindow m.natAbs := by
  have hm0 : m ≤ 0 := by omega
  have hmabs : (m.natAbs : ℤ) = -m :=
    Int.ofNat_natAbs_of_nonpos hm0
  rw [mem_integerWindow_iff]
  constructor
  · omega
  · omega

/- The shifted support records precisely the indices whose translated partner
   `a + m` can lie in a given finite support. -/
theorem mem_shifted_support_of_add_mem
    (a m : ℤ) (S : Finset ℤ) (h : a + m ∈ S) :
    a ∈ S.image (fun b => b - m) := by
  exact Finset.mem_image.mpr ⟨a + m, h, by omega⟩

/- Every non-crossing index pair belongs to exactly one of the three sign
   branches used by the CAR support lemmas.  The omitted fourth branch is the
   finite crossing window handled separately. -/
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

/- Outside the finite support and shifted support, every non-crossing current
   summand vanishes.  The proof is a three-way sign split; the fourth sign
   branch is exactly the crossing window isolated above. -/
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

/- The support, its shifted copy, and the sign-crossing window form one finite
   exceptional set.  This is the cutoff-enlargement fact used to assemble the
   pointwise stabilization proof. -/
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

theorem finite_support_excluded_beyond_window
    (S : Finset ℤ) :
    ∃ N0 : ℕ, ∀ a : ℤ, a ∉ integerWindow N0 → a ∉ S := by
  rcases finite_mode_set_subset_integerWindow S with ⟨N0, hN0⟩
  exact ⟨N0, fun a haW haS => haW (hN0 haS)⟩

/- A finite support has a uniform bound on differences of its indices.  This
   is the arithmetic bound used when a shifted negative mode is compared with
   two support indices. -/
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

theorem finite_support_no_shift_of_large_natAbs
    (S : Finset ℤ) (K : ℕ)
    (hK : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ (K : ℤ))
    (l : ℤ) (hl : (K : ℤ) < |l|) :
    ∀ a ∈ S, ∀ b ∈ S, a + l ≠ b := by
  intro a ha b hb hab
  have hd : |a - b| ≤ (K : ℤ) := hK a ha b hb
  have heq : a - b = -l := by omega
  rw [heq, abs_neg] at hd
  omega

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

theorem finite_support_add_not_mem_of_large_natAbs
    (S : Finset ℤ) (K : ℕ)
    (hK : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ (K : ℤ))
    (l : ℤ) (hl : (K : ℤ) < |l|) :
    ∀ a ∈ S, a + l ∉ S := by
  intro a ha hb
  exact (finite_support_no_shift_of_large_natAbs S K hK l hl a ha (a + l) hb rfl)

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

theorem nonneg_add_of_mem_integerWindow_of_large_positive_shift
    (B : ℕ) (a l : ℤ) (ha : a ∈ integerWindow B)
    (hl : 0 ≤ l) (hlarge : (2 * B : ℤ) < l) :
    0 ≤ a + l := by
  rw [mem_integerWindow_iff] at ha
  omega

theorem integerWindow_lower_bound
    (B : ℕ) (a : ℤ) (ha : a ∈ integerWindow B) :
    -(B : ℤ) ≤ a := by
  exact ((mem_integerWindow_iff B a).1 ha).1

theorem integerWindow_upper_bound
    (B : ℕ) (a : ℤ) (ha : a ∈ integerWindow B) :
    a ≤ (B : ℤ) := by
  exact ((mem_integerWindow_iff B a).1 ha).2

theorem natAbs_bound_to_abs_bound
    (B : ℕ) (a : ℤ) (ha : Int.natAbs a ≤ B) :
    |a| ≤ (B : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast ha

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

theorem shifted_index_not_mem_of_nonneg_index_large_positive_shift
    (S : Finset ℤ) (B : ℕ)
    (hS : ∀ b ∈ S, b ∈ integerWindow B)
    (a l : ℤ) (ha : 0 ≤ a) (hl : 0 ≤ l)
    (hlarge : (2 * B : ℤ) < l) :
    a + l ∉ S := by
  intro hb
  have hbW : a + l ∈ integerWindow B := hS (a + l) hb
  rw [mem_integerWindow_iff] at hbW
  omega

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
    have hab : a ≠ a + l := by omega
    exact normalMatrixUnit_apply_eq_zero_of_negative_distinct_outside_support
      a (a + l) S hx ha0 hb0 hab ha

/- theorem normalMatrixUnit_apply_eq_zero_of_positive_shift
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
      exact finite_support_add_not_mem_of_large_positive_mode S (2 * B)
        (by
          intro c hc d hd
          have hc' := hS c hc
          have hd' := hS d hd
          rw [mem_integerWindow_iff] at hc' hd'
          have hcd : |c - d| ≤ (2 * B : ℤ) := by omega
          exact hcd) l (le_of_lt hl)
        (by
          have : (2 * B + 1 : ℕ) ≤ l.natAbs := by
            rw [Int.natAbs_of_nonneg (le_of_lt hl)]
            exact_mod_cast hlarge
          omega) a ha
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

 -/ theorem normalMatrixUnit_apply_eq_zero_of_large_positive_shift_on_support
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

/- theorem fermionicCutoffCurrent_apply_eq_zero_of_positive_shift_window_bound
    (S : Finset ℤ) (B : ℕ)
    (hS : ∀ b ∈ S, b ∈ integerWindow B)
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
-/

/- The two shifted support sets needed by the two summands of a boundary
   diagonal term are still finite. -/
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

theorem fermionicBulkBoundaryDiagonalTerm_apply_eventually_zero
    (m n a : ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
        (fermionicRawCAR (𝕜 := 𝕜)) N m n a) x = 0 := by
  rcases RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm_eventually_zero
      (fermionicRawCAR (𝕜 := 𝕜)) m n a with ⟨N0, hN0⟩
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN
  exact congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x) (hN0 N hN)

theorem fermionicBulkBoundaryDiagonalTerm_eq_zero_of_same_shift_membership
    (N : ℕ) (m n a : ℤ)
    (hmem : (a + m ∈ integerWindow N) ↔ (a + n ∈ integerWindow N))
    (x : FermionicFock (𝕜 := 𝕜)) :
    (RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
      (fermionicRawCAR (𝕜 := 𝕜)) N m n a) x = 0 := by
  exact congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x)
    (RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm_eq_zero_of_same_shift_membership
      (fermionicRawCAR (𝕜 := 𝕜)) N m n a hmem)

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
      simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hm
    by_cases hn : a + n ∈ integerWindow N
    · have hn' : n + a ∈ cutoffWindow N := by
        simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hn
      simp [hm', hn', hend]
    · have hn' : n + a ∉ cutoffWindow N := by
        simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hn
      simp [hm', hn', hend]
  · have hm' : m + a ∉ cutoffWindow N := by
      simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hm
    by_cases hn : a + n ∈ integerWindow N
    · have hn' : n + a ∈ cutoffWindow N := by
        simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hn
      simp [hm', hn', hend]
    · have hn' : n + a ∉ cutoffWindow N := by
        simpa [SplitCliffordFiniteCAR.integerWindow, cutoffWindow, add_comm] using hn
      simp [hm', hn', hend]

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

/- For the moving boundary, both displayed matrix units have endpoint
   `a + m + n`; only their cutoff indicators differ. -/
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
    simp only [LinearMap.sum_apply]
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
      simpa using congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x)
        (hN1 N (Nat.le_trans (Nat.le_max_right _ _) hN))

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

theorem cutoffActualCentralTerm_eq_restrictedCrossing_of_add_eq_zero
    (N : ℕ) (m n : ℤ) (hmn : m + n = 0) :
    RawCARModeCompletion.cutoffActualCentralTerm
        (fermionicRawCAR (𝕜 := 𝕜)) N m n =
      ∑ a ∈ integerWindow N,
        if a + m ∈ integerWindow N then
          (occ a - occ (a + m)) •
            (fermionicRawCAR (𝕜 := 𝕜)).central
        else 0 := by
  have hn : n = -m := by omega
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

theorem fermionicActualCentralTerm_eq_crossing_of_large_cutoff
    (N : ℕ) (m : ℤ) (hN : m.natAbs ≤ N) :
    (RawCARModeCompletion.cutoffActualCentralTerm
      (fermionicRawCAR (𝕜 := 𝕜)) N m (-m) -
      RawCARModeCompletion.cutoffWindowCrossingTerm
        (fermionicRawCAR (𝕜 := 𝕜)) N m (-m)) = 0 := by
  exact InfoGeometry.Canonical.SplitCliffordCurrentCommutator.RawCARModeCompletion.current_central_edge_correction_eq_zero_of_edge_occ_balance
    (fermionicRawCAR (𝕜 := 𝕜)) N m
    (InfoGeometry.Canonical.SplitCliffordCurrentCommutator.RawCARModeCompletion.edge_occ_balance_of_natAbs_le N m hN)

theorem fermionicBoundaryTerm_apply_eventually_zero_of_add_eq_zero
    (m n : ℤ) (hmn : m + n = 0) (x : FermionicFock (𝕜 := 𝕜)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (RawCARModeCompletion.cutoffBoundaryTerm
        (fermionicRawCAR (𝕜 := 𝕜)) N m n) x = 0 := by
  have hn : n = -m := by omega
  rw [hn]
  filter_upwards [fermionicBulkBoundaryTerm_apply_eventually_zero m (-m) x,
    Filter.eventually_ge_atTop m.natAbs] with N hbulk hN
  unfold RawCARModeCompletion.cutoffBoundaryTerm
  rw [fermionicActualCentralTerm_eq_crossing_of_large_cutoff N m hN]
  simp [hbulk]

/- The same boundary vanishing after the canonical identity representation
   into endomorphisms.  This is the exact interface required by
   `StabilizedCurrentSource`; no second representation is introduced. -/
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

/- Fixed-window transport of the native boundary theorem.  This is the
   support-safe intermediate statement: the cutoff index remains external,
   while the summed index is confined to a fixed finite window. -/
theorem fermionicBulkBoundaryDiagonalSum_apply_eventually_zero_on_window
    (m n : ℤ) (K : ℕ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (∑ a ∈ integerWindow K,
        (RawCARModeCompletion.cutoffBulkBoundaryDiagonalTerm
          (fermionicRawCAR (𝕜 := 𝕜)) N m n a)) x = 0 := by
  rcases RawCARModeCompletion.cutoffBulkBoundaryDiagonalSum_eventually_zero_on_window
      (fermionicRawCAR (𝕜 := 𝕜)) m n K with ⟨N0, hN0⟩
  exact ⟨N0, fun N hN => by
    simpa using congrArg (fun T : FermionicEnd (𝕜 := 𝕜) => T x) (hN0 N hN)⟩

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

def fermionicCutoffCurrent (N : ℕ) (m : ℤ) : FermionicEnd (𝕜 := 𝕜) :=
  (fermionicRawCAR (𝕜 := 𝕜)).cutoffCurrent N m

theorem fermionicCutoffCurrent_eq_sum (N : ℕ) (m : ℤ) :
    fermionicCutoffCurrent (𝕜 := 𝕜) N m =
      ∑ a ∈ integerWindow N,
        (fermionicRawCAR (𝕜 := 𝕜)).matrixUnit a (a + m) := by
  rfl

/-! The finite cutoff is an actual exterior-Fock operator sum.  This theorem
does not identify the infinite completion with an endomorphism; it records
the source-level normal ordering before any locally-finite extension. -/
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

/-
  rcases exteriorFock_exists_finite_mode_support x with ⟨S, hx⟩
  let B : ℕ := S.sup Int.natAbs
  refine ⟨2 * B + 1, ?_⟩
  intro N hN
  rw [fermionicCutoffCurrent_eq_normalMatrixUnit_sum]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  have hlarge : (2 * B : ℤ) < l := by
    have h : (2 * B + 1 : ℕ) ≤ l.natAbs := hN
    rw [Int.natAbs_of_nonneg hl] at h
    omega
  by_cases haS : a ∈ S
  · have hbS : a + l ∉ S := by
      exact finite_support_add_not_mem_of_large_natAbs S (2 * B) (by
        intro c hc d hd
        have hc' : Int.natAbs c ≤ B := by
          dsimp [B]; exact Finset.le_sup (f := Int.natAbs) hc
        have hd' : Int.natAbs d ≤ B := by
          dsimp [B]; exact Finset.le_sup (f := Int.natAbs) hd
        have hc'' : |c| ≤ (B : ℤ) := by
          rw [Int.abs_eq_natAbs]; exact_mod_cast hc'
        have hd'' : |d| ≤ (B : ℤ) := by
          rw [Int.abs_eq_natAbs]; exact_mod_cast hd'
        have hcd : |c - d| ≤ |c| + |d| := by
          calc
            |c - d| = |c + (-d)| := by rw [sub_eq_add_neg]
            _ ≤ |c| + |-d| := abs_add_le _ _
            _ = |c| + |d| := by rw [abs_neg]
        omega) l (by omega) a ha (a + l) hbS rfl
    have ha' : -(B : ℤ) ≤ a := by
      have h : Int.natAbs a ≤ B := by
        dsimp [B]; exact Finset.le_sup (f := Int.natAbs) haS
      rw [Int.neg_le, Int.abs_eq_natAbs]
      exact_mod_cast h
    exact normalMatrixUnit_apply_eq_zero_of_not_mem_support_of_nonneg
      a (a + l) S hx (by omega) hbS
  · by_cases ha0 : 0 ≤ a
    · have hbS : a + l ∉ S := by
        intro hbS
        have hbound : Int.natAbs (a + l) ≤ B := by
          dsimp [B]; exact Finset.le_sup (f := Int.natAbs) hbS
        have hnonneg : (0 : ℤ) ≤ a + l := by omega
        rw [Int.ofNat_natAbs_of_nonneg hnonneg] at hbound
        omega
      exact normalMatrixUnit_apply_eq_zero_of_not_mem_support_of_nonneg
        a (a + l) S hx (by omega) hbS
    · have ha0' : a < 0 := lt_of_not_ge ha0
      by_cases hb0 : 0 ≤ a + l
      · exact normalMatrixUnit_apply_eq_zero_of_negative_nonnegative_outside_support
          a (a + l) S hx ha0' hb0 haS
      · have hab : a ≠ a + l := by omega
        exact normalMatrixUnit_apply_eq_zero_of_negative_distinct_outside_support
          a (a + l) S hx ha0' (lt_of_not_ge hb0) hab haS
-/

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

theorem fermionicCutoffCurrent_apply_eventually_eq_stabilized
    (m : ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    ∃ N0 : ℕ, ∀ᶠ N : ℕ in Filter.atTop,
      (fermionicCutoffCurrent (𝕜 := 𝕜) N m) x =
        (fermionicCutoffCurrent (𝕜 := 𝕜) N0 m) x := by
  rcases fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x with
    ⟨N0, hN0⟩
  exact ⟨N0, Filter.eventually_atTop.2 ⟨N0, hN0⟩⟩

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

@[simp] theorem fermionicCurrentMode_apply (m : ℤ) (x : FermionicFock (𝕜 := 𝕜)) :
    fermionicCurrentMode (𝕜 := 𝕜) m x =
      (fermionicCutoffCurrent (𝕜 := 𝕜)
        (Classical.choose
          (fermionicCutoffCurrent_apply_stabilizes_of_finite_support m x)) m) x :=
  rfl

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

/- The finite normal-ordered current has zero vacuum coefficient.  This is
   the finite Fock statement obtained directly from the native exterior
   vacuum functional; it does not assert pointwise convergence of currents. -/
theorem fermionicCutoffCurrent_vacuumExpect_zero (N : ℕ) (m : ℤ) :
    vacuumExpectEnd (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
        (fermionicCutoffCurrent (𝕜 := 𝕜) N m) = 0 := by
  rw [fermionicCutoffCurrent_eq_normalMatrixUnit_sum]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  exact normalMatrixUnit_vacuumExpect_zero_directSum 𝕜 a (a + m)

theorem fermionicCutoffCurrent_vacuumExpect_eventually_eq (m : ℤ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      vacuumExpectEnd (R := 𝕜) (M := CanonicalNormalOrdering.IntModeSpace 𝕜)
        (fermionicCutoffCurrent (𝕜 := 𝕜) N m) = 0 := by
  exact Filter.Eventually.of_forall (fun N =>
    fermionicCutoffCurrent_vacuumExpect_zero N m)

theorem fermionicCurrent_coefficientwise_completion (m : ℤ) :
    ∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j := by
  intro i j
  exact cutoffDiagonalCurrent_coeff_eventually_eq_completed m i j

/-
Coefficientwise stabilization in the filter interface used by the
completion layer.  This is only a statement about the locally finite
matrix readout; it does not introduce a pointwise Fock-space limit.
-/
theorem fermionicCurrent_coefficientwise_eventually_eq (m i j : ℤ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j := by
  rcases fermionicCurrent_coefficientwise_completion m i j with ⟨N0, hN0⟩
  exact Filter.eventually_atTop.2 ⟨N0, hN0⟩

theorem fermionicCurrent_completion_packet (m n : ℤ) :
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
variable (α : 𝕜)

abbrev BosonicFock : Type _ := ChargedFockSpace 𝕜 α
abbrev BosonicEnd : Type _ := BosonicFock (α := α) →ₗ[𝕜] BosonicFock (α := α)

noncomputable def fermionToBosonCurrent
    (X : CompletedCurrentModeCarrier) : BosonicEnd (α := α) :=
  representedCompletedCurrentMode α X

theorem fermionToBosonCurrent_mode (m : ℤ) :
    fermionToBosonCurrent α (completedCurrentPoint m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m := by
  exact representedCompletedCurrentMode_point α m

theorem fermionToBosonCurrent_eq_heisenbergRepresentation
    (X : CompletedCurrentModeCarrier) :
    fermionToBosonCurrent α X =
      chargedFockSpaceHeisenbergMode 𝕜 α
        (completedCurrentModeEquiv.symm X) := by
  exact representedCompletedCurrentMode_eq_heisenbergRepresentation α X

theorem fermionToBosonCurrent_commutator (m n : ℤ) :
    (fermionToBosonCurrent α (completedCurrentPoint m)).commutator
      (fermionToBosonCurrent α (completedCurrentPoint n)) =
      if m + n = 0 then (m : 𝕜) • (1 : BosonicEnd (α := α)) else 0 := by
  exact representedCompletedCurrentMode_commutator α m n

theorem virasoro_acts_on_bosonizedFermionicCurrent (r m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      (fermionToBosonCurrent α (completedCurrentPoint m)) =
      -m • fermionToBosonCurrent α (completedCurrentPoint (r + m)) := by
  exact virasoro_lgen_acts_on_completedCurrent α r m

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

noncomputable def fermionicStabilizedCurrentSource :
    StabilizedCurrentSource 𝕜 (FermionicEnd (𝕜 := 𝕜))
      (FermionicFock (𝕜 := 𝕜)) where
  source := fermionicRawCAR (𝕜 := 𝕜)
  ρ := RingHom.id _
  J := fermionicCurrentMode (𝕜 := 𝕜)
  trunc := fermionicCurrentMode_apply_eventually_zero
  cutoff_eventually_constant := by
    intro m x
    simpa [endomorphismCutoffCurrent] using
      (fermionicCutoffCurrent_eventually_eq_fermionicCurrentMode m x)
  boundary_eventually_zero := by
    intro m n x
    simpa [endomorphismCutoffCurrent] using
      (fermionicEndomorphismBoundaryTerm_apply_eventually_zero m n x)

theorem fermionicCurrentMode_commutator (m n : ℤ) :
    (fermionicCurrentMode (𝕜 := 𝕜) m).commutator
        (fermionicCurrentMode (𝕜 := 𝕜) n) =
      if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 (FermionicFock (𝕜 := 𝕜)))
      else 0 := by
  exact StabilizedCurrentSource.current_commutator
    (fermionicStabilizedCurrentSource (𝕜 := 𝕜)) m n

noncomputable def fermionicCurrentHeisenbergRep :
    CurrentHeisenbergRep 𝕜 (FermionicFock (𝕜 := 𝕜)) where
  J := fermionicCurrentMode (𝕜 := 𝕜)
  trunc := fermionicCurrentMode_apply_eventually_zero
  comm := fermionicCurrentMode_commutator

noncomputable def fermionicCurrentSugawaraRepresentation :
    VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
      Module.End 𝕜 (FermionicFock (𝕜 := 𝕜)) :=
  (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).currentSugawaraRepresentation

theorem fermionicCurrentSugawaraRepresentation_apply_lgen (r : ℤ) :
    fermionicCurrentSugawaraRepresentation (𝕜 := 𝕜)
        (VirasoroAlgebra.lgen 𝕜 r) =
      (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).sugawaraStressMode r := by
  exact (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).currentSugawaraRepresentation_lgen_apply r

theorem fermionicCurrentSugawaraRepresentation_apply_cgen :
    fermionicCurrentSugawaraRepresentation (𝕜 := 𝕜)
        (VirasoroAlgebra.cgen 𝕜) =
      (1 : Module.End 𝕜 (FermionicFock (𝕜 := 𝕜))) := by
  exact (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).currentSugawaraRepresentation_central

theorem fermionicCurrentSugawara_stressMode_commutator (m n : ℤ) :
    ((fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).sugawaraStressMode m).commutator
        ((fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).sugawaraStressMode n) =
      (m - n) • (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).sugawaraStressMode (m + n) +
        (if m + n = 0 then
          ((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
            (1 : Module.End 𝕜 (FermionicFock (𝕜 := 𝕜)))
        else 0) := by
  exact (fermionicCurrentHeisenbergRep (𝕜 := 𝕜)).sugawaraStressMode_virasoroBracket m n

theorem fermionic_to_bosonic_current_intertwiner_packet (r m : ℤ) :
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j) ∧
    fermionToBosonCurrent α (completedCurrentPoint m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m ∧
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 r)).commutator
      (fermionToBosonCurrent α (completedCurrentPoint m)) =
      -m • fermionToBosonCurrent α (completedCurrentPoint (r + m)) := by
  exact ⟨fermionicCurrent_coefficientwise_completion m,
    fermionToBosonCurrent_mode α m,
    virasoro_acts_on_bosonizedFermionicCurrent α r m⟩

end ChargedFock
end InfoGeometry.Canonical.FermionicCurrentChargedFockIntertwiner
