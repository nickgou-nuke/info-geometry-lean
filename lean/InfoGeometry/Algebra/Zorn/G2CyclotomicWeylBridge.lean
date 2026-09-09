import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.GradeActionInterface

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

/-!
# Cyclotomic model of the abstract `G₂` Weyl symmetry

This file models the two six-element root orbits by `Bool × ZMod 6`.  The
Boolean coordinate records short versus long roots, while the cyclic
coordinate records the sixfold rotation.  It is an abstract Weyl/root
carrier only: no identification with `SplitOctF2Aut` is asserted here.
-/

namespace InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl

abbrev Root := Bool × ZMod 6

/-- The sector projection forgets the cyclic root index. -/
def sector : Root → Bool := Prod.fst

/-- Canonical cross-section of the two sector orbits. -/
def sectorSection : Bool → Root := fun b => (b, 0)

@[simp] theorem sector_section (b : Bool) :
    sector (sectorSection b) = b := rfl

theorem sectorSection_injective : Function.Injective sectorSection := by
  intro b1 b2 h
  cases b1 <;> cases b2 <;> first | rfl | cases h

theorem sector_surjective : Function.Surjective sector := by
  intro b
  exact ⟨sectorSection b, sector_section b⟩

theorem root_eq_sectorSection_smul (r : Root) :
    ∃ k : ZMod 6, r = (r.1, k) := by
  exact ⟨r.2, rfl⟩

open DihedralGroup

def rotation (n : ZMod 6) (r : Root) : Root :=
  (r.1, r.2 + n)

def reflection (r : Root) : Root :=
    (r.1, -r.2)

/-! The section is not merely existential: the cyclic coordinate is its
unique transport parameter. -/
theorem sector_section_coordinate (r : Root) :
    rotation r.2 (sectorSection (sector r)) = r := by
  rcases r with ⟨b, k⟩
  simp [rotation, sectorSection, sector]

theorem sector_section_coordinate_unique (r : Root) (k : ZMod 6)
    (h : rotation k (sectorSection (sector r)) = r) :
    k = r.2 := by
  rcases r with ⟨b, r₂⟩
  change (b, 0 + k) = (b, r₂) at h
  simpa using congrArg Prod.snd h

theorem sector_crossSection_unique (r : Root) :
    ∃! k : ZMod 6,
      rotation k (sectorSection (sector r)) = r := by
  refine ⟨r.2, sector_section_coordinate r, ?_⟩
  intro k hk
  exact sector_section_coordinate_unique r k hk

/-! The CAS six-cycle has no nontrivial stabilizer on a root sector. -/
theorem rotation_section_free (b : Bool) (k : ZMod 6)
    (h : rotation k (sectorSection b) = sectorSection b) :
    k = 0 := by
  apply sector_section_coordinate_unique (sectorSection b) k
  simpa using h

/-! The section meets each cyclic sector orbit in exactly its canonical point. -/
theorem sectorSection_intersects_orbit_unique (b : Bool) (r : Root)
    (hr : r.1 = b) :
    ∃! k : ZMod 6, rotation k (sectorSection b) = r := by
  subst b
  exact sector_crossSection_unique r

def dihedralAction : DihedralGroup 6 → Root → Root
  | r n, (b, k) => (b, k - n)
  | sr n, (b, k) => (b, n - k)

instance : MulAction (DihedralGroup 6) Root where
  smul := dihedralAction
  one_smul := by
    intro x
    rcases x with ⟨b, k⟩
    change (b, k - (0 : ZMod 6)) = (b, k)
    simp
  mul_smul := by
    intro g h x
    cases g with
    | r g =>
      cases h with
      | r h =>
        rcases x with ⟨b, k⟩
        change (b, k - (g + h)) = (b, (k - h) - g)
        congr 1
        abel

      | sr h =>
        rcases x with ⟨b, k⟩
        change (b, (h - g) - k) = (b, (h - k) - g)
        congr 1
        abel

    | sr g =>
      cases h with
      | r h =>
        rcases x with ⟨b, k⟩
        change (b, (g + h) - k) = (b, g - (k - h))
        congr 1
        abel

      | sr h =>
        rcases x with ⟨b, k⟩
        change (b, k - (h - g)) = (b, g - (h - k))
        congr 1
        abel

theorem dihedral_action_preserves_sector
    (g : DihedralGroup 6) (r : Root) :
    (g • r).1 = r.1 := by
  cases g <;> rcases r with ⟨b, k⟩ <;> rfl

theorem dihedral_mapsTo_sector_family :
    InfoGeometry.OperatorAlgebra.MapsToGrade
      (fun b : Bool => {r : Root | sector r = b})
      (fun g : DihedralGroup 6 => fun r => g • r)
      (fun _ b => b) := by
  intro g b r hr
  change (g • r).1 = b
  change sector r = b at hr
  rw [dihedral_action_preserves_sector g r]
  exact hr

theorem dihedral_sector_image_eq (g : DihedralGroup 6) (b : Bool) :
    (fun r : Root => g • r) '' {r : Root | sector r = b} =
      {r : Root | sector r = b} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨r, hr, rfl⟩
    change (g • r).1 = b
    rw [dihedral_action_preserves_sector g r]
    exact hr
  · intro r hr
    refine ⟨g⁻¹ • r, ?_, ?_⟩
    · change (g⁻¹ • r).1 = b
      rw [dihedral_action_preserves_sector g⁻¹ r]
      exact hr
    · simp

theorem dihedral_composition_mapsTo_sector_family :
    InfoGeometry.OperatorAlgebra.MapsToGrade
      (fun b : Bool => {r : Root | sector r = b})
      (fun gh : DihedralGroup 6 × DihedralGroup 6 =>
        fun r => gh.1 • (gh.2 • r))
      (fun _ b => b) := by
  exact InfoGeometry.OperatorAlgebra.mapsToGrade_comp_family
    dihedral_mapsTo_sector_family dihedral_mapsTo_sector_family

theorem sectorSection_represents_orbit (r : Root) :
    ∃ g : DihedralGroup 6, g • sectorSection (sector r) = r := by
  rcases r with ⟨b, k⟩
  refine ⟨DihedralGroup.r (-k), ?_⟩
  change (b, (0 : ZMod 6) - (-k)) = (b, k)
  congr 1
  abel

theorem sectorSection_unique_sector (r : Root) (b : Bool)
    (h : sector r = b) : sector r = sector (sectorSection b) := by
  simpa [h]

theorem dihedral_orbit_sector_closed (r : Root) (g : DihedralGroup 6) :
    (g • r).1 = r.1 :=
  dihedral_action_preserves_sector g r

theorem dihedral_reaches_same_sector
    (b : Bool) (r : Root) (hr : r.1 = b) :
    ∃ g : DihedralGroup 6, g • (b, 0) = r := by
  rcases r with ⟨b', k⟩
  change b' = b at hr
  subst b'
  refine ⟨DihedralGroup.r (-k), ?_⟩
  change (b, (0 : ZMod 6) - (-k)) = (b, k)
  congr 1
  abel

theorem dihedral_orbit_eq_sector (b : Bool) :
    MulAction.orbit (DihedralGroup 6) (b, (0 : ZMod 6)) =
      {r : Root | r.1 = b} := by
  ext r
  constructor
  · intro hr
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hr
    rw [← hg]
    exact dihedral_action_preserves_sector g (b, (0 : ZMod 6))
  · intro hr
    apply MulAction.mem_orbit_iff.mpr
    exact dihedral_reaches_same_sector b r hr

/-! The orbit relation has exactly the two expected sector classes. -/
theorem dihedral_same_orbit_iff (r s : Root) :
    (∃ g : DihedralGroup 6, g • r = s) ↔ r.1 = s.1 := by
  constructor
  · rintro ⟨g, h⟩
    rw [← h]
    exact (dihedral_action_preserves_sector g r).symm
  · intro hsector
    rcases r with ⟨br, kr⟩
    rcases s with ⟨bs, ks⟩
    change br = bs at hsector
    subst bs
    refine ⟨DihedralGroup.r (kr - ks), ?_⟩
    change (br, kr - (kr - ks)) = (br, ks)
    congr 1
    abel

theorem root_card : Fintype.card Root = 12 := by
  rw [Fintype.card_prod]
  simp

theorem sector_card (b : Bool) :
    Fintype.card {r : Root // r.1 = b} = 6 := by
  let e : {r : Root // r.1 = b} ≃ ZMod 6 :=
    { toFun := fun r => r.1.2
      invFun := fun k => ⟨(b, k), rfl⟩
      left_inv := by
        intro r
        apply Subtype.ext
        rcases r with ⟨⟨b', k⟩, hb⟩
        simp only at hb
        subst b'
        rfl
      right_inv := by
        intro k
        rfl }
  rw [Fintype.card_congr e]
  simp

theorem dihedral_orbit_card (b : Bool) :
    Nat.card (MulAction.orbit (DihedralGroup 6) (b, (0 : ZMod 6))) = 6 := by
  calc
    Nat.card (MulAction.orbit (DihedralGroup 6) (b, (0 : ZMod 6))) =
        Nat.card {r : Root // r.1 = b} :=
      Nat.card_congr (Equiv.setCongr (dihedral_orbit_eq_sector b))
    _ = Fintype.card {r : Root // r.1 = b} := Nat.card_eq_fintype_card
    _ = 6 := sector_card b

noncomputable instance orbitFintype (b : Bool) :
    Fintype (MulAction.orbit (DihedralGroup 6) (b, (0 : ZMod 6))) :=
  Fintype.ofFinite _

theorem dihedral_stabilizer_card (b : Bool) :
    Fintype.card
        (MulAction.stabilizer (DihedralGroup 6) (b, (0 : ZMod 6))) = 2 := by
  have horbit :
      Fintype.card
          (MulAction.orbit (DihedralGroup 6) (b, (0 : ZMod 6))) = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact dihedral_orbit_card b
  have hgroup : Fintype.card (DihedralGroup 6) = 12 := by
    rw [DihedralGroup.card]
  have h :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (DihedralGroup 6) (b, (0 : ZMod 6))
  rw [horbit, hgroup] at h
  omega

theorem dihedral_root_orbit_stabilizer_factorization (b : Bool) :
    Fintype.card
          (MulAction.orbit (DihedralGroup 6) (b, (0 : ZMod 6))) *
        Fintype.card
          (MulAction.stabilizer (DihedralGroup 6) (b, (0 : ZMod 6))) =
      Fintype.card (DihedralGroup 6) := by
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (DihedralGroup 6) (b, (0 : ZMod 6))

noncomputable instance dihedralRootFaithfulSMul :
    FaithfulSMul (DihedralGroup 6) Root where
  eq_of_smul_eq_smul := by
    intro g h hh
    cases g with
    | r g =>
      cases h with
      | r h =>
        have hz := congrArg (fun z : Root => z.2) (hh (false, 0))
        change (0 : ZMod 6) - g = 0 - h at hz
        simpa using congrArg Neg.neg hz
      | sr h =>
        have hz := congrArg (fun z : Root => z.2) (hh (false, 0))
        have ho := congrArg (fun z : Root => z.2) (hh (false, 1))
        change (0 : ZMod 6) - g = h - 0 at hz
        change (1 : ZMod 6) - g = h - 1 at ho
        have hbad : (1 : ZMod 6) = -1 := by
          linear_combination ho - hz
        exact False.elim ((by decide : ¬ ((1 : ZMod 6) = -1)) hbad)
    | sr g =>
      cases h with
      | r h =>
        have hz := congrArg (fun z : Root => z.2) (hh (false, 0))
        have ho := congrArg (fun z : Root => z.2) (hh (false, 1))
        change g - 0 = 0 - h at hz
        change g - 1 = 1 - h at ho
        have hbad : (1 : ZMod 6) = -1 := by
          linear_combination hz - ho
        exact False.elim ((by decide : ¬ ((1 : ZMod 6) = -1)) hbad)
      | sr h =>
        have hz := congrArg (fun z : Root => z.2) (hh (false, 0))
        change g - 0 = h - 0 at hz
        simpa using hz

def dihedralRootPermutationRep : DihedralGroup 6 →* Equiv.Perm Root :=
  MulAction.toPermHom (DihedralGroup 6) Root

@[simp] theorem dihedralRootPermutationRep_apply
    (g : DihedralGroup 6) (r : Root) :
    dihedralRootPermutationRep g r = g • r :=
  rfl

theorem dihedralRootPermutationRep_injective :
    Function.Injective dihedralRootPermutationRep := by
  exact @MulAction.toPerm_injective (DihedralGroup 6) Root _ _ dihedralRootFaithfulSMul

noncomputable def dihedralRootPermutationImageEquiv :
    DihedralGroup 6 ≃ Set.range dihedralRootPermutationRep :=
  Equiv.ofBijective
    (fun g => ⟨dihedralRootPermutationRep g, ⟨g, rfl⟩⟩)
    ⟨(fun _ _ hgh => dihedralRootPermutationRep_injective
        (congrArg Subtype.val hgh)),
      (fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩)⟩

theorem dihedralRootPermutationImage_card :
    Fintype.card (Set.range dihedralRootPermutationRep) = 12 := by
  rw [← Fintype.card_congr dihedralRootPermutationImageEquiv]
  rw [DihedralGroup.card]

theorem dihedral_stabilizer_mem_iff (b : Bool) (g : DihedralGroup 6) :
    g ∈ MulAction.stabilizer (DihedralGroup 6) (b, (0 : ZMod 6)) ↔
      g = DihedralGroup.r 0 ∨ g = DihedralGroup.sr 0 := by
  cases g with
  | r k =>
    constructor
    · intro hg
      rw [MulAction.mem_stabilizer_iff] at hg
      change (b, (0 : ZMod 6) - k) = (b, 0) at hg
      have hk : k = 0 := by
        have := congrArg Prod.snd hg
        simpa using this
      left
      simp [hk]
    · intro hg
      rcases hg with hg | hg
      · simp [hg, dihedralAction]
      · cases hg
  | sr k =>
    constructor
    · intro hg
      rw [MulAction.mem_stabilizer_iff] at hg
      change (b, k - (0 : ZMod 6)) = (b, 0) at hg
      have hk : k = 0 := by
        have := congrArg Prod.snd hg
        simpa using this
      right
      simp [hk]
    · intro hg
      rcases hg with hg | hg
      · cases hg
      · cases hg
        change (b, (0 : ZMod 6) - 0) = (b, 0)
        simp

theorem rotation_add (m n : ZMod 6) (r : Root) :
    rotation m (rotation n r) = rotation (m + n) r := by
  rcases r with ⟨b, k⟩
  simp [rotation]
  abel

theorem rotation_zero (r : Root) : rotation 0 r = r := by
  rcases r with ⟨b, k⟩
  simp [rotation]

theorem rotation_six (r : Root) : rotation 6 r = r := by
  rcases r with ⟨b, k⟩
  change (b, k + (6 : ZMod 6)) = (b, k)
  have h6 : (6 : ZMod 6) = 0 := ZMod.natCast_self 6
  rw [h6, add_zero]

theorem rotation_neg (n : ZMod 6) (r : Root) :
    rotation (-n) (rotation n r) = r := by
  rcases r with ⟨b, k⟩
  simp [rotation, add_assoc]

theorem rotation_injective (n : ZMod 6) :
    Function.Injective (rotation n) := by
  intro r s hrs
  have h := congrArg (rotation (-n)) hrs
  simpa [rotation, add_assoc] using h

theorem reflection_involutive : Function.Involutive reflection := by
  intro r
  rcases r with ⟨b, k⟩
  simp [reflection]

theorem reflection_rotation_reflection (n : ZMod 6) (r : Root) :
    reflection (rotation n (reflection r)) = rotation (-n) r := by
  rcases r with ⟨b, k⟩
  simp [reflection, rotation]
  abel

theorem rotation_preserves_sector (n : ZMod 6) (r : Root) :
    (rotation n r).1 = r.1 := by
  rfl

theorem reflection_preserves_sector (r : Root) :
    (reflection r).1 = r.1 := by
  rfl

/-! ## The concrete-carrier contract

The following structure is deliberately a contract, not a claimed
construction.  A concrete Lie-theoretic root carrier must provide an
equivalence together with the operations it is required to intertwine.
-/

structure ConcreteRootTransport (Concrete : Type*) where
  toConcrete : Root ≃ Concrete
  sector : Concrete → Bool
  concreteRotation : ZMod 6 → Concrete → Concrete
  concreteReflection : Concrete → Concrete
  sector_preserving : ∀ r, sector (toConcrete r) = r.1
  rotation_intertwining :
    ∀ n r, concreteRotation n (toConcrete r) = toConcrete (rotation n r)
  reflection_intertwining :
    ∀ r, concreteReflection (toConcrete r) = toConcrete (reflection r)

theorem concrete_card_of_transport
    {Concrete : Type*} [Fintype Concrete]
    (T : ConcreteRootTransport Concrete) :
    Fintype.card Concrete = 12 := by
  rw [← Fintype.card_congr T.toConcrete]
  exact root_card

theorem concrete_reflection_involutive
    {Concrete : Type*} [Fintype Concrete]
    (T : ConcreteRootTransport Concrete) :
    Function.Involutive T.concreteReflection := by
  intro c
  obtain ⟨r, rfl⟩ := T.toConcrete.surjective c
  calc
    T.concreteReflection (T.concreteReflection (T.toConcrete r)) =
        T.concreteReflection (T.toConcrete (reflection r)) := by
      rw [T.reflection_intertwining r]
    _ = T.toConcrete (reflection (reflection r)) :=
      T.reflection_intertwining (reflection r)
    _ = T.toConcrete r := by
      rw [reflection_involutive]

theorem concrete_rotation_preserves_sector
    {Concrete : Type*} [Fintype Concrete]
    (T : ConcreteRootTransport Concrete)
    (n : ZMod 6) (c : Concrete) :
    T.sector (T.concreteRotation n c) = T.sector c := by
  obtain ⟨r, rfl⟩ := T.toConcrete.surjective c
  rw [T.rotation_intertwining, T.sector_preserving,
    T.sector_preserving, rotation_preserves_sector]

theorem concrete_reflection_preserves_sector
    {Concrete : Type*} [Fintype Concrete]
    (T : ConcreteRootTransport Concrete)
    (c : Concrete) :
    T.sector (T.concreteReflection c) = T.sector c := by
  obtain ⟨r, rfl⟩ := T.toConcrete.surjective c
  rw [T.reflection_intertwining, T.sector_preserving,
    T.sector_preserving, reflection_preserves_sector]

theorem concrete_rotation_sector_fiber_closed
    {Concrete : Type*} [Fintype Concrete]
    (T : ConcreteRootTransport Concrete)
    (n : ZMod 6) (c : Concrete) (b : Bool)
    (hc : T.sector c = b) :
    T.sector (T.concreteRotation n c) = b := by
  rw [concrete_rotation_preserves_sector T n c, hc]

theorem concrete_reflection_sector_fiber_closed
    {Concrete : Type*} [Fintype Concrete]
    (T : ConcreteRootTransport Concrete)
    (c : Concrete) (b : Bool)
    (hc : T.sector c = b) :
    T.sector (T.concreteReflection c) = b := by
  rw [concrete_reflection_preserves_sector T c, hc]

end InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
