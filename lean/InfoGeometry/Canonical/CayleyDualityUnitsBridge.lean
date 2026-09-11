import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import InfoGeometry.Canonical.CayleyPeirceKleinFourBridge

/-!
# Native units for the Cayley/Hodge Klein packet

This owner packages the Cayley conjugation, Hodge star, and middle exchange-flip
operators as units of the endomorphism monoid.  It proves the corresponding
finite subgroup is a Klein four-group.  It is separate from the parity-unit
owner and makes no identification with a physical, Galois, or braid group.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyDualityUnitsBridge

open InfoGeometry.Canonical.CayleyPeirceKleinFourBridge
open InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge

abbrev Coord :=
  InfoGeometry.Canonical.CayleyPeirceKleinFourBridge.Coord
abbrev CoordEnd :=
  InfoGeometry.Canonical.CayleyPeirceKleinFourBridge.CoordEnd

def involutionUnit (A : CoordEnd) (hA : A * A = 1) : CoordEndˣ where
  val := A
  inv := A
  val_inv := hA
  inv_val := hA

def C_unit : CoordEndˣ := involutionUnit C_op C_sq
def Star_unit : CoordEndˣ := involutionUnit Star_op Star_sq
def Xi_unit : CoordEndˣ := involutionUnit Xi_op Xi_sq

@[simp] theorem C_unit_val : (C_unit : CoordEnd) = C_op := rfl
@[simp] theorem Star_unit_val : (Star_unit : CoordEnd) = Star_op := rfl
@[simp] theorem Xi_unit_val : (Xi_unit : CoordEnd) = Xi_op := rfl

theorem C_unit_mul_Star_unit : C_unit * Star_unit = Xi_unit := by
  apply Units.ext
  change C_op * Star_op = Xi_op
  exact C_mul_Star

theorem Star_unit_mul_C_unit : Star_unit * C_unit = Xi_unit := by
  apply Units.ext
  change Star_op * C_op = Xi_op
  exact Star_mul_C

theorem Star_unit_mul_Xi_unit : Star_unit * Xi_unit = C_unit := by
  apply Units.ext
  change Star_op * Xi_op = C_op
  exact Star_mul_Xi

theorem Xi_unit_mul_Star_unit : Xi_unit * Star_unit = C_unit := by
  apply Units.ext
  change Xi_op * Star_op = C_op
  exact Xi_mul_Star

theorem Xi_unit_mul_C_unit : Xi_unit * C_unit = Star_unit := by
  apply Units.ext
  change Xi_op * C_op = Star_op
  exact Xi_mul_C

theorem C_unit_mul_Xi_unit : C_unit * Xi_unit = Star_unit := by
  apply Units.ext
  change C_op * Xi_op = Star_op
  exact C_mul_Xi

@[simp] theorem C_unit_sq : C_unit * C_unit = 1 := by
  apply Units.ext
  change C_op * C_op = 1
  exact C_sq

@[simp] theorem Star_unit_sq : Star_unit * Star_unit = 1 := by
  apply Units.ext
  change Star_op * Star_op = 1
  exact Star_sq

@[simp] theorem Xi_unit_sq : Xi_unit * Xi_unit = 1 := by
  apply Units.ext
  change Xi_op * Xi_op = 1
  exact Xi_sq

@[simp] theorem C_unit_inv : C_unit⁻¹ = C_unit := by
  apply Units.ext
  rfl

@[simp] theorem Star_unit_inv : Star_unit⁻¹ = Star_unit := by
  apply Units.ext
  rfl

@[simp] theorem Xi_unit_inv : Xi_unit⁻¹ = Xi_unit := by
  apply Units.ext
  rfl

theorem C_op_ne_one : C_op ≠ 1 := by
  intro h
  let x : Coord := (1, 0, 0, 0)
  have hx := congrArg (fun A : CoordEnd => A x) h
  norm_num [C_op, cayleyConj, x] at hx

theorem Star_op_ne_one : Star_op ≠ 1 := by
  intro h
  let x : Coord := (1, 0, 0, 0)
  have hx := congrArg (fun A : CoordEnd => A x) h
  norm_num [Star_op, hodgeStar, x] at hx

theorem Xi_op_ne_one : Xi_op ≠ 1 := by
  intro h
  let x : Coord := (0, (fun _ : Fin 3 => 1), 0, 0)
  have hx := congrArg (fun A : CoordEnd => A x) h
  have hv := congrArg (fun z : Coord => z.2.1 0) hx
  norm_num [Xi_op, middleExchangeFlip, x] at hv

theorem C_op_ne_Star_op : C_op ≠ Star_op := by
  intro h
  let x : Coord := (0, (fun _ : Fin 3 => 1), 0, 0)
  have hx := congrArg (fun A : CoordEnd => A x) h
  have hv := congrArg (fun z : Coord => z.2.1 0) hx
  norm_num [C_op, Star_op, cayleyConj, hodgeStar, x] at hv

theorem C_op_ne_Xi_op : C_op ≠ Xi_op := by
  intro h
  let x : Coord := (1, 0, 0, 0)
  have hx := congrArg (fun A : CoordEnd => A x) h
  have hs := congrArg (fun z : Coord => z.1) hx
  norm_num [C_op, Xi_op, cayleyConj, middleExchangeFlip, x] at hs

theorem Star_op_ne_Xi_op : Star_op ≠ Xi_op := by
  intro h
  let x : Coord := (1, 0, 0, 0)
  have hx := congrArg (fun A : CoordEnd => A x) h
  have hs := congrArg (fun z : Coord => z.1) hx
  norm_num [Star_op, Xi_op, hodgeStar, middleExchangeFlip, x] at hs

def dualityUnitPacket : Set CoordEndˣ := {1, C_unit, Star_unit, Xi_unit}

theorem one_ne_C_unit : (1 : CoordEndˣ) ≠ C_unit := by
  intro h
  apply C_op_ne_one
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h.symm

theorem one_ne_Star_unit : (1 : CoordEndˣ) ≠ Star_unit := by
  intro h
  apply Star_op_ne_one
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h.symm

theorem one_ne_Xi_unit : (1 : CoordEndˣ) ≠ Xi_unit := by
  intro h
  apply Xi_op_ne_one
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h.symm

theorem C_unit_ne_Star_unit : C_unit ≠ Star_unit := by
  intro h
  apply C_op_ne_Star_op
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h

theorem C_unit_ne_Xi_unit : C_unit ≠ Xi_unit := by
  intro h
  apply C_op_ne_Xi_op
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h

theorem Star_unit_ne_Xi_unit : Star_unit ≠ Xi_unit := by
  intro h
  apply Star_op_ne_Xi_op
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h

theorem dualityUnitPacket_ncard : dualityUnitPacket.ncard = 4 := by
  change ({1, C_unit, Star_unit, Xi_unit} : Set CoordEndˣ).ncard = 4
  rw [Set.ncard_insert_of_notMem]
  · rw [Set.ncard_insert_of_notMem]
    · rw [Set.ncard_insert_of_notMem]
      · simp
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact Star_unit_ne_Xi_unit
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨C_unit_ne_Star_unit, C_unit_ne_Xi_unit⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨one_ne_C_unit, one_ne_Star_unit, one_ne_Xi_unit⟩

private theorem dualityUnitPacket_mul_mem
    {X Y : CoordEndˣ} (hX : X ∈ dualityUnitPacket)
    (hY : Y ∈ dualityUnitPacket) : X * Y ∈ dualityUnitPacket := by
  simp only [dualityUnitPacket, Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY ⊢
  rcases hX with rfl | rfl | rfl | rfl <;>
    rcases hY with rfl | rfl | rfl | rfl <;>
      simp [C_unit_sq, Star_unit_sq, Xi_unit_sq,
        C_unit_mul_Star_unit, Star_unit_mul_C_unit,
        Star_unit_mul_Xi_unit, Xi_unit_mul_Star_unit,
        Xi_unit_mul_C_unit, C_unit_mul_Xi_unit]

def dualityPacketSubgroup : Subgroup CoordEndˣ where
  carrier := dualityUnitPacket
  one_mem' := by simp [dualityUnitPacket]
  mul_mem' := dualityUnitPacket_mul_mem
  inv_mem' := by
    intro u hu
    simp only [dualityUnitPacket, Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl | rfl | rfl
    · simp
    · rw [C_unit_inv]; simp
    · rw [Star_unit_inv]; simp
    · rw [Xi_unit_inv]; simp

def cayleyDualityKleinSubgroup : Subgroup CoordEndˣ :=
  Subgroup.closure {C_unit, Star_unit}

theorem C_unit_mem_cayleyDualityKleinSubgroup :
    C_unit ∈ cayleyDualityKleinSubgroup :=
  Subgroup.subset_closure (by simp)

theorem Star_unit_mem_cayleyDualityKleinSubgroup :
    Star_unit ∈ cayleyDualityKleinSubgroup :=
  Subgroup.subset_closure (by simp)

theorem Xi_unit_mem_cayleyDualityKleinSubgroup :
    Xi_unit ∈ cayleyDualityKleinSubgroup := by
  rw [← C_unit_mul_Star_unit]
  exact cayleyDualityKleinSubgroup.mul_mem
    C_unit_mem_cayleyDualityKleinSubgroup Star_unit_mem_cayleyDualityKleinSubgroup

theorem cayleyDualityKleinSubgroup_eq_dualityPacketSubgroup :
    cayleyDualityKleinSubgroup = dualityPacketSubgroup := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · simp [dualityPacketSubgroup, dualityUnitPacket]
    · simp [dualityPacketSubgroup, dualityUnitPacket]
  · intro u hu
    change (u : CoordEndˣ) ∈ dualityUnitPacket at hu
    simp only [dualityUnitPacket, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact cayleyDualityKleinSubgroup.one_mem
    · exact C_unit_mem_cayleyDualityKleinSubgroup
    · exact Star_unit_mem_cayleyDualityKleinSubgroup
    · exact Xi_unit_mem_cayleyDualityKleinSubgroup

theorem cayleyDualityKleinSubgroup_sq (u : cayleyDualityKleinSubgroup) : u * u = 1 := by
  have hu : (u : CoordEndˣ) ∈ dualityUnitPacket := by
    have hu' : (u : CoordEndˣ) ∈ dualityPacketSubgroup := by
      rw [← cayleyDualityKleinSubgroup_eq_dualityPacketSubgroup]
      exact u.property
    exact hu'
  simp only [dualityUnitPacket, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with hu | hu | hu | hu
  · have h : u = (1 : cayleyDualityKleinSubgroup) := Subtype.ext hu
    rw [h]
    simp
  · have h : u = ⟨C_unit, C_unit_mem_cayleyDualityKleinSubgroup⟩ := Subtype.ext hu
    rw [h]
    simp
  · have h : u = ⟨Star_unit, Star_unit_mem_cayleyDualityKleinSubgroup⟩ :=
      Subtype.ext hu
    rw [h]
    simp
  · have h : u = ⟨Xi_unit, Xi_unit_mem_cayleyDualityKleinSubgroup⟩ :=
      Subtype.ext hu
    rw [h]
    simp

theorem cayleyDualityKleinSubgroup_isKleinFour :
    IsKleinFour cayleyDualityKleinSubgroup := by
  letI : Nontrivial cayleyDualityKleinSubgroup := by
    refine ⟨⟨⟨C_unit, C_unit_mem_cayleyDualityKleinSubgroup⟩, 1, ?_⟩⟩
    intro h
    apply one_ne_C_unit
    exact congrArg (fun u : cayleyDualityKleinSubgroup => (u : CoordEndˣ)) h.symm
  constructor
  · rw [cayleyDualityKleinSubgroup_eq_dualityPacketSubgroup]
    change dualityUnitPacket.ncard = 4
    exact dualityUnitPacket_ncard
  · apply (Monoid.exponent_eq_prime_iff (by norm_num : Nat.Prime 2)).2
    intro u hu
    apply orderOf_eq_prime
    · simpa [pow_two] using cayleyDualityKleinSubgroup_sq u
    · exact hu

noncomputable def cayleyDualityKleinSubgroup_mulEquiv :
    Multiplicative (ZMod 2 × ZMod 2) ≃* cayleyDualityKleinSubgroup := by
  letI : IsKleinFour cayleyDualityKleinSubgroup :=
    cayleyDualityKleinSubgroup_isKleinFour
  exact (IsKleinFour.nonempty_mulEquiv
    (G₁ := Multiplicative (ZMod 2 × ZMod 2))
    (G₂ := cayleyDualityKleinSubgroup)).some

end InfoGeometry.Canonical.CayleyDualityUnitsBridge
