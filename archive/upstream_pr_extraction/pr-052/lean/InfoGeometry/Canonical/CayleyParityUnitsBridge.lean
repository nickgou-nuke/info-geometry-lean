import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import InfoGeometry.Canonical.CayleyPeirceKleinFourBridge

/-!
# Native units for the parity Klein packet

The endomorphism carrier is a monoid, not a group.  This owner therefore
packages the involutions `P`, `GammaF`, and `M_mid` as genuine units of the
endomorphism monoid.  It does not yet assert a group isomorphism or a physical
interpretation.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyParityUnitsBridge

open InfoGeometry.Canonical.CayleyPeirceKleinFourBridge

abbrev CoordEnd := Module.End ℝ Coord

def involutionUnit (A : CoordEnd) (hA : A * A = 1) : CoordEndˣ where
  val := A
  inv := A
  val_inv := hA
  inv_val := hA

def P_unit : CoordEndˣ := involutionUnit P P_sq
def GammaF_unit : CoordEndˣ := involutionUnit GammaF GammaF_sq
def M_mid_unit : CoordEndˣ := involutionUnit M_mid M_mid_sq

@[simp] theorem P_unit_val : (P_unit : CoordEnd) = P := rfl
@[simp] theorem GammaF_unit_val : (GammaF_unit : CoordEnd) = GammaF := rfl
@[simp] theorem M_mid_unit_val : (M_mid_unit : CoordEnd) = M_mid := rfl

theorem P_unit_mul_GammaF_unit : P_unit * GammaF_unit = M_mid_unit := by
  apply Units.ext
  change P * GammaF = M_mid
  exact P_mul_GammaF

theorem GammaF_unit_mul_P_unit : GammaF_unit * P_unit = M_mid_unit := by
  apply Units.ext
  change GammaF * P = M_mid
  exact GammaF_mul_P

theorem GammaF_unit_mul_M_mid_unit : GammaF_unit * M_mid_unit = P_unit := by
  apply Units.ext
  change GammaF * M_mid = P
  exact GammaF_mul_M

theorem M_mid_unit_mul_GammaF_unit : M_mid_unit * GammaF_unit = P_unit := by
  apply Units.ext
  change M_mid * GammaF = P
  exact M_mul_GammaF

theorem M_mid_unit_mul_P_unit : M_mid_unit * P_unit = GammaF_unit := by
  apply Units.ext
  change M_mid * P = GammaF
  exact M_mul_P

theorem P_unit_mul_M_mid_unit : P_unit * M_mid_unit = GammaF_unit := by
  apply Units.ext
  change P * M_mid = GammaF
  exact P_mul_M

@[simp] theorem P_unit_sq : P_unit * P_unit = 1 := by
  apply Units.ext
  change P * P = 1
  exact P_sq

@[simp] theorem GammaF_unit_sq : GammaF_unit * GammaF_unit = 1 := by
  apply Units.ext
  change GammaF * GammaF = 1
  exact GammaF_sq

@[simp] theorem M_mid_unit_sq : M_mid_unit * M_mid_unit = 1 := by
  apply Units.ext
  change M_mid * M_mid = 1
  exact M_mid_sq

@[simp] theorem P_unit_inv : P_unit⁻¹ = P_unit := by
  apply Units.ext
  rfl

@[simp] theorem GammaF_unit_inv : GammaF_unit⁻¹ = GammaF_unit := by
  apply Units.ext
  rfl

@[simp] theorem M_mid_unit_inv : M_mid_unit⁻¹ = M_mid_unit := by
  apply Units.ext
  rfl

def parityUnitPacket : Set CoordEndˣ := {1, P_unit, GammaF_unit, M_mid_unit}

theorem one_ne_P_unit : (1 : CoordEndˣ) ≠ P_unit := by
  intro h
  apply P_ne_one
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h.symm

theorem one_ne_GammaF_unit : (1 : CoordEndˣ) ≠ GammaF_unit := by
  intro h
  apply GammaF_ne_one
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h.symm

theorem one_ne_M_mid_unit : (1 : CoordEndˣ) ≠ M_mid_unit := by
  intro h
  apply M_mid_ne_one
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h.symm

theorem P_unit_ne_GammaF_unit : P_unit ≠ GammaF_unit := by
  intro h
  apply P_ne_GammaF
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h

theorem P_unit_ne_M_mid_unit : P_unit ≠ M_mid_unit := by
  intro h
  apply P_ne_M_mid
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h

theorem GammaF_unit_ne_M_mid_unit : GammaF_unit ≠ M_mid_unit := by
  intro h
  apply GammaF_ne_M_mid
  exact congrArg (fun u : CoordEndˣ => (u : CoordEnd)) h

theorem parityUnitPacket_ncard : parityUnitPacket.ncard = 4 := by
  change ({1, P_unit, GammaF_unit, M_mid_unit} : Set CoordEndˣ).ncard = 4
  rw [Set.ncard_insert_of_notMem]
  · rw [Set.ncard_insert_of_notMem]
    · rw [Set.ncard_insert_of_notMem]
      · simp
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact GammaF_unit_ne_M_mid_unit
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨P_unit_ne_GammaF_unit, P_unit_ne_M_mid_unit⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨one_ne_P_unit, one_ne_GammaF_unit, one_ne_M_mid_unit⟩

private theorem parityUnitPacket_mul_mem
    {X Y : CoordEndˣ} (hX : X ∈ parityUnitPacket)
    (hY : Y ∈ parityUnitPacket) : X * Y ∈ parityUnitPacket := by
  simp only [parityUnitPacket, Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY ⊢
  rcases hX with rfl | rfl | rfl | rfl <;>
    rcases hY with rfl | rfl | rfl | rfl <;>
      simp [P_unit_sq, GammaF_unit_sq, M_mid_unit_sq,
        P_unit_mul_GammaF_unit,
        GammaF_unit_mul_P_unit, GammaF_unit_mul_M_mid_unit,
        M_mid_unit_mul_GammaF_unit, M_mid_unit_mul_P_unit,
        P_unit_mul_M_mid_unit]

def parityPacketSubgroup : Subgroup CoordEndˣ where
  carrier := parityUnitPacket
  one_mem' := by simp [parityUnitPacket]
  mul_mem' := parityUnitPacket_mul_mem
  inv_mem' := by
    intro u hu
    simp only [parityUnitPacket, Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl | rfl | rfl
    · simp
    · rw [P_unit_inv]
      simp
    · rw [GammaF_unit_inv]
      simp
    · rw [M_mid_unit_inv]
      simp

def parityKleinSubgroup : Subgroup CoordEndˣ :=
  Subgroup.closure {P_unit, GammaF_unit}

theorem P_unit_mem_parityKleinSubgroup :
    P_unit ∈ parityKleinSubgroup := by
  exact Subgroup.subset_closure (by simp)

theorem GammaF_unit_mem_parityKleinSubgroup :
    GammaF_unit ∈ parityKleinSubgroup := by
  exact Subgroup.subset_closure (by simp)

theorem M_mid_unit_mem_parityKleinSubgroup :
    M_mid_unit ∈ parityKleinSubgroup := by
  rw [← P_unit_mul_GammaF_unit]
  exact parityKleinSubgroup.mul_mem
    P_unit_mem_parityKleinSubgroup GammaF_unit_mem_parityKleinSubgroup

theorem one_mem_parityKleinSubgroup :
    (1 : CoordEndˣ) ∈ parityKleinSubgroup :=
  parityKleinSubgroup.one_mem

theorem parityUnitPacket_subset_parityKleinSubgroup :
    parityUnitPacket ⊆ (parityKleinSubgroup : Set CoordEndˣ) := by
  intro u hu
  simp only [parityUnitPacket, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact one_mem_parityKleinSubgroup
  · exact P_unit_mem_parityKleinSubgroup
  · exact GammaF_unit_mem_parityKleinSubgroup
  · exact M_mid_unit_mem_parityKleinSubgroup

theorem parityKleinSubgroup_eq_parityPacketSubgroup :
    parityKleinSubgroup = parityPacketSubgroup := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · simp [parityPacketSubgroup, parityUnitPacket]
    · simp [parityPacketSubgroup, parityUnitPacket]
  · intro u hu
    exact parityUnitPacket_subset_parityKleinSubgroup hu

theorem parityKleinSubgroup_mem_parityUnitPacket
    (u : parityKleinSubgroup) :
    (u : CoordEndˣ) ∈ parityUnitPacket := by
  have hu : (u : CoordEndˣ) ∈ parityPacketSubgroup := by
    rw [← parityKleinSubgroup_eq_parityPacketSubgroup]
    exact u.property
  exact hu

theorem parityKleinSubgroup_sq (u : parityKleinSubgroup) : u * u = 1 := by
  have hu := parityKleinSubgroup_mem_parityUnitPacket u
  simp only [parityUnitPacket, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with hu | hu | hu | hu
  · have h : u = (1 : parityKleinSubgroup) := Subtype.ext hu
    rw [h]
    simp
  · have h : u = ⟨P_unit, P_unit_mem_parityKleinSubgroup⟩ := Subtype.ext hu
    rw [h]
    simp
  · have h : u = ⟨GammaF_unit, GammaF_unit_mem_parityKleinSubgroup⟩ :=
      Subtype.ext hu
    rw [h]
    simp
  · have h : u = ⟨M_mid_unit, M_mid_unit_mem_parityKleinSubgroup⟩ :=
      Subtype.ext hu
    rw [h]
    simp

theorem parityKleinSubgroup_isKleinFour : IsKleinFour parityKleinSubgroup := by
  letI : Nontrivial parityKleinSubgroup := by
    refine ⟨⟨⟨P_unit, P_unit_mem_parityKleinSubgroup⟩, 1, ?_⟩⟩
    intro h
    apply one_ne_P_unit
    exact congrArg (fun u : parityKleinSubgroup => (u : CoordEndˣ)) h.symm
  constructor
  · rw [parityKleinSubgroup_eq_parityPacketSubgroup]
    change parityUnitPacket.ncard = 4
    exact parityUnitPacket_ncard
  · apply (Monoid.exponent_eq_prime_iff (by norm_num : Nat.Prime 2)).2
    intro u hu
    apply orderOf_eq_prime
    · simpa [pow_two] using parityKleinSubgroup_sq u
    · exact hu

noncomputable def parityKleinSubgroup_mulEquiv :
    Multiplicative (ZMod 2 × ZMod 2) ≃* parityKleinSubgroup := by
  letI : IsKleinFour parityKleinSubgroup := parityKleinSubgroup_isKleinFour
  exact (IsKleinFour.nonempty_mulEquiv
    (G₁ := Multiplicative (ZMod 2 × ZMod 2))
    (G₂ := parityKleinSubgroup)).some

end InfoGeometry.Canonical.CayleyParityUnitsBridge
