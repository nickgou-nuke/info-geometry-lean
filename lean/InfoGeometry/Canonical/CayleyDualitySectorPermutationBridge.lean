import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.V4RootSystem

/-!
# Label-level permutation action of Cayley/Hodge dualities

The four joint parity sectors are represented by a finite label type.  Cayley
conjugation and the middle exchange are the two independent transpositions;
Hodge duality is their product.  This owner records the finite permutation
representation only, without identifying it with a physical symmetry group.
-/

namespace InfoGeometry.Canonical.CayleyDualitySectorPermutationBridge

open InfoGeometry.Topology.V4RootSystem

inductive ParitySector
  | plusPlus
  | plusMinus
  | minusPlus
  | minusMinus
  deriving DecidableEq, Fintype

open ParitySector

def sectorC : Equiv.Perm ParitySector := Equiv.swap plusPlus minusMinus

def sectorXi : Equiv.Perm ParitySector := Equiv.swap plusMinus minusPlus

def sectorStar : Equiv.Perm ParitySector := sectorC * sectorXi

@[simp] theorem sectorC_plusPlus : sectorC plusPlus = minusMinus := by rfl
@[simp] theorem sectorC_minusMinus : sectorC minusMinus = plusPlus := by rfl
@[simp] theorem sectorC_plusMinus : sectorC plusMinus = plusMinus := by
  exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
@[simp] theorem sectorC_minusPlus : sectorC minusPlus = minusPlus := by
  exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)

@[simp] theorem sectorXi_plusPlus : sectorXi plusPlus = plusPlus := by
  exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
@[simp] theorem sectorXi_minusMinus : sectorXi minusMinus = minusMinus := by
  exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
@[simp] theorem sectorXi_plusMinus : sectorXi plusMinus = minusPlus := by rfl
@[simp] theorem sectorXi_minusPlus : sectorXi minusPlus = plusMinus := by rfl

@[simp] theorem sectorStar_plusPlus : sectorStar plusPlus = minusMinus := by rfl
@[simp] theorem sectorStar_minusMinus : sectorStar minusMinus = plusPlus := by rfl
@[simp] theorem sectorStar_plusMinus : sectorStar plusMinus = minusPlus := by rfl
@[simp] theorem sectorStar_minusPlus : sectorStar minusPlus = plusMinus := by rfl

theorem sectorC_sq : sectorC * sectorC = 1 := by native_decide
theorem sectorXi_sq : sectorXi * sectorXi = 1 := by native_decide
theorem sectorC_comm_sectorXi : sectorC * sectorXi = sectorXi * sectorC := by
  native_decide
theorem sectorStar_eq_sectorXi_mul_sectorC :
    sectorStar = sectorXi * sectorC := by
  exact sectorC_comm_sectorXi
theorem sectorStar_sq : sectorStar * sectorStar = 1 := by native_decide

def sectorPermutation : V4Group → Equiv.Perm ParitySector
  | V4Group.I => 1
  | V4Group.W1 => sectorC
  | V4Group.W2 => sectorXi
  | V4Group.W12 => sectorStar

def sectorPermutationHom : V4Group →* Equiv.Perm ParitySector where
  toFun := sectorPermutation
  map_one' := by native_decide
  map_mul' := by
    intro g h
    cases g <;> cases h <;> native_decide

@[simp] theorem sectorPermutation_I : sectorPermutation V4Group.I = 1 := rfl
@[simp] theorem sectorPermutation_W1 : sectorPermutation V4Group.W1 = sectorC := rfl
@[simp] theorem sectorPermutation_W2 : sectorPermutation V4Group.W2 = sectorXi := rfl
@[simp] theorem sectorPermutation_W12 : sectorPermutation V4Group.W12 = sectorStar := rfl

theorem sectorC_ne_sectorXi : sectorC ≠ sectorXi := by native_decide
theorem sectorC_ne_sectorStar : sectorC ≠ sectorStar := by native_decide
theorem sectorXi_ne_sectorStar : sectorXi ≠ sectorStar := by native_decide
theorem sectorC_ne_one : sectorC ≠ 1 := by native_decide
theorem sectorXi_ne_one : sectorXi ≠ 1 := by native_decide
theorem sectorStar_ne_one : sectorStar ≠ 1 := by native_decide

theorem sectorPermutation_injective : Function.Injective sectorPermutationHom := by
  apply (injective_iff_map_eq_one sectorPermutationHom).2
  intro g hg
  cases g
  · rfl
  · exfalso
    apply sectorC_ne_one
    simpa [sectorPermutationHom, sectorPermutation] using hg
  · exfalso
    apply sectorXi_ne_one
    simpa [sectorPermutationHom, sectorPermutation] using hg
  · exfalso
    apply sectorStar_ne_one
    simpa [sectorPermutationHom, sectorPermutation] using hg

/-- The faithful sector action has exactly the four expected permutation units. -/
theorem sectorPermutationHom_range :
    Set.range sectorPermutationHom =
      ({1, sectorC, sectorXi, sectorStar} : Set (Equiv.Perm ParitySector)) := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    cases g <;> simp [sectorPermutationHom, sectorPermutation]
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨V4Group.I, rfl⟩
    · exact ⟨V4Group.W1, rfl⟩
    · exact ⟨V4Group.W2, rfl⟩
    · exact ⟨V4Group.W12, rfl⟩

def outerSectorOrbit : Set ParitySector := {plusPlus, minusMinus}
def middleSectorOrbit : Set ParitySector := {plusMinus, minusPlus}

theorem sectorStar_maps_outerSectorOrbit (s : ParitySector) :
    s ∈ outerSectorOrbit → sectorStar s ∈ outerSectorOrbit := by
  intro hs
  cases s <;> simp [outerSectorOrbit, sectorStar] at hs ⊢

theorem sectorStar_maps_middleSectorOrbit (s : ParitySector) :
    s ∈ middleSectorOrbit → sectorStar s ∈ middleSectorOrbit := by
  intro hs
  cases s <;> simp [middleSectorOrbit, sectorStar] at hs ⊢

theorem sectorC_preserves_outerSectorOrbit :
    sectorC '' outerSectorOrbit = outerSectorOrbit := by
  have hC : sectorC.symm = sectorC := by
    ext s
    cases s <;> simp [sectorC, Equiv.swap_apply_def]
  ext s
  cases s <;>
    simp [hC, outerSectorOrbit, sectorC_plusPlus, sectorC_minusMinus,
      sectorC_plusMinus, sectorC_minusPlus]

theorem sectorXi_preserves_outerSectorOrbit :
    sectorXi '' outerSectorOrbit = outerSectorOrbit := by
  have hXi : sectorXi.symm = sectorXi := by
    ext s
    cases s <;> simp [sectorXi, Equiv.swap_apply_def]
  ext s
  cases s <;>
    simp [hXi, outerSectorOrbit, sectorXi_plusPlus, sectorXi_minusMinus,
      sectorXi_plusMinus, sectorXi_minusPlus]

theorem sectorC_preserves_middleSectorOrbit :
    sectorC '' middleSectorOrbit = middleSectorOrbit := by
  have hC : sectorC.symm = sectorC := by
    ext s
    cases s <;> simp [sectorC, Equiv.swap_apply_def]
  ext s
  cases s <;>
    simp [hC, middleSectorOrbit, sectorC_plusPlus, sectorC_minusMinus,
      sectorC_plusMinus, sectorC_minusPlus]

theorem sectorXi_preserves_middleSectorOrbit :
    sectorXi '' middleSectorOrbit = middleSectorOrbit := by
  have hXi : sectorXi.symm = sectorXi := by
    ext s
    cases s <;> simp [sectorXi, Equiv.swap_apply_def]
  ext s
  cases s <;>
    simp [hXi, middleSectorOrbit, sectorXi_plusPlus, sectorXi_minusMinus,
      sectorXi_plusMinus, sectorXi_minusPlus]

theorem sectorStar_preserves_outerSectorOrbit :
    sectorStar '' outerSectorOrbit = outerSectorOrbit := by
  have hStar : sectorStar.symm = sectorStar := by
    native_decide
  ext s
  cases s <;>
    simp [hStar, outerSectorOrbit, sectorStar_plusPlus, sectorStar_minusMinus,
      sectorStar_plusMinus, sectorStar_minusPlus]

theorem sectorStar_preserves_middleSectorOrbit :
    sectorStar '' middleSectorOrbit = middleSectorOrbit := by
  have hStar : sectorStar.symm = sectorStar := by
    native_decide
  ext s
  cases s <;>
    simp [hStar, middleSectorOrbit, sectorStar_plusPlus, sectorStar_minusMinus,
      sectorStar_plusMinus, sectorStar_minusPlus]

theorem outerSectorOrbit_union_middleSectorOrbit :
    outerSectorOrbit ∪ middleSectorOrbit = Set.univ := by
  ext s
  cases s <;> simp [outerSectorOrbit, middleSectorOrbit]

theorem outerSectorOrbit_inter_middleSectorOrbit :
    outerSectorOrbit ∩ middleSectorOrbit = (∅ : Set ParitySector) := by
  ext s
  cases s <;> simp [outerSectorOrbit, middleSectorOrbit]

end InfoGeometry.Canonical.CayleyDualitySectorPermutationBridge
