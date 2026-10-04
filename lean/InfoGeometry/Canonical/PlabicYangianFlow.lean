import Mathlib

/-!
# Finite bilocal commutator identities under cyclic reordering

This file formalizes the algebraic part of the proposed boundary-flow
calculation.  It proves cyclic invariance of the ordered bilocal commutator
sum for three and four charges on the zero-total-charge locus.  The result is
about elements of an associative ring; it does not model plabic embeddings,
Yangian differential operators, or urban-renewal moves.
-/

namespace InfoGeometry.PlabicYangian

/-- The commutator in an associative ring. -/
def lieBracket {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

@[simp] theorem lieBracket_self {A : Type*} [Ring A] (x : A) :
    lieBracket x x = 0 := by
  simp [lieBracket]

theorem lieBracket_antisymm {A : Type*} [Ring A] (x y : A) :
    lieBracket x y = - lieBracket y x := by
  simp [lieBracket]

/-- The three-cycle on the ordered labels `0,1,2`. -/
def cyclicShift3 (i : Fin 3) : Fin 3 :=
  match i with
  | 0 => 1
  | 1 => 2
  | 2 => 0

def level0_3 {A : Type*} [Ring A] (E : Fin 3 → A) : A :=
  E 0 + E 1 + E 2

/-- The ordered bilocal commutator sum on three charges. -/
def level1_3 {A : Type*} [Ring A] (E : Fin 3 → A) : A :=
  lieBracket (E 0) (E 1) + lieBracket (E 0) (E 2) + lieBracket (E 1) (E 2)

/-- On zero total charge, the three-charge bilocal commutator is invariant
under cyclic reordering. -/
theorem level1_3_cyclic_invariant {A : Type*} [Ring A] (E : Fin 3 → A)
    (h : level0_3 E = 0) :
    level1_3 (E ∘ cyclicShift3) = level1_3 E := by
  have htail : E 1 + E 2 = -E 0 := by
    dsimp [level0_3] at h
    calc
      E 1 + E 2 = -E 0 + (E 0 + E 1 + E 2) := by abel
      _ = -E 0 := by rw [h]; simp
  have hlast : E 2 = -E 0 - E 1 := by
    calc
      E 2 = (E 1 + E 2) - E 1 := by abel
      _ = -E 0 - E 1 := by rw [htail]
  dsimp [level1_3, cyclicShift3, lieBracket]
  rw [hlast]
  noncomm_ring

/-- The four-cycle on the ordered labels `0,1,2,3`. -/
def cyclicShift4 (i : Fin 4) : Fin 4 :=
  match i with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 0

def level0_4 {A : Type*} [Ring A] (E : Fin 4 → A) : A :=
  E 0 + E 1 + E 2 + E 3

/-- The ordered bilocal commutator sum on four charges. -/
def level1_4 {A : Type*} [Ring A] (E : Fin 4 → A) : A :=
  lieBracket (E 0) (E 1) + lieBracket (E 0) (E 2) +
  lieBracket (E 0) (E 3) + lieBracket (E 1) (E 2) +
  lieBracket (E 1) (E 3) + lieBracket (E 2) (E 3)

/-- Exact change in the four-charge bilocal sum under cyclic reordering.
This identity records the boundary terms before imposing zero total charge. -/
theorem level1_4_cyclic_difference {A : Type*} [Ring A] (E : Fin 4 → A) :
    level1_4 (E ∘ cyclicShift4) - level1_4 E =
      2 * lieBracket (E 1 + E 2 + E 3) (E 0) := by
  dsimp [level1_4, cyclicShift4, lieBracket]
  noncomm_ring

/-- The ordered four-charge bilocal commutator is cyclically invariant when
the total charge vanishes. -/
theorem level1_4_cyclic_invariant {A : Type*} [Ring A] (E : Fin 4 → A)
    (h : level0_4 E = 0) :
    level1_4 (E ∘ cyclicShift4) = level1_4 E := by
  have htail : E 1 + E 2 + E 3 = -E 0 := by
    dsimp [level0_4] at h
    calc
      E 1 + E 2 + E 3 = -E 0 + (E 0 + E 1 + E 2 + E 3) := by abel
      _ = -E 0 := by rw [h]; simp
  have hchange := level1_4_cyclic_difference E
  rw [htail] at hchange
  have hzero : 2 * lieBracket (-E 0) (E 0) = 0 := by
    simp [lieBracket]
  have hchangezero : level1_4 (E ∘ cyclicShift4) - level1_4 E = 0 := by
    calc
      level1_4 (E ∘ cyclicShift4) - level1_4 E =
          2 * lieBracket (-E 0) (E 0) := hchange
      _ = 0 := hzero
  exact sub_eq_zero.mp hchangezero

/-- The nearest-neighbor cyclic commutator contour is invariant off shell. -/
def cyclicFlux4 {A : Type*} [Ring A] (E : Fin 4 → A) : A :=
  lieBracket (E 0) (E 1) + lieBracket (E 1) (E 2) +
  lieBracket (E 2) (E 3) + lieBracket (E 3) (E 0)

theorem cyclicFlux4_shift_invariant {A : Type*} [Ring A] (E : Fin 4 → A) :
    cyclicFlux4 (E ∘ cyclicShift4) = cyclicFlux4 E := by
  dsimp [cyclicFlux4, cyclicShift4]
  abel

end InfoGeometry.PlabicYangian
