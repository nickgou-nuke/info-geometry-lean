/-
InfoGeometry/CondensedMatter/CliffordAtomsZ2n.lean

Split Clifford atoms, local `Z2^n` charge bookkeeping, and the separate
global-anomaly boundary.

This file records the algebraic part of the slogan

  Cl(1,1)^{\hat\otimes n} gives local Clifford signs,
  but a global anomaly/stacking class is extra data.

In particular, the four-bit `Z2^4` charge lattice is not identified with a
cyclic `Z16` invariant.  A concrete DIII/topological model must supply a
compatibility datum relating local Clifford addresses to a global index.
-/

import Mathlib.Tactic
import InfoGeometry.CondensedMatter.DIIISuperfluid

noncomputable section

namespace InfoGeometry.CondensedMatter.CliffordAtomsZ2n

/-! ## 1. Split Clifford atom systems -/

/--
A finite system of split Clifford atoms in an ambient real operator algebra.

For each atom `i`, the intended generators satisfy

`eᵢ² = +1`, `fᵢ² = -1`, and `fᵢ eᵢ = - eᵢ fᵢ`.

The local Cartan/chiral involution is defined as

`Hᵢ = eᵢ fᵢ`.

The commutation of the `Hᵢ` is included as a property field.  This is deliberate:
it is the representation-level statement that the even local Cartan products
from distinct atoms commute.
-/
structure SplitCliffordAtomSystem
    (ι Op : Type*) [Ring Op] where
  /-- Positive-square generator of atom `i`. -/
  e : ι → Op

  /-- Negative-square generator of atom `i`. -/
  f : ι → Op

def SplitCliffordAtomSystemLaws
    {ι Op : Type*} [Ring Op]
    (A : SplitCliffordAtomSystem ι Op) : Prop :=
  (∀ i : ι, A.e i * A.e i = 1) ∧
  (∀ i : ι, A.f i * A.f i = -1) ∧
  (∀ i : ι, A.f i * A.e i = -(A.e i * A.f i)) ∧
  (∀ i j : ι, (A.e i * A.f i) * (A.e j * A.f j) =
    (A.e j * A.f j) * (A.e i * A.f i))

namespace SplitCliffordAtomSystem

variable {ι Op : Type*} [Ring Op]
variable (A : SplitCliffordAtomSystem ι Op)

/-- The local Cartan/chiral involution of atom `i`: `Hᵢ = eᵢ fᵢ`. -/
def H (i : ι) : Op :=
  A.e i * A.f i

/-- Each local Cartan product squares to `1`. -/
theorem H_sq
    (hA : SplitCliffordAtomSystemLaws A)
    (i : ι) :
    A.H i * A.H i = 1 := by
  calc
    A.H i * A.H i
        = (A.e i * A.f i) * (A.e i * A.f i) := rfl
    _ = A.e i * (A.f i * A.e i) * A.f i := by
        noncomm_ring
    _ = A.e i * (-(A.e i * A.f i)) * A.f i := by
        rw [hA.2.2.1 i]
    _ = -(A.e i * A.e i) * (A.f i * A.f i) := by
        noncomm_ring
    _ = -(1 : Op) * (-1 : Op) := by
        rw [hA.1 i, hA.2.1 i]
    _ = 1 := by
        simp

/-- The local Cartan products commute. -/
theorem H_comm'
    (hA : SplitCliffordAtomSystemLaws A)
    (i j : ι) :
    A.H i * A.H j = A.H j * A.H i :=
  hA.2.2.2 i j

end SplitCliffordAtomSystem

/-! ## 2. Local `Z2^n` charge bookkeeping -/

/-- A local `Z2^n` Clifford charge assignment, represented as Boolean bits. -/
abbrev Z2Charge (ι : Type*) :=
  ι → Bool

/-- Flip the `i`-th local Clifford bit. -/
def flipBit
    {ι : Type*} [DecidableEq ι]
    (i : ι)
    (charge : Z2Charge ι) : Z2Charge ι :=
  Function.update charge i (!charge i)

@[simp]
theorem flipBit_self
    {ι : Type*} [DecidableEq ι]
    (i : ι)
    (charge : Z2Charge ι) :
    flipBit i charge i = !charge i := by
  simp [flipBit]

@[simp]
theorem flipBit_other
    {ι : Type*} [DecidableEq ι]
    {i j : ι}
    (hij : j ≠ i)
    (charge : Z2Charge ι) :
    flipBit i charge j = charge j := by
  simp [flipBit, Function.update_of_ne hij]

@[simp]
theorem flipBit_involutive
    {ι : Type*} [DecidableEq ι]
    (i : ι)
    (charge : Z2Charge ι) :
    flipBit i (flipBit i charge) = charge := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flipBit]
  · rw [flipBit_other hji, flipBit_other hji]

def flipBitEquiv
    {ι : Type*} [DecidableEq ι]
    (i : ι) : Z2Charge ι ≃ Z2Charge ι where
  toFun := flipBit i
  invFun := flipBit i
  left_inv charge := flipBit_involutive i charge
  right_inv charge := flipBit_involutive i charge

theorem flipBit_comm
    {ι : Type*} [DecidableEq ι]
    {i j : ι}
    (hij : i ≠ j)
    (charge : Z2Charge ι) :
    flipBit i (flipBit j charge) = flipBit j (flipBit i charge) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [flipBit, hij]
  · by_cases hkj : k = j
    · subst k
      simp [flipBit, hki]
    · simp [flipBit, hki, hkj, Ne.symm hij]

theorem flipBitEquiv_comm
    {ι : Type*} [DecidableEq ι]
    {i j : ι}
    (hij : i ≠ j) :
    (flipBitEquiv i).trans (flipBitEquiv j) =
      (flipBitEquiv j).trans (flipBitEquiv i) := by
  apply Equiv.ext
  intro charge
  simpa [flipBitEquiv] using (flipBit_comm hij charge).symm

/--
A proof-carrying action datum saying that a chosen Clifford edge operator realizes
the expected hypercube move on local charge readouts.

This is the formal version of: the `i`-th Clifford generator flips the `i`-th
Cartan bit and leaves the other bits fixed.
-/
structure CliffordHypercubeActionData
    (ι Op State : Type*) [DecidableEq ι] where
  /-- Edge operator associated to the `i`-th Clifford atom. -/
  edge : ι → Op

  /-- Action of an edge operator on states. -/
  act : Op → State → State

  /-- Local charge readout of a state. -/
  charge : State → Z2Charge ι

def CliffordHypercubeActionLaw
    {ι Op State : Type*} [DecidableEq ι]
    (A : CliffordHypercubeActionData ι Op State) : Prop :=
  ∀ (i : ι) (v : State),
    A.charge (A.act (A.edge i) v) = flipBit i (A.charge v)

def CliffordHypercubeAction
    (ι Op State : Type*) [DecidableEq ι] :=
  { A : CliffordHypercubeActionData ι Op State // CliffordHypercubeActionLaw A }

namespace CliffordHypercubeAction

variable {ι Op State : Type*} [DecidableEq ι]
variable (A : CliffordHypercubeAction ι Op State)

/-- The `i`-th Clifford edge flips the `i`-th bit. -/
theorem edge_flips_own_bit
    (i : ι)
    (v : State) :
    A.1.charge (A.1.act (A.1.edge i) v) i = !A.1.charge v i := by
  rw [A.2]
  simp

theorem edge_preserves_other_bit
    (hA : CliffordHypercubeActionLaw A.1)
    {i j : ι}
    (hij : j ≠ i)
    (v : State) :
    A.1.charge (A.1.act (A.1.edge i) v) j = A.1.charge v j := by
  rw [hA]
  simp [hij]

theorem edge_charge_involutive
    (hA : CliffordHypercubeActionLaw A.1)
    (i : ι)
    (v : State) :
    A.1.charge (A.1.act (A.1.edge i) (A.1.act (A.1.edge i) v)) =
      A.1.charge v := by
  rw [hA, hA, flipBit_involutive]

theorem edge_charge_comm
    (hA : CliffordHypercubeActionLaw A.1)
    {i j : ι}
    (hij : i ≠ j)
    (v : State) :
    A.1.charge (A.1.act (A.1.edge i) (A.1.act (A.1.edge j) v)) =
      A.1.charge (A.1.act (A.1.edge j) (A.1.act (A.1.edge i) v)) := by
  rw [hA, hA, hA, hA]
  exact flipBit_comm hij (A.1.charge v)

end CliffordHypercubeAction

/- Old law-parametrized statements are subsumed by the subtype field above. -/
/-
    (hA : CliffordHypercubeActionLaw A)
    (i : ι)
    (v : State) :
    A.charge (A.act (A.edge i) v) i = !A.charge v i := by
  rw [hA]
  simp

/-- The `i`-th Clifford edge preserves every other bit. -/
theorem edge_preserves_other_bit
    (hA : CliffordHypercubeActionLaw A)
    {i j : ι}
    (hij : j ≠ i)
    (v : State) :
    A.charge (A.act (A.edge i) v) j = A.charge v j := by
  rw [hA]
  simp [hij]

theorem edge_charge_involutive
    (hA : CliffordHypercubeActionLaw A)
    (i : ι)
    (v : State) :
    A.charge (A.act (A.edge i) (A.act (A.edge i) v)) = A.charge v := by
  rw [hA, hA, flipBit_involutive]

theorem edge_charge_comm
    (hA : CliffordHypercubeActionLaw A)
    {i j : ι}
    (hij : i ≠ j)
    (v : State) :
    A.charge (A.act (A.edge i) (A.act (A.edge j) v)) =
      A.charge (A.act (A.edge j) (A.act (A.edge i) v)) := by
  rw [hA, hA, hA, hA]
  exact flipBit_comm hij (A.charge v)

end CliffordHypercubeAction
 -/

/-! ## 3. Four-atom chirality action -/

/--
The four-atom total chirality package.

The total chirality `Gamma` is intended to be the product

`H₀ H₁ H₂ H₃`.

Its square is recorded as a proof-carrying field, rather than inferred from a
particular multiplication normal form.  This keeps the file representation
agnostic while making the `8 + 8` chiral split available to concrete models.
-/
structure FourAtomChiralityData
    (Op : Type*) [Ring Op] where
  /-- Local split Clifford atom system indexed by four atoms. -/
  atoms : SplitCliffordAtomSystem (Fin 4) Op

  /-- Total chirality/volume element. -/
  Gamma : Op

def FourAtomChiralityLaws
    {Op : Type*} [Ring Op] (C : FourAtomChiralityData Op) : Prop :=
  SplitCliffordAtomSystemLaws C.atoms ∧
  C.Gamma = ((C.atoms.H 0 * C.atoms.H 1) * C.atoms.H 2) * C.atoms.H 3 ∧
  C.Gamma * C.Gamma = 1

def FourAtomChirality
    (Op : Type*) [Ring Op] :=
  { C : FourAtomChiralityData Op // FourAtomChiralityLaws C }

namespace FourAtomChirality

variable {Op : Type*} [Ring Op]
variable (C : FourAtomChirality Op)

theorem sq_mul_of_sq_one_of_commute
    {a b : Op}
    (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    (a * b) * (a * b) = 1 := by
  calc
    (a * b) * (a * b) = a * (b * a) * b := by noncomm_ring
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by noncomm_ring
    _ = 1 := by rw [ha, hb]; simp

theorem total_chirality_sq_from_atoms :
    C.1.Gamma * C.1.Gamma = 1 := by
  let h0 := C.1.atoms.H 0
  let h1 := C.1.atoms.H 1
  let h2 := C.1.atoms.H 2
  let h3 := C.1.atoms.H 3
  have h01 : (h0 * h1) * (h0 * h1) = 1 := by
    exact sq_mul_of_sq_one_of_commute
      (C.1.atoms.H_sq C.2.1 0) (C.1.atoms.H_sq C.2.1 1)
      (C.1.atoms.H_comm' C.2.1 0 1)
  have h23 : (h2 * h3) * (h2 * h3) = 1 := by
    exact sq_mul_of_sq_one_of_commute
      (C.1.atoms.H_sq C.2.1 2) (C.1.atoms.H_sq C.2.1 3)
      (C.1.atoms.H_comm' C.2.1 2 3)
  have hcomm : (h0 * h1) * (h2 * h3) = (h2 * h3) * (h0 * h1) := by
    dsimp [h0, h1, h2, h3]
    calc
      (C.1.atoms.H 0 * C.1.atoms.H 1) * (C.1.atoms.H 2 * C.1.atoms.H 3) =
          C.1.atoms.H 0 * (C.1.atoms.H 1 * C.1.atoms.H 2) * C.1.atoms.H 3 := by
            noncomm_ring
      _ = C.1.atoms.H 0 * (C.1.atoms.H 2 * C.1.atoms.H 1) * C.1.atoms.H 3 := by
            rw [C.1.atoms.H_comm' C.2.1 1 2]
      _ = (C.1.atoms.H 0 * C.1.atoms.H 2) * C.1.atoms.H 1 * C.1.atoms.H 3 := by
            noncomm_ring
      _ = (C.1.atoms.H 2 * C.1.atoms.H 0) * C.1.atoms.H 1 * C.1.atoms.H 3 := by
            rw [C.1.atoms.H_comm' C.2.1 0 2]
      _ = C.1.atoms.H 2 * C.1.atoms.H 0 * (C.1.atoms.H 1 * C.1.atoms.H 3) := by
            noncomm_ring
      _ = C.1.atoms.H 2 * C.1.atoms.H 0 * (C.1.atoms.H 3 * C.1.atoms.H 1) := by
            rw [C.1.atoms.H_comm' C.2.1 1 3]
      _ = C.1.atoms.H 2 * C.1.atoms.H 0 * C.1.atoms.H 3 * C.1.atoms.H 1 := by
            noncomm_ring
      _ = C.1.atoms.H 2 * (C.1.atoms.H 0 * C.1.atoms.H 3) * C.1.atoms.H 1 := by
            noncomm_ring
      _ = C.1.atoms.H 2 * (C.1.atoms.H 3 * C.1.atoms.H 0) * C.1.atoms.H 1 := by
            rw [C.1.atoms.H_comm' C.2.1 0 3]
      _ = (C.1.atoms.H 2 * C.1.atoms.H 3) *
          (C.1.atoms.H 0 * C.1.atoms.H 1) := by
            noncomm_ring
  rw [C.2.2.1]
  simpa [h0, h1, h2, h3, mul_assoc] using
    (sq_mul_of_sq_one_of_commute h01 h23 hcomm)

/-- The total chirality squares to `1`. -/
theorem total_chirality_sq :
    C.1.Gamma * C.1.Gamma = 1 :=
  C.total_chirality_sq_from_atoms

theorem total_chirality_pow_four :
    C.1.Gamma ^ 4 = 1 := by
  have hsq : C.1.Gamma ^ 2 = 1 := by
    simpa [pow_two] using C.total_chirality_sq
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
  simp

/-- Local Cartan products square to `1` inside the four-atom package. -/
theorem local_H_sq
    (i : Fin 4) :
    C.1.atoms.H i * C.1.atoms.H i = 1 :=
  C.1.atoms.H_sq C.2.1 i

/-- Local Cartan products commute inside the four-atom package. -/
theorem local_H_comm
    (i j : Fin 4) :
    C.1.atoms.H i * C.1.atoms.H j = C.1.atoms.H j * C.1.atoms.H i :=
  C.1.atoms.H_comm' C.2.1 i j

end FourAtomChirality

end InfoGeometry.CondensedMatter.CliffordAtomsZ2n
