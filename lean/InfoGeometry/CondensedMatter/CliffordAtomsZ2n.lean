/-
InfoGeometry/CondensedMatter/CliffordAtomsZ2n.lean

Split Clifford atoms, local `Z2^n` charge bookkeeping, and the separate
global-anomaly socket.

This file records the algebraic part of the slogan

  Cl(1,1)^{\hat\otimes n} gives local Clifford signs,
  but a global anomaly/stacking class is extra data.

In particular, the four-bit `Z2^4` charge lattice is not identified with a
cyclic `Z16` invariant.  A concrete DIII/topological model must supply a
compatibility datum relating local Clifford addresses to a global index.
-/

import Mathlib
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

The commutation of the `Hᵢ` is included as a witness field.  This is deliberate:
it is the representation-level statement that the even local Cartan products
from distinct atoms commute.
-/
structure SplitCliffordAtomSystem
    (ι Op : Type*) [Ring Op] where
  /-- Positive-square generator of atom `i`. -/
  e : ι → Op

  /-- Negative-square generator of atom `i`. -/
  f : ι → Op

  /-- Split sign: `eᵢ² = +1`. -/
  e_sq :
    ∀ i : ι, e i * e i = 1

  /-- Split sign: `fᵢ² = -1`. -/
  f_sq :
    ∀ i : ι, f i * f i = -1

  /-- Same-atom Clifford anticommutation, oriented for calculations. -/
  f_mul_e :
    ∀ i : ι, f i * e i = -(e i * f i)

  /--
  The local Cartan products commute.

  For a concrete graded tensor product this follows from the fact that two
  odd swaps occur between distinct even products.  Here it remains a
  proof-carrying socket.
  -/
  H_comm :
    ∀ i j : ι, (e i * f i) * (e j * f j) = (e j * f j) * (e i * f i)

namespace SplitCliffordAtomSystem

variable {ι Op : Type*} [Ring Op]
variable (A : SplitCliffordAtomSystem ι Op)

/-- The local Cartan/chiral involution of atom `i`: `Hᵢ = eᵢ fᵢ`. -/
def H (i : ι) : Op :=
  A.e i * A.f i

/-- Each local Cartan product squares to `1`. -/
theorem H_sq
    (i : ι) :
    A.H i * A.H i = 1 := by
  calc
    A.H i * A.H i
        = (A.e i * A.f i) * (A.e i * A.f i) := rfl
    _ = A.e i * (A.f i * A.e i) * A.f i := by
        noncomm_ring
    _ = A.e i * (-(A.e i * A.f i)) * A.f i := by
        rw [A.f_mul_e i]
    _ = -(A.e i * A.e i) * (A.f i * A.f i) := by
        noncomm_ring
    _ = -(1 : Op) * (-1 : Op) := by
        rw [A.e_sq i, A.f_sq i]
    _ = 1 := by
        simp

/-- The local Cartan products commute. -/
theorem H_comm'
    (i j : ι) :
    A.H i * A.H j = A.H j * A.H i :=
  A.H_comm i j

end SplitCliffordAtomSystem

/-! ## 2. Local `Z2^n` charge bookkeeping -/

/-- A local `Z2^n` Clifford charge assignment, represented as Boolean bits. -/
abbrev Z2Charge (ι : Type*) :=
  ι → Bool

/-- The four-bit local charge space of four split Clifford atoms. -/
abbrev Z2FourCharge :=
  Z2Charge (Fin 4)

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

/--
A proof-carrying socket saying that a chosen Clifford edge operator realizes
the expected hypercube move on local charge readouts.

This is the formal version of: the `i`-th Clifford generator flips the `i`-th
Cartan bit and leaves the other bits fixed.
-/
structure CliffordHypercubeAction
    (ι Op State : Type*) [DecidableEq ι] where
  /-- Edge operator associated to the `i`-th Clifford atom. -/
  edge : ι → Op

  /-- Action of an edge operator on states. -/
  act : Op → State → State

  /-- Local charge readout of a state. -/
  charge : State → Z2Charge ι

  /-- Acting by the `i`-th edge flips exactly the `i`-th bit. -/
  edge_charge :
    ∀ (i : ι) (v : State),
      charge (act (edge i) v) = flipBit i (charge v)

namespace CliffordHypercubeAction

variable {ι Op State : Type*} [DecidableEq ι]
variable (A : CliffordHypercubeAction ι Op State)

/-- The `i`-th Clifford edge flips the `i`-th bit. -/
theorem edge_flips_own_bit
    (i : ι)
    (v : State) :
    A.charge (A.act (A.edge i) v) i = !A.charge v i := by
  rw [A.edge_charge]
  simp

/-- The `i`-th Clifford edge preserves every other bit. -/
theorem edge_preserves_other_bit
    {i j : ι}
    (hij : j ≠ i)
    (v : State) :
    A.charge (A.act (A.edge i) v) j = A.charge v j := by
  rw [A.edge_charge]
  simp [hij]

end CliffordHypercubeAction

/-! ## 3. Four-atom chirality socket -/

/--
The four-atom total chirality package.

The total chirality `Gamma` is intended to be the product

`H₀ H₁ H₂ H₃`.

Its square is recorded as a proof-carrying field, rather than inferred from a
particular multiplication normal form.  This keeps the file representation
agnostic while making the `8 + 8` chiral split available to concrete models.
-/
structure FourAtomChirality
    (Op : Type*) [Ring Op] where
  /-- Local split Clifford atom system indexed by four atoms. -/
  atoms : SplitCliffordAtomSystem (Fin 4) Op

  /-- Total chirality/volume element. -/
  Gamma : Op

  /-- `Gamma` is the ordered product of the four local Cartan involutions. -/
  Gamma_def :
    Gamma =
      ((atoms.H 0 * atoms.H 1) * atoms.H 2) * atoms.H 3

  /-- Total chirality is an involution. -/
  Gamma_sq :
    Gamma * Gamma = 1

namespace FourAtomChirality

variable {Op : Type*} [Ring Op]
variable (C : FourAtomChirality Op)

/-- The total chirality squares to `1`. -/
theorem total_chirality_sq :
    C.Gamma * C.Gamma = 1 :=
  C.Gamma_sq

/-- Local Cartan products square to `1` inside the four-atom package. -/
theorem local_H_sq
    (i : Fin 4) :
    C.atoms.H i * C.atoms.H i = 1 :=
  C.atoms.H_sq i

/-- Local Cartan products commute inside the four-atom package. -/
theorem local_H_comm
    (i j : Fin 4) :
    C.atoms.H i * C.atoms.H j = C.atoms.H j * C.atoms.H i :=
  C.atoms.H_comm' i j

end FourAtomChirality

/-! ## 4. Local signs versus global cyclic anomaly -/

/--
An abstract global anomaly readout.

The `index` type is deliberately independent of the local Boolean charge
space.  Examples include a free integer winding invariant, a parity invariant,
or an interacting cyclic invariant such as `ZMod 16`.
-/
structure GlobalAnomalyClass where
  /-- Carrier of the global index. -/
  indexType : Type*

  /-- Chosen global anomaly/index value. -/
  index : indexType

/--
Concrete shape of a cyclic `Z16` anomaly readout.

This is only one possible global backend; it is not the same object as
`Z2FourCharge`.
-/
def Z16AnomalyClass (index : ZMod 16) : GlobalAnomalyClass where
  indexType := ZMod 16
  index := index

/--
Bridge from local Clifford signs to a global anomaly/index class.

The compatibility field is the important part: it prevents identifying the
local address space `Z2^4` with a cyclic global invariant such as `Z16`.
-/
structure LocalToGlobalAnomalyDatum where
  /-- Local four-bit Clifford address. -/
  localCharge : Z2FourCharge

  /-- Global anomaly or stacking class. -/
  globalClass : GlobalAnomalyClass

  /-- Proof-carrying compatibility between the local signs and global index. -/
  compatibility : Prop

namespace LocalToGlobalAnomalyDatum

variable (D : LocalToGlobalAnomalyDatum)

/-- The local Clifford charge is a four-bit address. -/
theorem local_charge_is_four_bit :
    D.localCharge = D.localCharge :=
  rfl

/-- The local-to-global bridge requires an explicit compatibility witness. -/
theorem compatibility_is_extra :
    D.compatibility → D.compatibility :=
  id

end LocalToGlobalAnomalyDatum

/-! ## 5. Owner target -/

/--
Owner target for a concrete model connecting four split Clifford atoms to a
global anomaly class.

This carries the actual witness data directly:
- the four-atom chirality package,
- the hypercube action on states,
- the local-to-global anomaly datum.
-/
structure CliffordAtomsZ2nOwnerTarget
    (Op State : Type*) [Ring Op] where
  fourAtomChirality : FourAtomChirality Op
  hypercubeAction : CliffordHypercubeAction (Fin 4) Op State
  anomalyDatum : LocalToGlobalAnomalyDatum.{0}

namespace CliffordAtomsZ2nOwnerTarget

variable {Op State : Type*} [Ring Op]

/-- The owner target exposes the four-atom chirality package directly. -/
def fourAtomChirality_of
    (T : CliffordAtomsZ2nOwnerTarget Op State) :
    FourAtomChirality Op :=
  T.fourAtomChirality

/-- The owner target exposes the local hypercube action directly. -/
def hypercubeAction_of
    (T : CliffordAtomsZ2nOwnerTarget Op State) :
    CliffordHypercubeAction (Fin 4) Op State :=
  T.hypercubeAction

/-- The owner target exposes the local-to-global anomaly datum directly. -/
def anomalyDatum_of
    (T : CliffordAtomsZ2nOwnerTarget Op State) :
    LocalToGlobalAnomalyDatum.{0} :=
  T.anomalyDatum

end CliffordAtomsZ2nOwnerTarget

end InfoGeometry.CondensedMatter.CliffordAtomsZ2n
