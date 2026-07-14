/-
InfoGeometry/OperatorAlgebra/CliffordAtomsZ2n.lean

Split Clifford atoms and local Z2 charge addresses.

This module records the local Clifford bookkeeping behind
`Cl(1,1)^{hat tensor n}`-style constructions.  The resulting `Z2^n` charge
hypercube is a local Cartan/sign address space.  It is deliberately not
identified with cyclic global anomaly classes such as `Z16`.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CliffordAtomsZ2n

/-! ## 1. Split Clifford atoms -/

/--
A single split Clifford atom `Cl(1,1)`.

The local Cartan/chiral element is `h = e f`.  Its square is derived below,
not stored as data.
-/
structure SplitCliffordAtom
    (Op : Type*) [Ring Op] where
  /-- Positive-square split generator. -/
  e : Op

  /-- Negative-square split generator. -/
  f : Op

  /-- `e² = +1`. -/
  e_sq :
    e * e = 1

  /-- `f² = -1`. -/
  f_sq :
    f * f = -1

  /-- Same-atom anticommutation. -/
  anticomm :
    e * f = -(f * e)

namespace SplitCliffordAtom

variable {Op : Type*} [Ring Op]
variable (A : SplitCliffordAtom Op)

/-- The local split-Cartan element `h = e f`. -/
def h : Op :=
  A.e * A.f

/-- The local split-Cartan element is an involution: `(e f)² = 1`. -/
theorem h_sq :
    A.h * A.h = 1 := by
  calc
    A.h * A.h
        = (A.e * A.f) * (A.e * A.f) := by
            rfl
    _ = A.e * (A.f * A.e) * A.f := by
            noncomm_ring
    _ = A.e * (-(A.e * A.f)) * A.f := by
            rw [A.anticomm]
            simp
    _ = -(A.e * (A.e * A.f)) * A.f := by
            rw [mul_neg]
    _ = -((A.e * A.e) * A.f) * A.f := by
            rw [mul_assoc]
    _ = -((1 : Op) * A.f) * A.f := by
            rw [A.e_sq]
    _ = (-A.f) * A.f := by
            rw [one_mul]
    _ = -(A.f * A.f) := by
            rw [neg_mul]
    _ = -(-1 : Op) := by
            rw [A.f_sq]
    _ = 1 := by
            simp

end SplitCliffordAtom

/--
A finite system of split Clifford atoms.

For each atom `i`, `e i` and `f i` are odd generators with opposite square
signs, and `H i = e i * f i` is the associated local Cartan/chiral involution.

The commuting laws for the `H i` are explicit fields.  This keeps the interface
usable for graded tensor products without forcing one particular implementation
of Koszul signs at this abstract layer.
-/
structure SplitCliffordAtomSystem
    (ι Op : Type*) [Fintype ι] [Ring Op] where
  /-- Positive-square split generator. -/
  e : ι → Op

  /-- Negative-square split generator. -/
  f : ι → Op

  /-- `e_i^2 = +1`. -/
  e_sq :
    ∀ i : ι, e i * e i = 1

  /-- `f_i^2 = -1`. -/
  f_sq :
    ∀ i : ι, f i * f i = -1

  /-- Same-atom anticommutation. -/
  same_anticomm :
    ∀ i : ι, e i * f i = -(f i * e i)

  /-- Local Cartan/chiral involution. -/
  H : ι → Op

  /-- `H_i = e_i f_i`. -/
  H_def :
    ∀ i : ι, H i = e i * f i

  /-- `H_i^2 = 1`. -/
  H_sq :
    ∀ i : ι, H i * H i = 1

  /-- The Cartan involutions commute. -/
  H_comm :
    ∀ i j : ι, H i * H j = H j * H i

namespace SplitCliffordAtomSystem

variable {ι Op : Type*} [Fintype ι] [Ring Op]
variable (A : SplitCliffordAtomSystem ι Op)

/-- Re-export the local Cartan square law. -/
theorem H_square
    (i : ι) :
    A.H i * A.H i = 1 :=
  A.H_sq i

/-- Re-export commutativity of the local Cartan involutions. -/
theorem H_mul_comm
    (i j : ι) :
    A.H i * A.H j = A.H j * A.H i :=
  A.H_comm i j

/-- The local Cartan involution attached to an atom. -/
def cartan
    (i : ι) : Op :=
  A.H i

end SplitCliffordAtomSystem

/-! ## 2. Four-atom local charge cube -/

/-- A `Z2^n` multicharge, represented as `n` Boolean Clifford bits. -/
def MultiCharge
    (n : ℕ) : Type :=
  Fin n → Bool

/-- Flip the `i`th Clifford bit of a multicharge. -/
def flip
    {n : ℕ}
    (q : MultiCharge n)
    (i : Fin n) : MultiCharge n :=
  fun j => if j = i then !q j else q j

@[simp]
theorem flip_self
    {n : ℕ}
    (q : MultiCharge n)
    (i : Fin n) :
    flip q i i = !q i := by
  simp [flip]

@[simp]
theorem flip_ne
    {n : ℕ}
    (q : MultiCharge n)
    {i j : Fin n}
    (h : j ≠ i) :
    flip q i j = q j := by
  simp [flip, h]

/--
The four-bit local charge address space.

This is the `Z2^4` bookkeeping layer, not a cyclic `Z16` anomaly.
-/
abbrev Z2FourCharge : Type :=
  MultiCharge 4

/-- Alias emphasizing the four-bit charge space attached to `Cl(1,1)^⊗4`. -/
abbrev Charge4 : Type :=
  MultiCharge 4

/--
A local Clifford weight for a four-atom split Clifford system.
-/
structure CliffordWeight
    {Op : Type*} [Ring Op]
    (A : SplitCliffordAtomSystem (Fin 4) Op) where
  /-- The four local Cartan bits. -/
  charge : Z2FourCharge

/--
Flip exactly one local Clifford bit.
-/
def flipCharge
    (i : Fin 4)
    (c : Z2FourCharge) : Z2FourCharge :=
  flip c i

@[simp]
theorem flipCharge_self
    (i : Fin 4)
    (c : Z2FourCharge) :
    flipCharge i c i = !c i := by
  simp [flipCharge]

theorem flipCharge_of_ne
    {i j : Fin 4}
    (hij : j ≠ i)
    (c : Z2FourCharge) :
    flipCharge i c j = c j := by
  simp [flipCharge, flip_ne c hij]

/--
Apply a local edge flip to a Clifford weight.
-/
def CliffordWeight.flip
    {Op : Type*} [Ring Op]
    {A : SplitCliffordAtomSystem (Fin 4) Op}
    (W : CliffordWeight A)
    (i : Fin 4) : CliffordWeight A where
  charge := flipCharge i W.charge

/-! ## 3. Cartan projectors and chirality for four atoms -/

/-- A four-atom split Clifford Cartan system. -/
abbrev SplitClifford4Cartan
    (Op : Type*) [Ring Op] :=
  SplitCliffordAtomSystem (Fin 4) Op

/-- Interpret a Boolean sector bit as the sign `+1` or `-1`. -/
def boolSign
    (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The scalar sign attached to the `i`th charge bit. -/
def sectorSign
    (eps : Z2FourCharge)
    (i : Fin 4) : ℝ :=
  boolSign (eps i)

/-- Flipping the `i`th bit negates the corresponding sign. -/
theorem sectorSign_flip_self
    (i : Fin 4)
    (eps : Z2FourCharge) :
    sectorSign (flipCharge i eps) i = -sectorSign eps i := by
  cases h : eps i <;> simp [sectorSign, boolSign, flipCharge, h]

/-- Flipping the `i`th bit leaves all other signs unchanged. -/
theorem sectorSign_flip_of_ne
    {i j : Fin 4}
    (hij : j ≠ i)
    (eps : Z2FourCharge) :
    sectorSign (flipCharge i eps) j = sectorSign eps j := by
  simp [sectorSign, flipCharge_of_ne hij eps]

/-- The `i`th Cartan half-projector factor. -/
def cartanProjectorFactor
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (C : SplitClifford4Cartan Op)
    (eps : Z2FourCharge)
    (i : Fin 4) : Op :=
  (1 / 2 : ℝ) • ((1 : Op) + (sectorSign eps i) • C.H i)

/--
The Cartan sector projector shape

`∏ᵢ (1 / 2) • (1 + epsᵢ Hᵢ)`.

This is the algebraic expression.  Idempotence/orthogonality
requires the usual commuting projector hypotheses supplied by concrete models.
-/
def cartanProjector
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (C : SplitClifford4Cartan Op)
    (eps : Z2FourCharge) : Op :=
  cartanProjectorFactor C eps 0 *
    cartanProjectorFactor C eps 1 *
      cartanProjectorFactor C eps 2 *
        cartanProjectorFactor C eps 3

/-- Total chirality of a four-atom Cartan system: `Gamma = H₁ H₂ H₃ H₄`. -/
def totalChirality
    {Op : Type*} [Ring Op]
    (C : SplitClifford4Cartan Op) : Op :=
  C.H 0 * C.H 1 * C.H 2 * C.H 3

/-- Left half-spinor projector shape `P₊ = (1 + Gamma) / 2`. -/
def positiveChiralityProjector
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (C : SplitClifford4Cartan Op) : Op :=
  (1 / 2 : ℝ) • ((1 : Op) + totalChirality C)

/-- Right half-spinor projector shape `P₋ = (1 - Gamma) / 2`. -/
def negativeChiralityProjector
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (C : SplitClifford4Cartan Op) : Op :=
  (1 / 2 : ℝ) • ((1 : Op) - totalChirality C)

/-! ## 4. Edge action on Cartan weight sectors -/

/--
A representation-level action of a four-atom Clifford Cartan system.

The edge-flip theorem needs more than multiplication in `Op`: it needs an
action on states, compatibility with multiplication and signs, and the fact
that `e_i` commutes with `H_j` for `j ≠ i` while anticommuting with `H_i`.
-/
structure CliffordEdgeAction
    {Op V : Type*} [Ring Op] [AddCommGroup V] [Module ℝ V]
    (A : SplitClifford4Cartan Op) where
  /-- Action of represented operators on states. -/
  act : Op → V → V

  /-- Multiplication in `Op` composes the represented action. -/
  act_mul :
    ∀ (a b : Op) (v : V), act (a * b) v = act a (act b v)

  /-- Negation in `Op` negates the represented action. -/
  act_neg :
    ∀ (a : Op) (v : V), act (-a) v = -act a v

  /-- The represented action is real-linear in the state argument. -/
  act_smul :
    ∀ (a : Op) (r : ℝ) (v : V), act a (r • v) = r • act a v

  /-- `e_i` commutes with `H_j` for the other Cartan axes. -/
  H_e_comm_of_ne :
    ∀ i j : Fin 4, j ≠ i → A.H j * A.e i = A.e i * A.H j

  /-- `e_i` anticommutes with its own Cartan axis. -/
  H_e_anticomm_self :
    ∀ i : Fin 4, A.H i * A.e i = -(A.e i * A.H i)

namespace CliffordEdgeAction

variable
    {Op V : Type*} [Ring Op] [AddCommGroup V] [Module ℝ V]
    {A : SplitClifford4Cartan Op}
    (R : CliffordEdgeAction (V := V) A)

/-- A state is a simultaneous Cartan weight vector with charge `eps`. -/
def IsWeightVector
    (v : V)
    (eps : Z2FourCharge) : Prop :=
  ∀ i : Fin 4, R.act (A.H i) v = sectorSign eps i • v

/--
Acting by the edge generator `e_i` flips exactly the `i`th Cartan bit.

This is the formal tesseract-edge statement:
`e_i` anticommutes with `H_i` and commutes with the other three `H_j`.
-/
theorem edge_flip_weight
    {v : V}
    {eps : Z2FourCharge}
    (hv : R.IsWeightVector v eps)
    (i : Fin 4) :
    R.IsWeightVector (R.act (A.e i) v) (flipCharge i eps) := by
  intro j
  by_cases hji : j = i
  · subst j
    calc
      R.act (A.H i) (R.act (A.e i) v)
          = R.act (A.H i * A.e i) v := by
              rw [R.act_mul]
      _ = R.act (-(A.e i * A.H i)) v := by
              rw [R.H_e_anticomm_self]
      _ = -R.act (A.e i * A.H i) v := by
              rw [R.act_neg]
      _ = -R.act (A.e i) (R.act (A.H i) v) := by
              rw [R.act_mul]
      _ = -R.act (A.e i) (sectorSign eps i • v) := by
              rw [hv i]
      _ = -(sectorSign eps i • R.act (A.e i) v) := by
              rw [R.act_smul]
      _ = sectorSign (flipCharge i eps) i • R.act (A.e i) v := by
              rw [sectorSign_flip_self]
              simp
  · calc
      R.act (A.H j) (R.act (A.e i) v)
          = R.act (A.H j * A.e i) v := by
              rw [R.act_mul]
      _ = R.act (A.e i * A.H j) v := by
              rw [R.H_e_comm_of_ne i j hji]
      _ = R.act (A.e i) (R.act (A.H j) v) := by
              rw [R.act_mul]
      _ = R.act (A.e i) (sectorSign eps j • v) := by
              rw [hv j]
      _ = sectorSign eps j • R.act (A.e i) v := by
              rw [R.act_smul]
      _ = sectorSign (flipCharge i eps) j • R.act (A.e i) v := by
              rw [sectorSign_flip_of_ne hji]

end CliffordEdgeAction

/-! ## 5. Local signs versus global anomalies -/

/--
The cyclic sixteenfold anomaly/stacking target.

This is not definitionally equivalent to `Z2FourCharge`.
-/
abbrev Z16Charge : Type :=
  ZMod 16

/--
Interface relating local Clifford signs to a global anomaly or stacking
index.

The fields are proof-carrying on purpose: `Z2^4` gives four independent local
binary addresses, while `Z16` is a cyclic global stacking law.
-/
structure LocalToGlobalAnomalyInterface where
  /-- Local admissible four-bit sectors. -/
  localCharge : Z2FourCharge → Prop

  /-- Global integer index or winding predicate. -/
  globalIndex : ℤ → Prop

/--
A global anomaly/topological class sitting above local Clifford signs.

This is the formal boundary between the `Z2^4` Cartan ledger and a genuine
global obstruction such as an index, residue, cyclic cocycle, eta invariant, or
interacting DIII stacking class.
-/
structure GlobalAnomalyClass where
  /-- Local Clifford sector predicate. -/
  localSector : Z2FourCharge → Prop

  /-- Global cyclic stacking/index value. -/
  cyclicIndex : ZMod 16

  /-- Integer lift or free-theory winding/index, when supplied by the model. -/
  integerLift : ℤ

  /-- The cyclic class is the mod-16 reduction of the integer lift. -/
  reduction_eq :
    cyclicIndex = (integerLift : ZMod 16)


namespace GlobalAnomalyClass

variable (G : GlobalAnomalyClass)

/-- Forget a global anomaly class to the local-to-global compatibility interface. -/
def toLocalToGlobalAnomalyInterface : LocalToGlobalAnomalyInterface where
  localCharge := G.localSector
  globalIndex := fun n => (n : ZMod 16) = G.cyclicIndex

end GlobalAnomalyClass

/--
A DIII index calibration turns a local charge address type into a cyclic
`ZMod 16` stacking index.

This is an interface, not a theorem: a four-bit charge space and `Z16` both have
sixteen elements in the motivating case, but they do not have the same group
law.
-/
structure DIIIIndexCalibration
    (Charge : Type*) where
  /-- Encoding of local sectors into a cyclic DIII stacking class. -/
  dIIIIndex : Charge → ZMod 16

/--
A DIII interaction calibration for the four-bit `Cl(1,1)^⊗4` address space.
-/
structure DIIIInteractionCalibration where
  /-- Encoding of local four-bit sectors into a cyclic DIII stacking class. -/
  encode : Charge4 → ZMod 16

namespace DIIIInteractionCalibration

variable (C : DIIIInteractionCalibration)

/-- Repackage the four-bit interaction calibration as the generic index calibration. -/
def toDIIIIndexCalibration : DIIIIndexCalibration Charge4 where
  dIIIIndex := C.encode

end DIIIInteractionCalibration

end InfoGeometry.OperatorAlgebra.CliffordAtomsZ2n
