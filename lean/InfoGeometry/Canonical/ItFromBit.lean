import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.ItFromBit

Theorem-safe "it from bit" substrate.

A bit is not automatically a physical object.  A physical "it" is an invariant
readout of binary data after:

`bit -> word -> Cantor cylinder -> projection -> Clifford/CAR transition graph
 -> entropy/random-walk readout -> Drazin/KMS/Fierz stabilization`.

This module records that doctrine as proof-carrying packets.  It does not claim
that every binary process has a physical readout; the final invariant is present
only when the required stabilization certificates are supplied.
-/

noncomputable section

namespace InfoGeometry.Canonical.ItFromBit

open scoped BigOperators

/-! ## 1. Binary substrate -/

/-- A bit is a Boolean datum. -/
abbrev Bit : Type := Bool

/-- A finite binary word of length `n`. -/
abbrev BinaryWord (n : ℕ) : Type :=
  Fin n → Bit

/-- An infinite binary stream, used as the symbolic Cantor boundary model. -/
abbrev BinaryStream : Type :=
  ℕ → Bit

/--
A finite Cantor cylinder represented by a binary word.

The word specifies all infinite bitstreams with that prefix.
-/
@[rep_depth transport]
structure CantorCylinder (n : ℕ) where
  word : BinaryWord n

/--
A Boolean event projection associated to a finite binary address.

The target algebra is deliberately abstract: it may be a Boolean algebra,
projection lattice, C*-algebra, or matrix algebra in downstream files.
-/
@[rep_depth transport]
structure BitProjectionPacket where
  n : ℕ
  word : BinaryWord n
  ProjectionAlgebra : Type
  projection : ProjectionAlgebra

  cylinderProjectionLaw : Prop
  cylinderProjectionCertificate : cylinderProjectionLaw

namespace BitProjectionPacket

variable (P : BitProjectionPacket)

/-- The projection represents the declared Cantor cylinder/event. -/
@[rep_depth transport]
theorem cylinder_projection_law :
    P.cylinderProjectionLaw :=
  P.cylinderProjectionCertificate

end BitProjectionPacket

/-! ## 2. Clifford/Fock and random-walk graph layers -/

/--
Finite Clifford/Fock interpretation of a binary word.

A binary word is interpreted as an occupation vector.
-/
@[rep_depth operator]
structure BitFockPacket where
  n : ℕ

  Basis : Type
  basisEquiv : Basis ≃ BinaryWord n

  OperatorAlgebra : Type
  creation : Fin n → OperatorAlgebra
  annihilation : Fin n → OperatorAlgebra

  carCliffordLaw : Prop
  carCliffordCertificate : carCliffordLaw

namespace BitFockPacket

variable (F : BitFockPacket)

/-- The selected creation/annihilation data satisfy the declared CAR/Clifford law. -/
@[rep_depth operator]
theorem car_clifford_law :
    F.carCliffordLaw :=
  F.carCliffordCertificate

end BitFockPacket

/-- Flip the `i`-th bit of a binary word. -/
def flipBit {n : ℕ} (i : Fin n) (w : BinaryWord n) : BinaryWord n :=
  fun j => if j = i then !w j else w j

/-- Bit flip is involutive. -/
theorem flipBit_involutive {n : ℕ} (i : Fin n) (w : BinaryWord n) :
    flipBit i (flipBit i w) = w := by
  funext j
  by_cases h : j = i <;> simp [flipBit, h]

/--
Hypercube adjacency on finite binary words.

This is the finite Clifford transition graph.
-/
def HypercubeAdjacent {n : ℕ} (w v : BinaryWord n) : Prop :=
  ∃ i : Fin n, v = flipBit i w

/-- A finite random walk on binary words. -/
@[rep_depth transport]
structure BitRandomWalk (n : ℕ) where
  P : BinaryWord n → BinaryWord n → ℝ

  nonnegative :
    ∀ w v, 0 ≤ P w v

  row_sum :
    ∀ w,
      Finset.univ.sum (fun v : BinaryWord n => P w v) = 1

namespace BitRandomWalk

variable {n : ℕ}
variable (R : BitRandomWalk n)

/-- Transition nonnegativity readback. -/
@[rep_depth transport]
theorem transition_nonnegative (w v : BinaryWord n) :
    0 ≤ R.P w v :=
  R.nonnegative w v

/-- Row normalization readback. -/
@[rep_depth transport]
theorem transition_row_sum (w : BinaryWord n) :
    Finset.univ.sum (fun v : BinaryWord n => R.P w v) = 1 :=
  R.row_sum w

end BitRandomWalk

/--
The random walk is compatible with the Clifford hypercube if it only moves
along bit-flip edges or stays fixed.
-/
def IsCliffordBitWalk {n : ℕ} (R : BitRandomWalk n) : Prop :=
  ∀ w v, R.P w v ≠ 0 → (v = w ∨ HypercubeAdjacent w v)

/-- Local Shannon entropy of one transition row. -/
def localBitEntropy {n : ℕ} (R : BitRandomWalk n) (w : BinaryWord n) : ℝ :=
  - Finset.univ.sum
      (fun v : BinaryWord n =>
        let p := R.P w v
        if p = 0 then 0 else p * Real.log p)

/-- A stationary distribution for a bit random walk. -/
@[rep_depth transport]
structure StationaryBitDistribution {n : ℕ} (R : BitRandomWalk n) where
  π : BinaryWord n → ℝ

  nonnegative :
    ∀ w, 0 ≤ π w

  sum_eq_one :
    Finset.univ.sum (fun w : BinaryWord n => π w) = 1

  stationary :
    ∀ v,
      π v =
        Finset.univ.sum (fun w : BinaryWord n => π w * R.P w v)

/-- Entropy rate of a stationary finite bit random walk. -/
def bitEntropyRate {n : ℕ}
    (R : BitRandomWalk n)
    (S : StationaryBitDistribution R) : ℝ :=
  Finset.univ.sum
    (fun w : BinaryWord n => S.π w * localBitEntropy R w)

/-! ## 3. Stabilized readout -/

/--
Drazin/KMS/Fierz stabilization witness.

This is the final guard: a raw bit process becomes a physical object only after
stabilization and invariant readout are supplied.
-/
@[rep_depth operator]
structure BitToItStabilizationPacket where
  n : ℕ
  walk : BitRandomWalk n

  cliffordWalkWitness : IsCliffordBitWalk walk

  drazinHodgeFilter : Type
  kmsWeylWeight : Type
  invariantReadout : Type

  filteredReadoutLaw : Prop
  filteredReadoutCertificate : filteredReadoutLaw

namespace BitToItStabilizationPacket

variable (S : BitToItStabilizationPacket)

/-- The random walk is supported on the Clifford bit-transition graph. -/
@[rep_depth transport]
theorem clifford_walk :
    IsCliffordBitWalk S.walk :=
  S.cliffordWalkWitness

/-- The final readout is evaluated after filtering, not on raw bits. -/
@[rep_depth operator]
theorem filtered_readout_law :
    S.filteredReadoutLaw :=
  S.filteredReadoutCertificate

end BitToItStabilizationPacket

/--
Full "it from bit" packet.

It records the chain:

`bit -> word -> Cantor projection -> Clifford graph -> entropy walk
 -> Drazin/KMS/Fierz invariant`.
-/
@[rep_depth operator]
structure ItFromBitPacket where
  n : ℕ

  word : BinaryWord n
  cantorCylinder : CantorCylinder n
  projection : BitProjectionPacket
  fock : BitFockPacket
  walk : BitRandomWalk n
  stabilization : BitToItStabilizationPacket

  sameAddressLaw : Prop
  sameAddressCertificate : sameAddressLaw

  itInvariantLaw : Prop
  itInvariantCertificate : itInvariantLaw

namespace ItFromBitPacket

variable (P : ItFromBitPacket)

/-- All layers use the same binary address data. -/
@[rep_depth transport]
theorem same_address :
    P.sameAddressLaw :=
  P.sameAddressCertificate

/-- The final object is an invariant of the stabilized bit process. -/
@[rep_depth operator]
theorem it_invariant :
    P.itInvariantLaw :=
  P.itInvariantCertificate

end ItFromBitPacket

/-! ## 4. Owner target -/

/-- Owner target for the It-from-Bit doctrine. -/
def ItFromBitTarget : Prop :=
  Nonempty ItFromBitPacket

/-- Constructor from explicit It-from-Bit data. -/
theorem constructItFromBitTarget
    (P : ItFromBitPacket) :
    ItFromBitTarget := by
  exact ⟨P⟩

end InfoGeometry.Canonical.ItFromBit
