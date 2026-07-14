import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.CuntzTensorQuotient

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
open InfoGeometry.Algebra.CuntzTensorQuotient

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
  CylinderProjectionHolds : Prop
  cylinder_projection_witness : CylinderProjectionHolds

namespace BitProjectionPacket

/-- Debt surface for proving that the projection represents the Cantor cylinder/event. -/
@[rep_depth transport]
theorem cylinder_projection_law (_P : BitProjectionPacket) :
    _P.CylinderProjectionHolds :=
  _P.cylinder_projection_witness

/-- The binary address carried by the projection packet is explicit. -/
theorem word_readout (P : BitProjectionPacket) :
    P.word = P.word :=
  rfl

/-- The ambient algebra carried by the projection packet is explicit. -/
theorem projection_algebra_readout (P : BitProjectionPacket) :
    P.ProjectionAlgebra = P.ProjectionAlgebra :=
  rfl

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
  CarCliffordHolds : Prop
  car_clifford_witness : CarCliffordHolds

namespace BitFockPacket

/-- Debt surface for proving the selected creation/annihilation CAR/Clifford law. -/
@[rep_depth operator]
theorem car_clifford_law (_F : BitFockPacket) :
    _F.CarCliffordHolds :=
  _F.car_clifford_witness

/-- The basis readout on the finite Fock packet is explicit. -/
theorem basisEquiv_readout (F : BitFockPacket) :
    F.basisEquiv = F.basisEquiv :=
  rfl

/-- The operator algebra readout on the finite Fock packet is explicit. -/
theorem operatorAlgebra_readout (F : BitFockPacket) :
    F.OperatorAlgebra = F.OperatorAlgebra :=
  rfl

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

/-- Every single bit flip is a hypercube edge. -/
theorem hypercubeAdjacent_flipBit {n : ℕ} (i : Fin n) (w : BinaryWord n) :
    HypercubeAdjacent w (flipBit i w) := by
  exact ⟨i, rfl⟩

/-- Hypercube adjacency is symmetric because bit flips are involutive. -/
theorem hypercubeAdjacent_symm {n : ℕ} {w v : BinaryWord n} :
    HypercubeAdjacent w v → HypercubeAdjacent v w := by
  rintro ⟨i, rfl⟩
  exact ⟨i, (flipBit_involutive i w).symm⟩

/-- Hypercube adjacency can be read in either direction. -/
theorem hypercubeAdjacent_comm {n : ℕ} {w v : BinaryWord n} :
    HypercubeAdjacent w v ↔ HypercubeAdjacent v w := by
  exact ⟨hypercubeAdjacent_symm, hypercubeAdjacent_symm⟩

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
  FilteredReadoutHolds : Prop
  filtered_readout_witness : FilteredReadoutHolds

  drazinHodgeFilter : Type
  kmsWeylWeight : Type
  invariantReadout : Type

namespace BitToItStabilizationPacket

variable (S : BitToItStabilizationPacket)

/-- The random walk is supported on the Clifford bit-transition graph. -/
@[rep_depth transport]
theorem clifford_walk :
    IsCliffordBitWalk S.walk :=
  S.cliffordWalkWitness

/-- Debt surface for proving that the final readout is evaluated after filtering. -/
@[rep_depth operator]
theorem filtered_readout_law (S : BitToItStabilizationPacket) :
    S.FilteredReadoutHolds :=
  S.filtered_readout_witness

/-- The walk component of the stabilization packet is explicit. -/
theorem walk_readout (S : BitToItStabilizationPacket) :
    S.walk = S.walk :=
  rfl

/-- The Drazin/Hodge filter component is explicit. -/
theorem drazinHodgeFilter_readout (S : BitToItStabilizationPacket) :
    S.drazinHodgeFilter = S.drazinHodgeFilter :=
  rfl

/-- The KMS/Weyl weight component is explicit. -/
theorem kmsWeylWeight_readout (S : BitToItStabilizationPacket) :
    S.kmsWeylWeight = S.kmsWeylWeight :=
  rfl

/-- The invariant readout component is explicit. -/
theorem invariantReadout_readout (S : BitToItStabilizationPacket) :
    S.invariantReadout = S.invariantReadout :=
  rfl

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
  SameAddressHolds : Prop
  ItInvariantHolds : Prop
  same_address_witness : SameAddressHolds
  it_invariant_witness : ItInvariantHolds

namespace ItFromBitPacket

variable (P : ItFromBitPacket)

/-- Debt surface for proving that all layers use the same binary address data. -/
@[rep_depth transport]
theorem same_address (P : ItFromBitPacket) :
    P.SameAddressHolds :=
  P.same_address_witness

/-- Debt surface for proving that the final object is an invariant of the stabilized bit process. -/
@[rep_depth operator]
theorem it_invariant (P : ItFromBitPacket) :
    P.ItInvariantHolds :=
  P.it_invariant_witness

/-- The finite word readout is explicit. -/
theorem word_readout (P : ItFromBitPacket) :
    P.word = P.word :=
  rfl

/-- The Cantor cylinder readout is explicit. -/
theorem cantorCylinder_readout (P : ItFromBitPacket) :
    P.cantorCylinder = P.cantorCylinder :=
  rfl

/-- The projection readout is explicit. -/
theorem projection_readout (P : ItFromBitPacket) :
    P.projection = P.projection :=
  rfl

/-- The finite Fock readout is explicit. -/
theorem fock_readout (P : ItFromBitPacket) :
    P.fock = P.fock :=
  rfl

/-- The random-walk readout is explicit. -/
theorem walk_readout (P : ItFromBitPacket) :
    P.walk = P.walk :=
  rfl

/-- The stabilization packet readout is explicit. -/
theorem stabilization_readout (P : ItFromBitPacket) :
    P.stabilization = P.stabilization :=
  rfl

end ItFromBitPacket

/-! ## 4. Finite Cuntz quotient realization -/

/-- Finite generator alphabet for the tensor-algebra presentation. -/
abbrev BitGeneratorAlphabet (n : ℕ) : Type :=
  CuntzGen n

/-- Free noncommutative word algebra on finite Cuntz generators. -/
abbrev BitWordAlgebra (n : ℕ) : Type :=
  CuntzTensor n

/-- Observable algebra obtained by imposing the finite Cuntz relations. -/
abbrev ItObservableAlgebra (n : ℕ) : Type :=
  CuntzAlg n

/-- Quotient map from formal bit words to admissible Cuntz observables. -/
def bitToItQuotient (n : ℕ) :
    BitWordAlgebra n →ₐ[ℂ] ItObservableAlgebra n :=
  cuntzMk n

@[simp] theorem bitToItQuotient_S (n : ℕ) (i : Fin n) :
    bitToItQuotient n (S n i) = cuntzS n i := by
  rfl

@[simp] theorem bitToItQuotient_Sdag (n : ℕ) (i : Fin n) :
    bitToItQuotient n (Sdag n i) = cuntzSdag n i := by
  rfl

/-- Formal dagger/star feedback descends through the Cuntz quotient. -/
theorem bitToIt_star_feedback (n : ℕ) (x : BitWordAlgebra n) :
    star (bitToItQuotient n x) = bitToItQuotient n (star x) := by
  simpa [bitToItQuotient, BitWordAlgebra, ItObservableAlgebra] using
    (star_cuntzMk n x)

/-- The quotient readout satisfies the finite Cuntz relations. -/
theorem bitToIt_cuntz_relations (n : ℕ) :
    (∀ i j : Fin n,
      bitToItQuotient n (Sdag n i * S n j) =
        if i = j then (1 : ItObservableAlgebra n) else 0) ∧
    (∑ i : Fin n, bitToItQuotient n (S n i * Sdag n i)) =
      (1 : ItObservableAlgebra n) := by
  constructor
  · intro i j
    simpa [bitToItQuotient, ItObservableAlgebra, cuntzS, cuntzSdag, map_mul] using
      (cuntz_orthogonality n i j)
  · simpa [bitToItQuotient, ItObservableAlgebra, cuntzS, cuntzSdag, map_mul] using
      (cuntz_ranges_sum_one n)

/--
Finite algebraic "it from bit" target:

* tensor words are read into the Cuntz quotient;
* star feedback is preserved by the quotient map;
* the Cuntz orthogonality and partition laws hold in the readout algebra.
-/
def CuntzItFromBitFiniteTarget (n : ℕ) : Prop :=
  (∀ x : BitWordAlgebra n,
    star (bitToItQuotient n x) = bitToItQuotient n (star x)) ∧
  (∀ i j : Fin n,
    bitToItQuotient n (Sdag n i * S n j) =
      if i = j then (1 : ItObservableAlgebra n) else 0) ∧
  (∑ i : Fin n, bitToItQuotient n (S n i * Sdag n i)) =
    (1 : ItObservableAlgebra n)

/-- Constructor for the finite Cuntz quotient realization. -/
theorem constructCuntzItFromBitFiniteTarget (n : ℕ) :
    CuntzItFromBitFiniteTarget n := by
  exact ⟨bitToIt_star_feedback n,
    (bitToIt_cuntz_relations n).1,
    (bitToIt_cuntz_relations n).2⟩

/-! ## 5. Explicit induction and colimit hypotheses -/

/--
Explicit staged induction data for passing from finite Cuntz readouts to a
directed system.  No existence of such a system is asserted here.
-/
structure ItFromBitInductionSystem where
  Stage : ℕ → Type
  starStage : ∀ n, Stage n → Stage n
  bitReadout : ∀ n, BitWordAlgebra n → Stage n
  step : ∀ n, Stage n → Stage (n + 1)
  bitReadout_star :
    ∀ n (x : BitWordAlgebra n),
      starStage n (bitReadout n x) = bitReadout n (star x)
  step_star :
    ∀ n (x : Stage n),
      starStage (n + 1) (step n x) = step n (starStage n x)

namespace ItFromBitInductionSystem

variable (I : ItFromBitInductionSystem)

/-- The finite readout commutes with the staged star operation. -/
theorem readout_preserves_star (n : ℕ) (x : BitWordAlgebra n) :
    I.starStage n (I.bitReadout n x) = I.bitReadout n (star x) :=
  I.bitReadout_star n x

/-- One induction step commutes with star. -/
theorem step_preserves_star (n : ℕ) (x : I.Stage n) :
    I.starStage (n + 1) (I.step n x) = I.step n (I.starStage n x) :=
  I.step_star n x

/-- Two induction steps commute with star by iterating the one-step law. -/
theorem two_steps_preserve_star (n : ℕ) (x : I.Stage n) :
    I.starStage (n + 1 + 1) (I.step (n + 1) (I.step n x)) =
      I.step (n + 1) (I.step n (I.starStage n x)) := by
  rw [I.step_star (n + 1), I.step_star n]

end ItFromBitInductionSystem

/--
Explicit colimit socket for an already constructed staged system.
The premises are the object, structure maps, and transition compatibility.
-/
structure ItFromBitColimitHypotheses where
  system : ItFromBitInductionSystem
  Colimit : Type
  intoColimit : ∀ n, system.Stage n → Colimit
  compat :
    ∀ n (x : system.Stage n),
      intoColimit (n + 1) (system.step n x) = intoColimit n x

namespace ItFromBitColimitHypotheses

variable (C : ItFromBitColimitHypotheses)

/-- The supplied cocone maps are compatible with the induction transition. -/
theorem transition_compatible (n : ℕ) (x : C.system.Stage n) :
    C.intoColimit (n + 1) (C.system.step n x) = C.intoColimit n x :=
  C.compat n x

end ItFromBitColimitHypotheses

/-- Kernel-checked finite Cuntz pipeline, for every finite stage. -/
def ItFromBitCuntzPipelineTarget : Prop :=
  ∀ n : ℕ, CuntzItFromBitFiniteTarget n

/-- Constructor for the finite-stage Cuntz pipeline. -/
theorem constructItFromBitCuntzPipelineTarget :
    ItFromBitCuntzPipelineTarget := by
  intro n
  exact constructCuntzItFromBitFiniteTarget n

/-! ## 6. Owner target -/

/-- Owner target for the It-from-Bit doctrine. -/
def ItFromBitTarget : Prop :=
  Nonempty ItFromBitPacket

/-- Constructor from explicit It-from-Bit data. -/
theorem constructItFromBitTarget
    (P : ItFromBitPacket) :
    ItFromBitTarget := by
  exact ⟨P⟩

end InfoGeometry.Canonical.ItFromBit
