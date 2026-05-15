import Mathlib
import InfoGeometry.Arithmetic.PrimitiveSetsAbove

/-!
# InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter

Finite split-Majorana primon Witten character.

This file is a finite-cutoff owner surface for the primon Majorana character:

* local Euler/Witten factor `1 - exp (-s log p)`;
* spinor square-root amplitude `exp (-(s/2) log p)`;
* finite Witten character as a finite product;
* split-Majorana CAR and OPE sockets;
* signed `2 × 2` Pfaffian block readout;
* two-state Hamiltonian Witten trace.

It does not assert RH, infinite Euler product convergence, zeta analytic
continuation, CFT construction, bosonization, Kac--Moody/Weyl denominator
theorems, Fredholm Pfaffians, or spectral triples.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter

open scoped BigOperators

/-! ## 1. Local primon Euler/Witten factor -/

/-- Primon energy `log p`. -/
def primonEnergy (p : ℕ) : ℝ :=
  Real.log (p : ℝ)

/-- Spinor square-root amplitude `exp (-(s/2) log p)`. -/
def primonSpinAmplitude (s : ℝ) (p : ℕ) : ℝ :=
  Real.exp (-(s / 2) * primonEnergy p)

/-- Local graded Euler/Witten factor `1 - exp (-s log p)`. -/
def localWittenFactor (s : ℝ) (p : ℕ) : ℝ :=
  1 - Real.exp (-s * primonEnergy p)

/-- The square of the spinor amplitude is the scalar Mellin/Euler weight. -/
theorem primonSpinAmplitude_sq
    (s : ℝ) (p : ℕ) :
    primonSpinAmplitude s p ^ 2 = Real.exp (-s * primonEnergy p) := by
  unfold primonSpinAmplitude
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- The local Witten factor is `1 - r_p(s)^2`. -/
theorem localWittenFactor_eq_one_sub_spinAmplitude_sq
    (s : ℝ) (p : ℕ) :
    localWittenFactor s p = 1 - primonSpinAmplitude s p ^ 2 := by
  rw [localWittenFactor, primonSpinAmplitude_sq]

/-- For `1 < p`, the local factor is `1 - primitiveMellinKernel p s`. -/
theorem localWittenFactor_eq_one_sub_primitiveMellinKernel
    {p : ℕ} (hp : 1 < p) (s : ℝ) :
    localWittenFactor s p = 1 - primitiveMellinKernel p s := by
  rw [localWittenFactor, primitiveMellinKernel, if_pos hp, primonEnergy]

/-! ## 2. Finite Witten character -/

/-- Finite cutoff Witten character `∏_{p∈P} (1 - exp (-s log p))`. -/
def finiteWittenCharacter (P : Finset ℕ) (s : ℝ) : ℝ :=
  P.prod (localWittenFactor s)

@[simp]
theorem finiteWittenCharacter_empty (s : ℝ) :
    finiteWittenCharacter ∅ s = 1 := by
  simp [finiteWittenCharacter]

theorem finiteWittenCharacter_insert
    {P : Finset ℕ} {p : ℕ} (hp : p ∉ P) (s : ℝ) :
    finiteWittenCharacter (insert p P) s =
      localWittenFactor s p * finiteWittenCharacter P s := by
  simp [finiteWittenCharacter, hp]

/-- Finite prime cutoff `{p ≤ Λ | p prime}`. -/
def primeCutoff (Λ : ℕ) : Finset ℕ :=
  (Finset.range (Λ + 1)).filter Nat.Prime

theorem mem_primeCutoff_iff {Λ p : ℕ} :
    p ∈ primeCutoff Λ ↔ p ≤ Λ ∧ Nat.Prime p := by
  simp [primeCutoff]

/-! ## 3. Local real spinor pairing -/

/-- Local two-component real spinor coefficients in the occupation basis. -/
structure LocalPrimonSpinor where
  emptyCoeff : ℝ
  occupiedCoeff : ℝ

/-- `ω_+ = |0⟩ + r_p |1⟩`. -/
def localSpinorPlus (s : ℝ) (p : ℕ) : LocalPrimonSpinor where
  emptyCoeff := 1
  occupiedCoeff := primonSpinAmplitude s p

/-- `ω_- = |0⟩ - r_p |1⟩`. -/
def localSpinorMinus (s : ℝ) (p : ℕ) : LocalPrimonSpinor where
  emptyCoeff := 1
  occupiedCoeff := -primonSpinAmplitude s p

/-- Euclidean coefficient pairing of two local occupation spinors. -/
def localSpinorPairing (u v : LocalPrimonSpinor) : ℝ :=
  u.emptyCoeff * v.emptyCoeff + u.occupiedCoeff * v.occupiedCoeff

/-- `⟨ω_+,ω_-⟩ = 1 - r_p(s)^2`. -/
theorem localSpinorPairing_plus_minus
    (s : ℝ) (p : ℕ) :
    localSpinorPairing (localSpinorPlus s p) (localSpinorMinus s p) =
      localWittenFactor s p := by
  simp [localSpinorPairing, localSpinorPlus, localSpinorMinus,
    localWittenFactor_eq_one_sub_spinAmplitude_sq]
  ring

/-- Finite product of local spinor pairings. -/
def finiteSpinorPairing (P : Finset ℕ) (s : ℝ) : ℝ :=
  P.prod (fun p => localSpinorPairing (localSpinorPlus s p) (localSpinorMinus s p))

/-- The finite spinor-pairing product equals the finite Witten character. -/
theorem finiteSpinorPairing_eq_wittenCharacter
    (P : Finset ℕ) (s : ℝ) :
    finiteSpinorPairing P s = finiteWittenCharacter P s := by
  unfold finiteSpinorPairing finiteWittenCharacter
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact localSpinorPairing_plus_minus s p

/-! ## 4. Split-Majorana CAR and OPE sockets -/

/-- Anticommutator in a ring. -/
def anticommutator {Op : Type*} [Ring Op] (x y : Op) : Op :=
  x * y + y * x

/-- Law-bearing split-Majorana CAR socket. -/
structure SplitMajoranaCAR
    (Prime Op : Type*) [DecidableEq Prime] [Ring Op] where
  c : Prime → Op
  d : Prime → Op
  c_c :
    ∀ p q, anticommutator (c p) (c q) =
      if p = q then (2 : Op) else 0
  d_d :
    ∀ p q, anticommutator (d p) (d q) =
      if p = q then -(2 : Op) else 0
  c_d :
    ∀ p q, anticommutator (c p) (d q) = 0

namespace SplitMajoranaCAR

variable {Prime Op : Type*} [DecidableEq Prime] [Ring Op]
variable (C : SplitMajoranaCAR Prime Op)

theorem c_c_valid (p q : Prime) :
    anticommutator (C.c p) (C.c q) =
      if p = q then (2 : Op) else 0 :=
  C.c_c p q

theorem d_d_valid (p q : Prime) :
    anticommutator (C.d p) (C.d q) =
      if p = q then -(2 : Op) else 0 :=
  C.d_d p q

theorem c_d_valid (p q : Prime) :
    anticommutator (C.c p) (C.d q) = 0 :=
  C.c_d p q

end SplitMajoranaCAR

/-- Witness-gated split-Majorana OPE datum. -/
structure SplitMajoranaOPEDatum
    (Prime Field Singular : Type*) [DecidableEq Prime] [Zero Singular] [One Singular]
    [Neg Singular] where
  cField : Prime → Field
  dField : Prime → Field
  singular : Field → Field → Singular
  c_c_singular :
    ∀ p q, singular (cField p) (cField q) =
      if p = q then 1 else 0
  d_d_singular :
    ∀ p q, singular (dField p) (dField q) =
      if p = q then -1 else 0
  c_d_regular :
    ∀ p q, singular (cField p) (dField q) = 0

/-! ## 5. Signed Pfaffian block lane -/

/-- Signed `2 × 2` Majorana skew block with upper-right local Witten factor. -/
def majoranaPfaffianBlock
    (s : ℝ) (p : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(0 : ℝ), localWittenFactor s p; -localWittenFactor s p, 0]

/-- Signed Pfaffian readout for a `2 × 2` skew block. -/
def pfaffianTwoByTwo (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  A 0 1

/-- The signed Pfaffian of the local Majorana block is the local Witten factor. -/
theorem pfaffian_majoranaPfaffianBlock
    (s : ℝ) (p : ℕ) :
    pfaffianTwoByTwo (majoranaPfaffianBlock s p) =
      localWittenFactor s p := by
  simp [pfaffianTwoByTwo, majoranaPfaffianBlock]

/-- The determinant of the local skew block is the square of the local factor. -/
theorem det_majoranaPfaffianBlock
    (s : ℝ) (p : ℕ) :
    Matrix.det (majoranaPfaffianBlock s p) =
      (localWittenFactor s p) ^ 2 := by
  simp [majoranaPfaffianBlock, Matrix.det_fin_two]
  ring

/-- Finite product of signed local Pfaffian blocks. -/
def finiteMajoranaPfaffian (P : Finset ℕ) (s : ℝ) : ℝ :=
  P.prod (fun p => pfaffianTwoByTwo (majoranaPfaffianBlock s p))

/-- The finite signed Pfaffian product equals the finite Witten character. -/
theorem finiteMajoranaPfaffian_eq_wittenCharacter
    (P : Finset ℕ) (s : ℝ) :
    finiteMajoranaPfaffian P s = finiteWittenCharacter P s := by
  unfold finiteMajoranaPfaffian finiteWittenCharacter
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact pfaffian_majoranaPfaffianBlock s p

/-! ## 6. Two-state Hamiltonian trace -/

/-- Two local occupancy states for one primon mode. -/
inductive Occupancy where
  | empty
  | occupied
deriving DecidableEq, Fintype, Repr

namespace Occupancy

/-- Local occupation eigenvalue. -/
def number : Occupancy → ℕ
  | empty => 0
  | occupied => 1

/-- Local parity eigenvalue `1 - 2N`. -/
def parity : Occupancy → ℝ
  | empty => 1
  | occupied => -1

@[simp] theorem number_empty : number empty = 0 := rfl
@[simp] theorem number_occupied : number occupied = 1 := rfl
@[simp] theorem parity_empty : parity empty = 1 := rfl
@[simp] theorem parity_occupied : parity occupied = -1 := rfl

end Occupancy

/-- Occupancy eigenvalue of `N`. -/
def localOccupancyEigenvalue (o : Occupancy) : ℕ :=
  Occupancy.number o

/-- Parity eigenvalue of `1 - 2N`. -/
def localParityEigenvalue (o : Occupancy) : ℝ :=
  Occupancy.parity o

/-- Local Hamiltonian eigenvalue `(log p) N`. -/
def localHamiltonianEigenvalue (p : ℕ) (o : Occupancy) : ℝ :=
  primonEnergy p * (localOccupancyEigenvalue o : ℝ)

/-- Local two-state Witten trace. -/
def localTwoStateWittenTrace (p : ℕ) (s : ℝ) : ℝ :=
  localParityEigenvalue Occupancy.empty *
      Real.exp (-s * localHamiltonianEigenvalue p Occupancy.empty)
    + localParityEigenvalue Occupancy.occupied *
      Real.exp (-s * localHamiltonianEigenvalue p Occupancy.occupied)

/-- Local two-state Witten trace is the local Witten factor. -/
theorem localTwoStateWittenTrace_eq_localWittenFactor
    (p : ℕ) (s : ℝ) :
    localTwoStateWittenTrace p s = localWittenFactor s p := by
  simp [localTwoStateWittenTrace, localParityEigenvalue, localHamiltonianEigenvalue,
    localOccupancyEigenvalue, localWittenFactor]
  ring

/-- Finite product of local two-state Witten traces. -/
def finiteTwoStateWittenTrace (P : Finset ℕ) (s : ℝ) : ℝ :=
  P.prod (fun p => localTwoStateWittenTrace p s)

/-- The finite two-state trace product equals the finite Witten character. -/
theorem finiteTwoStateWittenTrace_eq_wittenCharacter
    (P : Finset ℕ) (s : ℝ) :
    finiteTwoStateWittenTrace P s = finiteWittenCharacter P s := by
  unfold finiteTwoStateWittenTrace finiteWittenCharacter
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact localTwoStateWittenTrace_eq_localWittenFactor p s

/-! ## 7. Owner target -/

/-- Owner target for the finite primon Majorana Witten character surface. -/
def PrimonMajoranaWittenCharacterOwnerTarget : Prop :=
  ∀ (P : Finset ℕ) (s : ℝ),
    finiteTwoStateWittenTrace P s = finiteWittenCharacter P s ∧
    finiteSpinorPairing P s = finiteWittenCharacter P s ∧
    finiteMajoranaPfaffian P s = finiteWittenCharacter P s

/-- The finite two-state trace, spinor pairing, and signed Pfaffian products agree. -/
theorem primonMajoranaWittenCharacterOwnerTarget :
    PrimonMajoranaWittenCharacterOwnerTarget := by
  intro P s
  exact ⟨finiteTwoStateWittenTrace_eq_wittenCharacter P s,
    finiteSpinorPairing_eq_wittenCharacter P s,
    finiteMajoranaPfaffian_eq_wittenCharacter P s⟩

end InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter
