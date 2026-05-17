import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeWittenCharacter
import InfoGeometry.Arithmetic.PrimeExteriorRepresentation

/-!
# InfoGeometry.Arithmetic.PrimeBooleanCube

Canonical finite Boolean-cube owner for prime-register arithmetic.

This file consolidates the finite square-free / Cantor-cube surface:

* vertices are subsets of a certified prime register;
* the prime-axis move is the existing `majoranaFlip`;
* local parity is `1 - 2N_p`;
* global chirality is `(-1)^card`;
* Möbius readout is delegated to the existing finite Witten-index owner;
* finite Witten character is delegated to the existing finite Witten-character owner.

No infinite Euler product.
No analytic continuation.
No Hilbert--Polya/RH claim.
No Pfaffian placeholder.
-/

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.PrimeBooleanCube

open InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-! ## 1. Canonical finite prime Boolean cube -/

/-- A vertex of the finite prime Boolean/Cantor cube. -/
@[rep_depth thermo]
abbrev Vertex (P : PrimeRegister) :=
  {S : Finset ℕ // S ⊆ P.primes}

/-- Occupied prime set of a vertex. -/
@[rep_depth thermo]
def occupied {P : PrimeRegister} (v : Vertex P) : Finset ℕ :=
  v.val

/-- The represented square-free integer. -/
@[rep_depth thermo]
def representedNat {P : PrimeRegister} (v : Vertex P) : ℕ :=
  Finset.prod v.val fun p => p

/-- Fermion number of a vertex. -/
@[rep_depth thermo]
def fermionNumber {P : PrimeRegister} (v : Vertex P) : ℕ :=
  v.val.card

/-- Fermion parity of a vertex. -/
@[rep_depth thermo]
def fermionParity {P : PrimeRegister} (v : Vertex P) : ℤ :=
  (-1 : ℤ) ^ v.val.card


/-! ## 2. Prime-axis flip -/

/-- Existing Majorana bit flip preserves the ambient prime register. -/
@[rep_depth thermo]
theorem majoranaFlip_subset_of_subset
    {P : PrimeRegister}
    {p : ℕ}
    {S : Finset ℕ}
    (hp : p ∈ P.primes)
    (hS : S ⊆ P.primes) :
    majoranaFlip p S ⊆ P.primes := by
  intro q hq
  by_cases hqp : q = p
  · subst q
    exact hp
  · exact hS ((mem_majoranaFlip_of_ne hqp S).mp hq)

/-- Prime-axis graph move on the Boolean cube. -/
@[rep_depth thermo]
def flipVertex
    {P : PrimeRegister}
    (p : ℕ)
    (hp : p ∈ P.primes)
    (v : Vertex P) :
    Vertex P where
  val := majoranaFlip p v.val
  property := majoranaFlip_subset_of_subset hp v.property

/-- Prime-axis flip is involutive. -/
@[simp, rep_depth thermo]
theorem flipVertex_involutive
    {P : PrimeRegister}
    (p : ℕ)
    (hp : p ∈ P.primes)
    (v : Vertex P) :
    flipVertex p hp (flipVertex p hp v) = v := by
  apply Subtype.ext
  simp [flipVertex, majoranaFlip_involutive]

/-- The flipped mode is occupied iff it was previously unoccupied. -/
@[simp, rep_depth thermo]
theorem mem_flipVertex_self
    {P : PrimeRegister}
    (p : ℕ)
    (hp : p ∈ P.primes)
    (v : Vertex P) :
    p ∈ (flipVertex p hp v).val ↔ p ∉ v.val := by
  simp [flipVertex]

/-- Other modes are unaffected by the prime-axis flip. -/
@[simp, rep_depth thermo]
theorem mem_flipVertex_of_ne
    {P : PrimeRegister}
    {p q : ℕ}
    (hp : p ∈ P.primes)
    (hqp : q ≠ p)
    (v : Vertex P) :
    q ∈ (flipVertex p hp v).val ↔ q ∈ v.val := by
  simp [flipVertex, mem_majoranaFlip_of_ne hqp]

/-- Cardinality increases by one when the flipped mode was absent. -/
@[rep_depth thermo]
theorem card_flipVertex_of_not_mem
    {P : PrimeRegister}
    {p : ℕ}
    (hp : p ∈ P.primes)
    {v : Vertex P}
    (h : p ∉ v.val) :
    (flipVertex p hp v).val.card = v.val.card + 1 := by
  simpa [flipVertex] using card_majoranaFlip_of_not_mem (p := p) (S := v.val) h

/-- Cardinality decreases by one when the flipped mode was present. -/
@[rep_depth thermo]
theorem card_flipVertex_add_one_of_mem
    {P : PrimeRegister}
    {p : ℕ}
    (hp : p ∈ P.primes)
    {v : Vertex P}
    (h : p ∈ v.val) :
    (flipVertex p hp v).val.card + 1 = v.val.card := by
  simpa [flipVertex] using card_majoranaFlip_add_one_of_mem (p := p) (S := v.val) h


/-! ## 3. Occupation, local parity, global chirality -/

/-- Integer-valued occupation number. -/
@[rep_depth thermo]
def occupationInt (p : ℕ) (S : Finset ℕ) : ℤ :=
  if p ∈ S then 1 else 0

/-- Local Majorana/Möbius parity `1 - 2N_p`. -/
@[rep_depth thermo]
def localParity (p : ℕ) (S : Finset ℕ) : ℤ :=
  1 - (2 : ℤ) * occupationInt p S

@[simp, rep_depth thermo]
theorem occupationInt_eq_one_of_mem
    {p : ℕ} {S : Finset ℕ}
    (hp : p ∈ S) :
    occupationInt p S = 1 := by
  simp [occupationInt, hp]

@[simp, rep_depth thermo]
theorem occupationInt_eq_zero_of_not_mem
    {p : ℕ} {S : Finset ℕ}
    (hp : p ∉ S) :
    occupationInt p S = 0 := by
  simp [occupationInt, hp]

@[simp, rep_depth thermo]
theorem localParity_eq_neg_one_of_mem
    {p : ℕ} {S : Finset ℕ}
    (hp : p ∈ S) :
    localParity p S = -1 := by
  simp [localParity, occupationInt, hp]

@[simp, rep_depth thermo]
theorem localParity_eq_one_of_not_mem
    {p : ℕ} {S : Finset ℕ}
    (hp : p ∉ S) :
    localParity p S = 1 := by
  simp [localParity, occupationInt, hp]

/-- Global chirality over the ambient certified prime register. -/
@[rep_depth thermo]
def globalChirality (P : PrimeRegister) (S : Finset ℕ) : ℤ :=
  Finset.prod P.primes fun p => localParity p S

/--
Global chirality equals fermion parity for a subset of the prime register.
-/
@[rep_depth thermo]
theorem globalChirality_eq_neg_one_pow_card
    (P : PrimeRegister)
    {S : Finset ℕ}
    (hS : S ⊆ P.primes) :
    globalChirality P S = (-1 : ℤ) ^ S.card := by
  classical
  have hfilter : P.primes.filter (fun p => p ∈ S) = S := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hS hp, hp⟩

  calc
    globalChirality P S
        = Finset.prod P.primes fun p => if p ∈ S then (-1 : ℤ) else 1 := by
            unfold globalChirality
            refine Finset.prod_congr rfl ?_
            intro p hp
            by_cases h : p ∈ S <;> simp [localParity, occupationInt, h]
    _ = Finset.prod (P.primes.filter fun p => p ∈ S) fun _ => (-1 : ℤ) := by
            rw [Finset.prod_filter]
    _ = Finset.prod S fun _ => (-1 : ℤ) := by
            rw [hfilter]
    _ = (-1 : ℤ) ^ S.card := by
            simp

/-- Vertex form of the chirality theorem. -/
@[rep_depth thermo]
theorem globalChirality_vertex_eq_fermionParity
    (P : PrimeRegister)
    (v : Vertex P) :
    globalChirality P v.val = fermionParity v := by
  unfold fermionParity
  exact globalChirality_eq_neg_one_pow_card P v.property


/-! ## 4. Möbius readout -/

/--
Möbius value of the represented square-free integer equals global chirality.
-/
@[rep_depth thermo]
theorem mobius_representedNat_eq_globalChirality
    (P : PrimeRegister)
    (v : Vertex P) :
    ArithmeticFunction.moebius (representedNat v) =
      globalChirality P v.val := by
  have hprime : ∀ p ∈ v.val, Nat.Prime p := by
    intro p hp
    exact P.prime_mem p (v.property hp)

  have hmob :
      ArithmeticFunction.moebius (Finset.prod v.val fun p => p) =
        (-1 : ℤ) ^ v.val.card :=
    mobius_prime_product_eq_parity v.val hprime

  calc
    ArithmeticFunction.moebius (representedNat v)
        = ArithmeticFunction.moebius (Finset.prod v.val fun p => p) := by
            rfl
    _ = (-1 : ℤ) ^ v.val.card := hmob
    _ = globalChirality P v.val := by
            exact (globalChirality_eq_neg_one_pow_card P v.property).symm

/-- Möbius value equals the fermion parity of the vertex. -/
@[rep_depth thermo]
theorem mobius_representedNat_eq_fermionParity
    (P : PrimeRegister)
    (v : Vertex P) :
    ArithmeticFunction.moebius (representedNat v) =
      fermionParity v := by
  rw [mobius_representedNat_eq_globalChirality]
  exact globalChirality_vertex_eq_fermionParity P v


/-! ## 5. Finite Witten character: delegate to existing owner -/

/--
Canonical finite Witten character over the prime register.

This is deliberately delegated to `PrimeWittenCharacter`, avoiding duplicate
Euler-product proofs.
-/
@[rep_depth thermo]
def finiteWittenCharacter (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  InfoGeometry.Arithmetic.PrimeWittenCharacter.finiteWittenCharacter P q

/-- The finite Witten character equals the existing finite Euler product owner. -/
@[rep_depth thermo]
theorem finiteWittenCharacter_eq_eulerProduct
    (P : PrimeRegister)
    (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q := by
  exact InfoGeometry.Arithmetic.PrimeWittenCharacter.finiteWittenCharacter_eq_eulerProduct P q

/--
The finite Witten character agrees with the existing finite Dirichlet Witten
character.
-/
@[rep_depth thermo]
theorem finiteWittenCharacter_eq_dirichletWittenCharacter
    (P : PrimeRegister)
    (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter P q := by
  exact InfoGeometry.Arithmetic.PrimeWittenCharacter.finiteWittenCharacter_eq_dirichletWittenCharacter
    P q


/-! ## 6. Owner target -/

/--
Canonical finite Boolean-cube owner target.

This owner intentionally covers only finite combinatorial closure.
-/
@[owner_target_tag]
def PrimeBooleanCubeOwnerTarget : Prop :=
  ∀ (P : PrimeRegister) (v : Vertex P) (q : ℕ → ℝ),
    globalChirality P v.val = fermionParity v ∧
    ArithmeticFunction.moebius (representedNat v) = fermionParity v ∧
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q ∧
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter P q

/-- The canonical finite Boolean-cube owner target is closed. -/
theorem primeBooleanCubeOwnerTarget :
    PrimeBooleanCubeOwnerTarget := by
  intro P v q
  exact
    ⟨ globalChirality_vertex_eq_fermionParity P v,
      mobius_representedNat_eq_fermionParity P v,
      finiteWittenCharacter_eq_eulerProduct P q,
      finiteWittenCharacter_eq_dirichletWittenCharacter P q ⟩

end InfoGeometry.Arithmetic.PrimeBooleanCube
