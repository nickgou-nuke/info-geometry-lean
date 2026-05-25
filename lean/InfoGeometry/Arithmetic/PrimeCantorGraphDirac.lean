import Mathlib
import InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
# InfoGeometry.Arithmetic.PrimeCantorGraphDirac

Finite graph/Hodge carrier on the prime-indexed Cantor cube.

This module pays the finite exterior-space debt:

* vertices are finite subsets of a certified prime register;
* prime-axis graph motion is the already-owned Majorana bit flip;
* creation and annihilation are concrete partial maps on basis vertices;
* the occupied chiral Hodge block `ε_p ι_p` is exactly the number projector;
* the weighted square-readout is exactly the prime-weighted number operator.

No infinite Euler product.
No analytic continuation.
No Hilbert--Polya claim.
No zeta/RH socket.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeCantorGraphDirac

open InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-! ## 1. Finite Cantor vertices over a certified prime register -/

/-- A vertex of the finite prime Cantor cube is a subset of the prime register. -/
@[rep_depth thermo]
abbrev PrimeCantorVertex (P : PrimeRegister) :=
  {S : Finset ℕ // S ⊆ P.primes}

/-- The underlying occupied prime set of a Cantor vertex. -/
@[rep_depth thermo]
def PrimeCantorVertex.occupied
    {P : PrimeRegister} (v : PrimeCantorVertex P) : Finset ℕ :=
  v.val

/-- Membership in a Cantor vertex. -/
@[rep_depth thermo]
def PrimeCantorVertex.occupiedMode
    {P : PrimeRegister} (v : PrimeCantorVertex P) (p : ℕ) : Prop :=
  p ∈ v.occupied

/--
The existing Majorana bit flip preserves the finite prime register.
-/
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

/-- Prime-axis graph move on the finite Cantor cube. -/
@[rep_depth thermo]
def flipVertex
    {P : PrimeRegister}
    (p : ℕ)
    (hp : p ∈ P.primes)
    (v : PrimeCantorVertex P) :
    PrimeCantorVertex P where
  val := majoranaFlip p v.val
  property := majoranaFlip_subset_of_subset hp v.property

/-- The prime-axis graph move is involutive. -/
@[rep_depth thermo]
theorem flipVertex_involutive
    {P : PrimeRegister}
    (p : ℕ)
    (hp : p ∈ P.primes)
    (v : PrimeCantorVertex P) :
    flipVertex p hp (flipVertex p hp v) = v := by
  apply Subtype.ext
  simp [flipVertex, majoranaFlip_involutive]

/-- The flipped mode is occupied iff it was previously unoccupied. -/
@[rep_depth thermo]
theorem occupiedMode_flipVertex_self
    {P : PrimeRegister}
    (p : ℕ)
    (hp : p ∈ P.primes)
    (v : PrimeCantorVertex P) :
    p ∈ (flipVertex p hp v).occupied ↔ p ∉ v.occupied := by
  simp [PrimeCantorVertex.occupied, flipVertex]

/-- Other modes are unaffected by the prime-axis graph move. -/
@[rep_depth thermo]
theorem occupiedMode_flipVertex_of_ne
    {P : PrimeRegister}
    {p q : ℕ}
    (hp : p ∈ P.primes)
    (hqp : q ≠ p)
    (v : PrimeCantorVertex P) :
    q ∈ (flipVertex p hp v).occupied ↔ q ∈ v.occupied := by
  simp [PrimeCantorVertex.occupied, flipVertex, mem_majoranaFlip_of_ne hqp]


/-! ## 2. Creation and annihilation as partial basis maps -/

/--
Creation `ε_p` on basis vertices.

If `p` is already occupied, the result is zero, represented by `none`.
-/
@[rep_depth thermo]
def create
    (p : ℕ)
    (S : Finset ℕ) : Option (Finset ℕ) :=
  if p ∈ S then none else some (insert p S)

/--
Annihilation `ι_p` on basis vertices.

If `p` is absent, the result is zero, represented by `none`.
-/
@[rep_depth thermo]
def annihilate
    (p : ℕ)
    (S : Finset ℕ) : Option (Finset ℕ) :=
  if p ∈ S then some (S.erase p) else none

/-- The occupied chiral block `ε_p ι_p`. -/
@[rep_depth thermo]
def createAfterAnnihilate
    (p : ℕ)
    (S : Finset ℕ) : Option (Finset ℕ) :=
  (annihilate p S).bind (create p)

/-- The vacant chiral block `ι_p ε_p`. -/
@[rep_depth thermo]
def annihilateAfterCreate
    (p : ℕ)
    (S : Finset ℕ) : Option (Finset ℕ) :=
  (create p S).bind (annihilate p)

/--
The occupied block `ε_p ι_p` is the number projector on basis vertices.
-/
@[rep_depth thermo]
theorem createAfterAnnihilate_eq_if
    (p : ℕ)
    (S : Finset ℕ) :
    createAfterAnnihilate p S =
      if p ∈ S then some S else none := by
  by_cases h : p ∈ S
  · have hpErase : p ∉ S.erase p := by simp
    have hinsert : insert p (S.erase p) = S := Finset.insert_erase h
    simp [createAfterAnnihilate, annihilate, create, h, hpErase, hinsert]
  · simp [createAfterAnnihilate, annihilate, create, h]

/--
The vacant block `ι_p ε_p` is the complementary number projector on basis
vertices.
-/
@[rep_depth thermo]
theorem annihilateAfterCreate_eq_if
    (p : ℕ)
    (S : Finset ℕ) :
    annihilateAfterCreate p S =
      if p ∈ S then none else some S := by
  by_cases h : p ∈ S
  · simp [annihilateAfterCreate, create, h]
  · have herase : (insert p S).erase p = S := by
      ext q
      by_cases hq : q = p
      · subst q
        simp [h]
      · simp [Finset.mem_erase, hq]
    simp [annihilateAfterCreate, create, annihilate, h, herase]

/-- `ε_p ι_p` returns the original basis vertex exactly when `p` is occupied. -/
@[rep_depth thermo]
theorem createAfterAnnihilate_eq_some_self_iff
    (p : ℕ)
    (S : Finset ℕ) :
    createAfterAnnihilate p S = some S ↔ p ∈ S := by
  rw [createAfterAnnihilate_eq_if]
  by_cases h : p ∈ S <;> simp [h]

/-- `ι_p ε_p` returns the original basis vertex exactly when `p` is vacant. -/
@[rep_depth thermo]
theorem annihilateAfterCreate_eq_some_self_iff
    (p : ℕ)
    (S : Finset ℕ) :
    annihilateAfterCreate p S = some S ↔ p ∉ S := by
  rw [annihilateAfterCreate_eq_if]
  by_cases h : p ∈ S <;> simp [h]

/-- Creation preserves the ambient prime register when the created mode is in it. -/
@[rep_depth thermo]
theorem create_preserves_register
    {P : PrimeRegister}
    {p : ℕ}
    {S T : Finset ℕ}
    (hp : p ∈ P.primes)
    (hS : S ⊆ P.primes)
    (hcreate : create p S = some T) :
    T ⊆ P.primes := by
  unfold create at hcreate
  by_cases h : p ∈ S
  · simp [h] at hcreate
  · simp [h] at hcreate
    subst T
    intro q hq
    by_cases hqp : q = p
    · subst q
      exact hp
    · exact hS (by simpa [hqp] using hq)

/-- Annihilation preserves the ambient prime register. -/
@[rep_depth thermo]
theorem annihilate_preserves_register
    {P : PrimeRegister}
    {p : ℕ}
    {S T : Finset ℕ}
    (hS : S ⊆ P.primes)
    (hann : annihilate p S = some T) :
    T ⊆ P.primes := by
  unfold annihilate at hann
  by_cases h : p ∈ S
  · simp [h] at hann
    subst T
    intro q hq
    exact hS (Finset.mem_erase.mp hq).2
  · simp [h] at hann


/-! ## 3. Weighted number operator and Hodge-square readout -/

/-- Occupancy readout of the `p` mode on a basis vertex. -/
@[rep_depth thermo]
def occupancyReadout
    (p : ℕ)
    (S : Finset ℕ) : ℝ :=
  if p ∈ S then 1 else 0

/--
Basis-level readout of the occupied Hodge block `ε_p ι_p`.

This is the diagonal square-readout that gives the number operator.
-/
@[rep_depth thermo]
def hodgeSquareReadout
    (p : ℕ)
    (S : Finset ℕ) : ℝ :=
  if createAfterAnnihilate p S = some S then 1 else 0

/-- The occupied Hodge-square readout is exactly the occupancy readout. -/
@[rep_depth thermo]
theorem hodgeSquareReadout_eq_occupancyReadout
    (p : ℕ)
    (S : Finset ℕ) :
    hodgeSquareReadout p S = occupancyReadout p S := by
  by_cases h : p ∈ S <;>
    simp [hodgeSquareReadout, occupancyReadout, createAfterAnnihilate_eq_if, h]

/--
Finite prime-weighted arithmetic number energy on a Cantor vertex.

This is the diagonal Hamiltonian readout
`H(S) = ∑_{p∈S} weight p`, restricted to the certified prime register.
-/
@[rep_depth thermo]
def weightedNumberEnergy
    (P : PrimeRegister)
    (weight : ℕ → ℝ)
    (S : Finset ℕ) : ℝ :=
  P.primes.sum (fun p => if p ∈ S then weight p else 0)

/--
The weighted Hodge-square energy obtained from the occupied block
`ε_p ι_p`.
-/
@[rep_depth thermo]
def weightedHodgeSquareEnergy
    (P : PrimeRegister)
    (weight : ℕ → ℝ)
    (S : Finset ℕ) : ℝ :=
  P.primes.sum (fun p => weight p * hodgeSquareReadout p S)

/--
The occupied Hodge-square readout gives the weighted number operator.
-/
@[rep_depth thermo]
theorem weightedHodgeSquareEnergy_eq_weightedNumberEnergy
    (P : PrimeRegister)
    (weight : ℕ → ℝ)
    (S : Finset ℕ) :
    weightedHodgeSquareEnergy P weight S =
      weightedNumberEnergy P weight S := by
  unfold weightedHodgeSquareEnergy weightedNumberEnergy
  refine Finset.sum_congr rfl ?_
  intro p hp
  by_cases h : p ∈ S <;>
    simp [hodgeSquareReadout_eq_occupancyReadout, occupancyReadout, h]

/--
If `S` is a vertex of the prime register, the weighted number energy is just
the sum over occupied modes.
-/
@[rep_depth thermo]
theorem weightedNumberEnergy_eq_sum_occupied
    (P : PrimeRegister)
    (weight : ℕ → ℝ)
    {S : Finset ℕ}
    (hS : S ⊆ P.primes) :
    weightedNumberEnergy P weight S =
      S.sum (fun p => weight p) := by
  unfold weightedNumberEnergy
  have hfilter : P.primes.filter (fun p => p ∈ S) = S := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hS hp, hp⟩
  calc
    P.primes.sum (fun p => if p ∈ S then weight p else 0)
        = (P.primes.filter (fun p => p ∈ S)).sum (fun p => weight p) := by
            rw [Finset.sum_filter]
    _ = S.sum (fun p => weight p) := by
            rw [hfilter]

/--
The weighted Hodge-square energy equals the occupied-mode sum.
-/
@[rep_depth thermo]
theorem weightedHodgeSquareEnergy_eq_sum_occupied
    (P : PrimeRegister)
    (weight : ℕ → ℝ)
    {S : Finset ℕ}
    (hS : S ⊆ P.primes) :
    weightedHodgeSquareEnergy P weight S =
      S.sum (fun p => weight p) := by
  rw [weightedHodgeSquareEnergy_eq_weightedNumberEnergy]
  exact weightedNumberEnergy_eq_sum_occupied P weight hS

/--
Creating an unoccupied prime mode adds exactly that mode's weight to the
finite prime-Cantor Hamiltonian.

This is the concrete creation-energy lemma:

  `H(S ∪ {p}) = H(S) + weight p`

provided `p` is in the certified prime register and not already occupied.
-/
@[rep_depth thermo]
theorem weightedNumberEnergy_insert_of_not_mem
    (P : PrimeRegister)
    (weight : ℕ → ℝ)
    {p : ℕ}
    {S : Finset ℕ}
    (hp : p ∈ P.primes)
    (hS : S ⊆ P.primes)
    (hnot : p ∉ S) :
    weightedNumberEnergy P weight (insert p S) =
      weightedNumberEnergy P weight S + weight p := by
  have hInsert : insert p S ⊆ P.primes := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hqp | hqS
    · subst q
      exact hp
    · exact hS hqS
  rw [weightedNumberEnergy_eq_sum_occupied P weight hInsert]
  rw [weightedNumberEnergy_eq_sum_occupied P weight hS]
  rw [Finset.sum_insert hnot]
  ring

/--
Annihilating an occupied prime mode subtracts exactly that mode's weight from
the finite prime-Cantor Hamiltonian.

This is the concrete annihilation-energy lemma:

  `H(S \ {p}) = H(S) - weight p`

provided `p` is occupied.
-/
@[rep_depth thermo]
theorem weightedNumberEnergy_erase_of_mem
    (P : PrimeRegister)
    (weight : ℕ → ℝ)
    {p : ℕ}
    {S : Finset ℕ}
    (hS : S ⊆ P.primes)
    (hmem : p ∈ S) :
    weightedNumberEnergy P weight (S.erase p) =
      weightedNumberEnergy P weight S - weight p := by
  have hErase : S.erase p ⊆ P.primes := by
    intro q hq
    exact hS (Finset.mem_of_mem_erase hq)
  rw [weightedNumberEnergy_eq_sum_occupied P weight hErase]
  rw [weightedNumberEnergy_eq_sum_occupied P weight hS]
  have hsum : (S.erase p).sum (fun q => weight q) + weight p = S.sum (fun q => weight q) := by
    simpa using Finset.sum_erase_add S (fun q => weight q) hmem
  exact (eq_sub_iff_add_eq).2 hsum


/-! ## 4. Bundled finite graph-Dirac carrier -/

/--
Finite prime Cantor graph-Dirac carrier.

The carrier is finite and combinatorial. The weights are arbitrary real
weights; the arithmetic specialization is `weight p = Real.log p`.
-/
@[rep_depth thermo]
structure FinitePrimeCantorGraphDirac where
  P : PrimeRegister
  weight : ℕ → ℝ

namespace FinitePrimeCantorGraphDirac

/-- Vertices of the finite prime Cantor graph. -/
@[rep_depth thermo]
abbrev Vertex (D : FinitePrimeCantorGraphDirac) :=
  PrimeCantorVertex D.P

/-- Prime-axis Majorana graph move. -/
@[rep_depth thermo]
def flip
    (D : FinitePrimeCantorGraphDirac)
    (p : ℕ)
    (hp : p ∈ D.P.primes)
    (v : D.Vertex) :
    D.Vertex :=
  flipVertex p hp v

/-- Prime-axis flip is involutive. -/
@[rep_depth thermo]
theorem flip_involutive
    (D : FinitePrimeCantorGraphDirac)
    (p : ℕ)
    (hp : p ∈ D.P.primes)
    (v : D.Vertex) :
    D.flip p hp (D.flip p hp v) = v :=
  flipVertex_involutive p hp v

/-- Arithmetic Hamiltonian readout on a vertex. -/
@[rep_depth thermo]
def hamiltonian
    (D : FinitePrimeCantorGraphDirac)
    (v : D.Vertex) : ℝ :=
  weightedNumberEnergy D.P D.weight v.val

/--
The finite Hodge-square readout equals the arithmetic Hamiltonian readout.
-/
@[rep_depth thermo]
theorem hodgeSquare_eq_hamiltonian
    (D : FinitePrimeCantorGraphDirac)
    (v : D.Vertex) :
    weightedHodgeSquareEnergy D.P D.weight v.val =
      D.hamiltonian v := by
  unfold hamiltonian
  exact weightedHodgeSquareEnergy_eq_weightedNumberEnergy D.P D.weight v.val

/-- Hamiltonian readout as the occupied-mode sum. -/
@[rep_depth thermo]
theorem hamiltonian_eq_sum_occupied
    (D : FinitePrimeCantorGraphDirac)
    (v : D.Vertex) :
    D.hamiltonian v =
      v.val.sum (fun p => D.weight p) := by
  unfold hamiltonian
  exact weightedNumberEnergy_eq_sum_occupied D.P D.weight v.property

end FinitePrimeCantorGraphDirac

end InfoGeometry.Arithmetic.PrimeCantorGraphDirac
