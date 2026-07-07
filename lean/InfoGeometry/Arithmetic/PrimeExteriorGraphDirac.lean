import Mathlib
import InfoGeometry.Arithmetic.PrimeExteriorRepresentation
import InfoGeometry.Arithmetic.PrimeMajoranaCARGate
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeCantorLatticeDirac

/-!
# InfoGeometry.Arithmetic.PrimeExteriorGraphDirac

Finite graph/Hodge carrier on the prime-indexed Cantor cube.

This module pays the finite exterior-space debt.

Vertices are finite square-free exterior states over a finite prime cutoff.
Prime-axis graph motion is the already-owned Majorana bit flip.
Creation and annihilation are concrete partial maps on basis vertices.
The occupied Hodge block `ε_p ι_p` is exactly the number projector.
The weighted Hodge-square readout is exactly the prime-weighted number operator.

No infinite Euler product.
No analytic continuation.
No Hilbert--Polya claim.
No RH/Mertens socket.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeExteriorGraphDirac

open InfoGeometry.Arithmetic.PrimeExteriorRepresentation
open InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-- A finite prime cutoff, using the existing certified prime register. -/
abbrev PrimeCutoff := PrimeRegister

/-- A prime mode inside a finite cutoff. -/
abbrev PrimeMode (P : PrimeCutoff) :=
  {p : ℕ // p ∈ P.primes}

/-- A prime mode embedding into `ℕ`. -/
def primeModeEmbedding (P : PrimeCutoff) : PrimeMode P ↪ ℕ :=
  ⟨Subtype.val, by
    intro a b h
    exact Subtype.ext h⟩

/-- A vertex of the finite prime Cantor cube. -/
abbrev Vertex (P : PrimeCutoff) :=
  SquareFreePrimeState (PrimeMode P)

/-- The underlying occupied prime set of a Cantor vertex. -/
def occupied {P : PrimeCutoff} (v : Vertex P) : Finset (PrimeMode P) :=
  v

/-- Membership in a Cantor vertex. -/
def occupiedMode {P : PrimeCutoff} (v : Vertex P) (p : PrimeMode P) : Prop :=
  p ∈ v

/-! ## 1. Prime-axis graph motion -/

/-- Prime-axis bit flip on the finite exterior/Cantor vertex. -/
def flip {P : PrimeCutoff} (p : PrimeMode P) (S : Vertex P) : Vertex P :=
  majoranaFlip p S

/-- Prime-axis flip is involutive. -/
@[simp]
theorem flip_involutive
    {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
    flip p (flip p S) = S := by
  simpa [flip] using majoranaFlip_involutive p S

/-- The flipped mode is occupied iff it was previously unoccupied. -/
@[simp]
theorem mem_flip_self
    {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
    p ∈ flip p S ↔ p ∉ S := by
  simpa [flip] using mem_majoranaFlip_self p S

/-- Other modes are unaffected by the prime-axis flip. -/
@[simp]
theorem mem_flip_of_ne
    {P : PrimeCutoff}
    {p q : PrimeMode P}
    (hqp : q ≠ p)
    (S : Vertex P) :
    q ∈ flip p S ↔ q ∈ S := by
  simpa [flip] using mem_majoranaFlip_of_ne hqp S

/-- Cardinality increases by one when the flipped mode was absent. -/
theorem card_flip_of_not_mem
    {P : PrimeCutoff}
    {p : PrimeMode P}
    {S : Vertex P}
    (h : p ∉ S) :
    (flip p S).card = S.card + 1 := by
  simpa [flip] using card_majoranaFlip_of_not_mem h

/-- Cardinality decreases by one when the flipped mode was present. -/
theorem card_flip_add_one_of_mem
    {P : PrimeCutoff}
    {p : PrimeMode P}
    {S : Vertex P}
    (h : p ∈ S) :
    (flip p S).card + 1 = S.card := by
  simpa [flip] using card_majoranaFlip_add_one_of_mem h

/-! ## 2. Creation and annihilation as partial basis maps -/

/--
Creation `ε_p` on basis vertices.

If `p` is already occupied, the result is zero, represented by `none`.
-/
def create {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
    Option (Vertex P) :=
  if p ∈ S then none else some (insert p S)

/--
Annihilation `ι_p` on basis vertices.

If `p` is absent, the result is zero, represented by `none`.
-/
def annihilate {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
    Option (Vertex P) :=
  if p ∈ S then some (S.erase p) else none

/-- The occupied chiral Hodge block `ε_p ι_p`. -/
def createAfterAnnihilate {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
    Option (Vertex P) :=
  (annihilate p S).bind (create p)

/-- The vacant chiral Hodge block `ι_p ε_p`. -/
def annihilateAfterCreate {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
    Option (Vertex P) :=
  (create p S).bind (annihilate p)

/-- The occupied block `ε_p ι_p` is the number projector on basis vertices. -/
theorem createAfterAnnihilate_eq_if
    {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
    createAfterAnnihilate p S =
      if p ∈ S then some S else none := by
  by_cases h : p ∈ S
  · have hpErase : p ∉ S.erase p := by simp
    have hinsert : insert p (S.erase p) = S := Finset.insert_erase h
    simp [createAfterAnnihilate, annihilate, create, h, hpErase, hinsert]
  · simp [createAfterAnnihilate, annihilate, create, h]

/-- The vacant block `ι_p ε_p` is the complementary number projector. -/
theorem annihilateAfterCreate_eq_if
    {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
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
theorem createAfterAnnihilate_eq_some_self_iff
    {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
    createAfterAnnihilate p S = some S ↔ p ∈ S := by
  by_cases h : p ∈ S
  · simp [createAfterAnnihilate, annihilate, create, h, Finset.insert_erase h]
  · simp [createAfterAnnihilate, annihilate, create, h]

/-- `ι_p ε_p` returns the original basis vertex exactly when `p` is vacant. -/
theorem annihilateAfterCreate_eq_some_self_iff
    {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
    annihilateAfterCreate p S = some S ↔ p ∉ S := by
  by_cases h : p ∈ S
  · simp [annihilateAfterCreate_eq_if, h]
  · simp [annihilateAfterCreate_eq_if, h]


/-! ## 3. Hodge-square / number-operator readout -/

/-- Occupancy readout of the `p` mode on a basis vertex. -/
def occupancyReadout {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) : ℝ :=
  if p ∈ S then 1 else 0

/--
Basis-level readout of the occupied Hodge block `ε_p ι_p`.

This is the diagonal square-readout that gives the number operator.
-/
def hodgeSquareReadout {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) : ℝ :=
  if createAfterAnnihilate p S = some S then 1 else 0

/-- The occupied Hodge-square readout is exactly the occupancy readout. -/
theorem hodgeSquareReadout_eq_occupancyReadout
    {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) :
    hodgeSquareReadout p S = occupancyReadout p S := by
  by_cases h : p ∈ S
  · simp [hodgeSquareReadout, occupancyReadout, h, createAfterAnnihilate_eq_some_self_iff]
  · simp [hodgeSquareReadout, occupancyReadout, h, createAfterAnnihilate_eq_some_self_iff]

/--
Finite prime-weighted arithmetic number energy on a Cantor vertex.

This is the diagonal Hamiltonian readout
`H(S) = ∑_{p ∈ S} weight p`.
-/
def weightedNumberEnergy
    (P : PrimeCutoff)
    (weight : PrimeMode P → ℝ)
    (S : Vertex P) : ℝ :=
  SquareFreePrimeState.squareFreeEnergy weight S

/--
The weighted Hodge-square energy obtained from the occupied block `ε_p ι_p`.
-/
def weightedHodgeSquareEnergy
    (P : PrimeCutoff)
    (weight : PrimeMode P → ℝ)
    (S : Vertex P) : ℝ :=
  S.sum fun p => weight p * hodgeSquareReadout p S

/-- The occupied Hodge-square readout gives the weighted number operator. -/
theorem weightedHodgeSquareEnergy_eq_weightedNumberEnergy
    (P : PrimeCutoff)
    (weight : PrimeMode P → ℝ)
    (S : Vertex P) :
  weightedHodgeSquareEnergy P weight S =
      weightedNumberEnergy P weight S := by
  unfold weightedHodgeSquareEnergy weightedNumberEnergy
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [hodgeSquareReadout_eq_occupancyReadout]
  unfold occupancyReadout
  simp [hp]

/-- The weighted number energy is the sum over occupied modes. -/
theorem weightedNumberEnergy_eq_sum_occupied
    (P : PrimeCutoff)
    (weight : PrimeMode P → ℝ)
    (S : Vertex P) :
    weightedNumberEnergy P weight S =
      S.sum weight := by
  rfl

/-- The weighted Hodge-square energy equals the occupied-mode sum. -/
theorem weightedHodgeSquareEnergy_eq_sum_occupied
    (P : PrimeCutoff)
    (weight : PrimeMode P → ℝ)
    (S : Vertex P) :
    weightedHodgeSquareEnergy P weight S =
      S.sum weight := by
  rw [weightedHodgeSquareEnergy_eq_weightedNumberEnergy]
  exact weightedNumberEnergy_eq_sum_occupied P weight S

/--
Arithmetic specialization: `primeEnergy p = log p`.

This is the finite-cutoff version of the arithmetic Hamiltonian readout.
-/
def primeEnergy {P : PrimeCutoff} (p : PrimeMode P) : ℝ :=
  Real.log (p : ℝ)

/-- The exterior-state energy with arithmetic prime weights. -/
def stateEnergy {P : PrimeCutoff} (S : Vertex P) : ℝ :=
  weightedNumberEnergy P primeEnergy S

/-- Prime-energy weighted number operator is the exterior-state energy. -/
theorem weightedNumberEnergy_primeEnergy_eq_stateEnergy
    (P : PrimeCutoff)
    (S : Vertex P) :
    weightedNumberEnergy P primeEnergy S = stateEnergy S := by
  rfl

/-- The Hodge-square energy with prime weights is exactly the exterior-state energy. -/
theorem weightedHodgeSquareEnergy_primeEnergy_eq_stateEnergy
    (P : PrimeCutoff)
    (S : Vertex P) :
    weightedHodgeSquareEnergy P primeEnergy S = stateEnergy S := by
  rw [weightedHodgeSquareEnergy_eq_weightedNumberEnergy]
  rfl


/-! ## 4. Bundled finite graph-Dirac carrier -/

/--
Finite prime exterior graph-Dirac carrier.

The carrier is finite and combinatorial.
The arithmetic specialization uses `primeEnergy p = log p`.
-/
structure FinitePrimeExteriorGraphDirac where
  P : PrimeCutoff
  weight : PrimeMode P → ℝ

namespace FinitePrimeExteriorGraphDirac

/-- Vertices of the finite prime exterior graph. -/
abbrev Vertex (D : FinitePrimeExteriorGraphDirac) :=
  PrimeExteriorGraphDirac.Vertex D.P

/-- Prime-axis Majorana graph move. -/
def flip
    (D : FinitePrimeExteriorGraphDirac)
    (p : PrimeMode D.P)
    (v : D.Vertex) :
    D.Vertex :=
  PrimeExteriorGraphDirac.flip p v

/-- Prime-axis graph move is involutive. -/
theorem flip_involutive
    (D : FinitePrimeExteriorGraphDirac)
    (p : PrimeMode D.P)
    (v : D.Vertex) :
    D.flip p (D.flip p v) = v := by
  simpa [flip] using PrimeExteriorGraphDirac.flip_involutive p v

/-- Weighted Hamiltonian readout on a finite exterior vertex. -/
def hamiltonian
    (D : FinitePrimeExteriorGraphDirac)
    (v : D.Vertex) : ℝ :=
  weightedNumberEnergy D.P D.weight v

/--
The finite Hodge-square readout equals the Hamiltonian readout.
-/
theorem hodgeSquare_eq_hamiltonian
    (D : FinitePrimeExteriorGraphDirac)
    (v : D.Vertex) :
    weightedHodgeSquareEnergy D.P D.weight v =
      D.hamiltonian v := by
  unfold hamiltonian
  exact weightedHodgeSquareEnergy_eq_weightedNumberEnergy D.P D.weight v

/-- Hamiltonian readout as occupied-mode sum. -/
theorem hamiltonian_eq_sum_occupied
    (D : FinitePrimeExteriorGraphDirac)
    (v : D.Vertex) :
    D.hamiltonian v =
      v.sum D.weight := by
  unfold hamiltonian
  exact weightedNumberEnergy_eq_sum_occupied D.P D.weight v

end FinitePrimeExteriorGraphDirac

/-! ## 5. Exterior chirality and Möbius readout -/

/-- Local Majorana parity on the exterior-state vertex. -/
def localMajoranaParity {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) : ℤ :=
  SquareFreePrimeState.localParitySign p S

/-- The local occupancy number on the exterior-state vertex. -/
def localOccupation {P : PrimeCutoff}
    (p : PrimeMode P)
    (S : Vertex P) : ℕ :=
  SquareFreePrimeState.localOccupation p S

/-- Local occupation is `1` exactly when the prime mode is present. -/
theorem localOccupation_eq_one_iff_mem
    {P : PrimeCutoff}
    (p : PrimeMode P) (S : Vertex P) :
    localOccupation p S = 1 ↔ p ∈ S := by
  simpa [localOccupation] using
    SquareFreePrimeState.localOccupation_eq_one_iff_mem p S

/-- Local occupation is `0` exactly when the prime mode is absent. -/
theorem localOccupation_eq_zero_iff_not_mem
    {P : PrimeCutoff}
    (p : PrimeMode P) (S : Vertex P) :
    localOccupation p S = 0 ↔ p ∉ S := by
  simpa [localOccupation] using
    SquareFreePrimeState.localOccupation_eq_zero_iff_not_mem p S

/-- Local parity is `-1` exactly when the prime mode is present. -/
theorem localMajoranaParity_eq_neg_one_iff_mem
    {P : PrimeCutoff}
    (p : PrimeMode P) (S : Vertex P) :
    localMajoranaParity p S = -1 ↔ p ∈ S := by
  simpa [localMajoranaParity] using
    SquareFreePrimeState.localParitySign_eq_neg_one_iff_mem p S

/-- Local parity is `+1` exactly when the prime mode is absent. -/
theorem localMajoranaParity_eq_one_iff_not_mem
    {P : PrimeCutoff}
    (p : PrimeMode P) (S : Vertex P) :
    localMajoranaParity p S = 1 ↔ p ∉ S := by
  simpa [localMajoranaParity] using
    SquareFreePrimeState.localParitySign_eq_one_iff_not_mem p S

/-- Local parity is `1 - 2N_p` on the exterior state. -/
theorem localMajoranaParity_eq_one_sub_two_localOccupation
    {P : PrimeCutoff}
    (p : PrimeMode P) (S : Vertex P) :
    localMajoranaParity p S = 1 - 2 * (localOccupation p S : ℤ) := by
  simpa [localMajoranaParity, localOccupation] using
    SquareFreePrimeState.localParitySign_eq_one_sub_two_localOccupation p S

/-- Global chirality on the finite exterior state. -/
def globalMajoranaChirality {P : PrimeCutoff} (S : Vertex P) : ℤ :=
  SquareFreePrimeState.Gamma S

/-- Global chirality is the product of local parities. -/
theorem globalMajoranaChirality_eq_prod_localParity
    {P : PrimeCutoff} (S : Vertex P) :
    globalMajoranaChirality S = ∏ p ∈ S, localMajoranaParity p S := by
  simpa [globalMajoranaChirality, localMajoranaParity] using
    (SquareFreePrimeState.gamma_eq_prod_localParity (S := S))

/-- Global chirality is the square-free fermion parity `(-1)^F`. -/
theorem globalMajoranaChirality_eq_neg_one_pow_card
    {P : PrimeCutoff} (S : Vertex P) :
    globalMajoranaChirality S = (-1 : ℤ) ^ S.card := by
  simpa [globalMajoranaChirality] using
    (SquareFreePrimeState.Gamma_eq_negOne_pow_fermionNumber (S := S))

/-- Global chirality agrees with the Möbius value of the represented prime product. -/
theorem globalMajoranaChirality_eq_mobius_primeProduct
    (P : PrimeCutoff) (S : Vertex P) :
    globalMajoranaChirality S =
      ArithmeticFunction.moebius (∏ p ∈ S, (p : ℕ)) := by
  classical
  let e : PrimeMode P ↪ ℕ := primeModeEmbedding P
  have hprime : ∀ p ∈ S.map e, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact P.prime_mem q.1 q.property
  have hmob :
      ArithmeticFunction.moebius (∏ p ∈ S.map e, p) =
        (-1 : ℤ) ^ S.card := by
    have hcard : (S.map e).card = S.card := Finset.card_map e
    simpa [hcard] using
      (PrimeBitWittenIndex.mobius_prime_product_eq_parity (S.map e) hprime)
  have hprod :
      (∏ p ∈ S.map e, p) = ∏ p ∈ S, (p : ℕ) := by
    have hmap := Finset.prod_map S e (fun p : ℕ => p)
    simpa [e, primeModeEmbedding] using hmap
  calc
    globalMajoranaChirality S = (-1 : ℤ) ^ S.card := by
      simpa [globalMajoranaChirality] using
        (SquareFreePrimeState.Gamma_eq_negOne_pow_fermionNumber (S := S))
    _ = ArithmeticFunction.moebius (∏ p ∈ S.map e, p) := by
      symm
      exact hmob
    _ = ArithmeticFunction.moebius (∏ p ∈ S, (p : ℕ)) := by
      rw [hprod]

/-! ## 6. Witten character and finite Euler product -/

/-- The finite Möbius/Witten character of the prime-exterior Dirac lattice. -/
def cantorDiracWittenCharacter
    (P : PrimeCutoff) (q : PrimeMode P → ℝ) : ℝ :=
  ((Finset.univ : Finset (PrimeMode P)).powerset).sum fun S =>
    (-1 : ℝ) ^ S.card * ∏ p ∈ S, q p

/-- Finite Euler-product form of the Cantor-lattice Dirac Witten character. -/
theorem cantorDiracWittenCharacter_eq_eulerProduct
    (P : PrimeCutoff) (q : PrimeMode P → ℝ) :
    cantorDiracWittenCharacter P q =
      ∏ p ∈ (Finset.univ : Finset (PrimeMode P)), (1 - q p) := by
  classical
  unfold cantorDiracWittenCharacter
  have hpow :=
    InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.powerset_signed_weight_eq_prod_one_sub
      (A := (Finset.univ : Finset (PrimeMode P))) (q := q)
  simpa [cantorDiracWittenCharacter] using hpow

/-- Möbius readout of the Cantor-lattice Dirac Witten character. -/
theorem cantorDiracWittenCharacter_eq_mobius_sum
    (P : PrimeCutoff) (q : PrimeMode P → ℝ) :
    cantorDiracWittenCharacter P q =
      ((Finset.univ : Finset (PrimeMode P)).powerset).sum fun S =>
        ((ArithmeticFunction.moebius (∏ p ∈ S, (p : ℕ)) : ℤ) : ℝ) *
          ∏ p ∈ S, q p := by
  classical
  unfold cantorDiracWittenCharacter
  refine Finset.sum_congr rfl ?_
  intro S hS
  have hμ :
      ArithmeticFunction.moebius (∏ p ∈ S, (p : ℕ)) =
        (-1 : ℤ) ^ S.card := by
    simpa using
      (PrimeBitWittenIndex.mobius_prime_product_eq_parity
        (S.map (primeModeEmbedding P))
        (by
          intro p hp
          rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
          exact P.prime_mem q.1 q.property))
  simpa [hμ]

/-- Unit-weight Witten cancellation on every nonempty finite prime-exterior lattice. -/
theorem cantorDiracWittenCharacter_unit_cancel
    (P : PrimeCutoff) (hP : P.primes.Nonempty) :
    cantorDiracWittenCharacter P (fun _ => (1 : ℝ)) = 0 := by
  rw [cantorDiracWittenCharacter_eq_eulerProduct]
  exact Finset.prod_eq_zero_iff.mpr
    (by
      rcases hP with ⟨p, hp⟩
      refine ⟨⟨p, hp⟩, by simp, ?_⟩
      ring)

/-! ## 7. Pfaffian skeleton -/

/--
The scalar Pfaffian of the 2×2 skew block

  `[0, a; -a, 0]`

is `a`.

This avoids importing a full Pfaffian API while retaining the exact
block-Pfaffian structure of the finite Majorana lattice.
-/
def skewBlockPfaffian (a : ℝ) : ℝ :=
  a

/-- Finite block-Pfaffian product for the prime-exterior Dirac lattice. -/
def cantorDiracPfaffianProduct
    (P : PrimeCutoff) (q : PrimeMode P → ℝ) : ℝ :=
  ∏ p ∈ (Finset.univ : Finset (PrimeMode P)), skewBlockPfaffian (1 - q p)

/-- The finite block-Pfaffian product equals the Witten character. -/
theorem cantorDiracPfaffianProduct_eq_wittenCharacter
    (P : PrimeCutoff) (q : PrimeMode P → ℝ) :
    cantorDiracPfaffianProduct P q =
      cantorDiracWittenCharacter P q := by
  rw [cantorDiracPfaffianProduct, cantorDiracWittenCharacter_eq_eulerProduct]
  simp [skewBlockPfaffian]

/-! ## 8. Stable projected chiral index -/

/--
Stable projected chiral index of the Cantor-exterior Dirac operator.

The raw hyperbolic Dirac flow has stable and unstable branches. The reciprocal
Euler product lives on the stable Mellin branch.
-/
def stableProjectedCantorDiracIndex
    (P : PrimeCutoff) (qStable : PrimeMode P → ℝ) : ℝ :=
  cantorDiracWittenCharacter P qStable

theorem stableProjectedCantorDiracIndex_eq_pfaffian
    (P : PrimeCutoff) (q : PrimeMode P → ℝ) :
    stableProjectedCantorDiracIndex P q =
      cantorDiracPfaffianProduct P q := by
  rw [stableProjectedCantorDiracIndex,
      cantorDiracPfaffianProduct_eq_wittenCharacter]

/--
Raw hyperbolic chiral index as stable branch minus unstable branch.
-/
def rawHyperbolicCantorDiracIndex
    (P : PrimeCutoff) (qStable qUnstable : PrimeMode P → ℝ) : ℝ :=
  stableProjectedCantorDiracIndex P qStable -
    stableProjectedCantorDiracIndex P qUnstable

theorem rawHyperbolicCantorDiracIndex_eq_pfaffian_difference
    (P : PrimeCutoff) (qStable qUnstable : PrimeMode P → ℝ) :
    rawHyperbolicCantorDiracIndex P qStable qUnstable =
      cantorDiracPfaffianProduct P qStable -
        cantorDiracPfaffianProduct P qUnstable := by
  rw [rawHyperbolicCantorDiracIndex,
      stableProjectedCantorDiracIndex_eq_pfaffian,
      stableProjectedCantorDiracIndex_eq_pfaffian]

end InfoGeometry.Arithmetic.PrimeExteriorGraphDirac
