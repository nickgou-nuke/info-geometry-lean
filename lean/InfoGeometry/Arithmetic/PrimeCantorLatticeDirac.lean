import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
# InfoGeometry.Arithmetic.PrimeCantorLatticeDirac

Finite prime-Cantor lattice Dirac skeleton.

The finite cutoff is a certified prime register `P`. Its Cantor lattice is the
Boolean cube of square-free occupancy states `S ⊆ P.primes`.

The `p`-axis edge is the bit flip `S ↦ S △ {p}`. The Dirac operator is the
prime-weighted graph/Clifford transport operator that sums over these axis
flips. The arithmetic Hamiltonian is the diagonal number operator

  `H(S) = Σ_{p∈S} λ p`

and the Möbius/Witten character is

  `Σ_{S⊆P} (-1)^|S| ∏_{p∈S} q p = ∏_{p∈P} (1 - q p)`.

Analytically one later sets `λ p = log p` and `q p = p^{-s}`. This module
does not assert the infinite Euler product, analytic continuation, or any
Type-III/Tomita theorem.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCantorLatticeDirac

open scoped BigOperators
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-! ## 1. Finite Cantor lattice -/

/--
The finite Cantor lattice carried by a prime register.

A vertex is a subset of the finite prime register, i.e. a square-free
occupancy configuration.
-/
@[rep_depth thermo]
abbrev CantorVertex (P : PrimeRegister) :=
  {S : Finset ℕ // S ⊆ P.primes}

/-- The finite set of Cantor-lattice vertices as powerset data. -/
@[rep_depth thermo]
def cantorVertices (P : PrimeRegister) : Finset (Finset ℕ) :=
  P.primes.powerset

@[rep_depth thermo]
theorem mem_cantorVertices_iff
    (P : PrimeRegister) (S : Finset ℕ) :
    S ∈ cantorVertices P ↔ S ⊆ P.primes := by
  simp [cantorVertices]

/--
The square-free integer represented by a Cantor vertex.
-/
@[rep_depth thermo]
def vertexNat (P : PrimeRegister) (v : CantorVertex P) : ℕ :=
  ∏ p ∈ v.val, p

/--
Fermion number of a Cantor vertex: the number of occupied prime axes.
-/
@[rep_depth thermo]
def vertexFermionNumber (P : PrimeRegister) (v : CantorVertex P) : ℕ :=
  v.val.card

/--
The ordinary Boolean bit flip along the `p`-axis.

This is the Cantor-lattice edge map `S ↦ S △ {p}`.
-/
@[rep_depth thermo]
def bitFlip (p : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if p ∈ S then S.erase p else insert p S

@[rep_depth thermo]
theorem mem_bitFlip_self (p : ℕ) (S : Finset ℕ) :
    p ∈ bitFlip p S ↔ p ∉ S := by
  classical
  unfold bitFlip
  by_cases hp : p ∈ S <;> simp [hp]

@[rep_depth thermo]
theorem mem_bitFlip_of_ne
    {x p : ℕ} (hxp : x ≠ p) (S : Finset ℕ) :
    x ∈ bitFlip p S ↔ x ∈ S := by
  classical
  unfold bitFlip
  by_cases hp : p ∈ S <;> simp [hp, hxp]

/-- Bit flip is an involution on the Boolean lattice. -/
@[rep_depth thermo]
theorem bitFlip_involutive (p : ℕ) (S : Finset ℕ) :
    bitFlip p (bitFlip p S) = S := by
  classical
  ext x
  by_cases hxp : x = p
  · subst x
    calc
      p ∈ bitFlip p (bitFlip p S) ↔ p ∉ bitFlip p S :=
        mem_bitFlip_self p (bitFlip p S)
      _ ↔ ¬ p ∉ S := by rw [mem_bitFlip_self]
      _ ↔ p ∈ S := not_not
  · rw [mem_bitFlip_of_ne hxp, mem_bitFlip_of_ne hxp]

/--
Bit flip preserves the finite prime register when the flipped axis belongs to
the register.
-/
@[rep_depth thermo]
theorem bitFlip_subset_register
    (P : PrimeRegister) {p : ℕ} (hp : p ∈ P.primes)
    {S : Finset ℕ} (hS : S ⊆ P.primes) :
    bitFlip p S ⊆ P.primes := by
  classical
  intro x hx
  by_cases hxp : x = p
  · subst x
    exact hp
  · have hxS : x ∈ S := (mem_bitFlip_of_ne hxp S).mp hx
    exact hS hxS

/--
The `p`-axis bit flip as an endomorphism of the finite Cantor lattice.
-/
@[rep_depth thermo]
def bitFlipVertex
    (P : PrimeRegister) (p : ℕ) (hp : p ∈ P.primes)
    (v : CantorVertex P) : CantorVertex P :=
  ⟨bitFlip p v.val, bitFlip_subset_register P hp v.property⟩

/-- Vertex-level bit flip is involutive. -/
@[rep_depth thermo]
theorem bitFlipVertex_involutive
    (P : PrimeRegister) (p : ℕ) (hp : p ∈ P.primes)
    (v : CantorVertex P) :
    bitFlipVertex P p hp (bitFlipVertex P p hp v) = v := by
  apply Subtype.ext
  exact bitFlip_involutive p v.val

/-! ## 2. Prime-Cantor graph Dirac operator -/

/--
A real field on the finite prime-Cantor lattice.
-/
@[rep_depth krein]
abbrev CantorField (P : PrimeRegister) :=
  CantorVertex P → ℝ

/--
The prime-weighted graph Dirac operator on the finite Cantor lattice.

For a field `f`, it sums the values of `f` on all prime-axis neighbors of
`v`, weighted by `κ p`.

Mathematically:

  `(D_κ f)(S) = Σ_{p∈P} κ_p f(S △ {p})`.
-/
@[rep_depth krein]
def cantorGraphDirac
    (P : PrimeRegister) (κ : ℕ → ℝ)
    (f : CantorField P) (v : CantorVertex P) : ℝ :=
  ∑ p ∈ P.primes.attach,
    κ p.val * f (bitFlipVertex P p.val p.property v)

/--
The `p`-axis component of the graph Dirac operator.
-/
@[rep_depth krein]
def cantorAxisDirac
    (P : PrimeRegister) (κ : ℕ → ℝ)
    (p : ℕ) (hp : p ∈ P.primes)
    (f : CantorField P) (v : CantorVertex P) : ℝ :=
  κ p * f (bitFlipVertex P p hp v)

/--
The graph Dirac operator is the sum of its prime-axis components.
-/
@[rep_depth krein]
theorem cantorGraphDirac_eq_axis_sum
    (P : PrimeRegister) (κ : ℕ → ℝ)
    (f : CantorField P) (v : CantorVertex P) :
    cantorGraphDirac P κ f v =
      ∑ p ∈ P.primes.attach,
        cantorAxisDirac P κ p.val p.property f v := by
  rfl

/--
A finite Dirac packet on the prime-Cantor lattice.

`axisWeight` is the abstract coefficient `κ_p`. Analytically one may set
`κ_p = sqrt(log p)`, but that analytic specialization is not part of this
finite algebraic module.
-/
@[rep_depth krein]
abbrev PrimeCantorDirac (P : PrimeRegister) := ℕ → ℝ

namespace PrimeCantorDirac

abbrev axisWeight {P : PrimeRegister} (D : PrimeCantorDirac P) : ℕ → ℝ :=
  D

variable {P : PrimeRegister}
variable (D : PrimeCantorDirac P)

/-- The operator associated to a finite prime-Cantor Dirac packet. -/
@[rep_depth krein]
def op : CantorField P → CantorField P :=
  fun f v => cantorGraphDirac P D.axisWeight f v

/-- The `p`-axis component of the packet operator. -/
@[rep_depth krein]
def axisOp
    (p : ℕ) (hp : p ∈ P.primes) :
    CantorField P → CantorField P :=
  fun f v => cantorAxisDirac P D.axisWeight p hp f v

/-- The packet operator is the sum of its axis operators at each vertex. -/
@[rep_depth krein]
theorem op_eq_axis_sum
    (f : CantorField P) (v : CantorVertex P) :
    D.op f v =
      ∑ p ∈ P.primes.attach, D.axisOp p.val p.property f v := by
  rfl

end PrimeCantorDirac

/-! ## 3. Arithmetic Hamiltonian on the Cantor lattice -/

/--
Diagonal arithmetic energy of a vertex.

Analytically, setting `λ p = log p` gives

  `H(S) = log(∏_{p∈S} p)`.
-/
@[rep_depth thermo]
def arithmeticEnergy
    (P : PrimeRegister) (lam : ℕ → ℝ) (v : CantorVertex P) : ℝ :=
  ∑ p ∈ v.val, lam p

/--
The arithmetic Hamiltonian as a diagonal operator on Cantor fields.
-/
@[rep_depth thermo]
def arithmeticHamiltonian
    (P : PrimeRegister) (lam : ℕ → ℝ)
    (f : CantorField P) (v : CantorVertex P) : ℝ :=
  arithmeticEnergy P lam v * f v

/-! ## 4. Majorana/Möbius chirality on the Cantor lattice -/

/--
Local occupation number, as an integer.
-/
@[rep_depth thermo]
def occupationInt (p : ℕ) (S : Finset ℕ) : ℤ :=
  if p ∈ S then 1 else 0

/--
Local Majorana parity `Π_p = 1 - 2N_p`, evaluated on a Cantor vertex.
-/
@[rep_depth thermo]
def localMajoranaParity (p : ℕ) (S : Finset ℕ) : ℤ :=
  1 - 2 * occupationInt p S

@[rep_depth thermo]
theorem localMajoranaParity_of_mem
    {p : ℕ} {S : Finset ℕ} (hp : p ∈ S) :
    localMajoranaParity p S = -1 := by
  simp [localMajoranaParity, occupationInt, hp]

@[rep_depth thermo]
theorem localMajoranaParity_of_notMem
    {p : ℕ} {S : Finset ℕ} (hp : p ∉ S) :
    localMajoranaParity p S = 1 := by
  simp [localMajoranaParity, occupationInt, hp]

/--
Global Majorana chirality on the finite prime-Cantor lattice:

  `Γ_Λ = ∏_{p∈P} (1 - 2N_p)`.
-/
@[rep_depth thermo]
def globalMajoranaChirality
    (P : PrimeRegister) (S : Finset ℕ) : ℤ :=
  ∏ p ∈ P.primes, localMajoranaParity p S

/--
Global Majorana chirality equals fermion parity on every Cantor vertex.
-/
@[rep_depth thermo]
theorem globalMajoranaChirality_eq_neg_one_pow_card
    (P : PrimeRegister) (S : Finset ℕ) (hS : S ⊆ P.primes) :
    globalMajoranaChirality P S = (-1 : ℤ) ^ S.card := by
  classical
  unfold globalMajoranaChirality
  have hprod :
      (∏ p ∈ P.primes, localMajoranaParity p S) =
        (∏ p ∈ S, localMajoranaParity p S) *
          (∏ p ∈ P.primes \ S, localMajoranaParity p S) := by
    rw [← Finset.prod_union]
    · congr
      exact (Finset.union_sdiff_of_subset hS).symm
    · exact Finset.disjoint_sdiff
  rw [hprod]
  have hSprod :
      (∏ p ∈ S, localMajoranaParity p S) = (-1 : ℤ) ^ S.card := by
    calc
      (∏ p ∈ S, localMajoranaParity p S)
          = ∏ _p ∈ S, (-1 : ℤ) := by
              refine Finset.prod_congr rfl ?_
              intro p hp
              exact localMajoranaParity_of_mem hp
      _ = (-1 : ℤ) ^ S.card := by simp
  have hComp :
      (∏ p ∈ P.primes \ S, localMajoranaParity p S) = 1 := by
    calc
      (∏ p ∈ P.primes \ S, localMajoranaParity p S)
          = ∏ _p ∈ P.primes \ S, (1 : ℤ) := by
              refine Finset.prod_congr rfl ?_
              intro p hp
              have hpnot : p ∉ S := (Finset.mem_sdiff.mp hp).2
              exact localMajoranaParity_of_notMem hpnot
      _ = 1 := by simp
  rw [hSprod, hComp, mul_one]

/--
On square-free prime vertices, global Majorana chirality is the Möbius value
of the represented integer.
-/
@[rep_depth thermo]
theorem globalMajoranaChirality_eq_mobius_primeProduct
    (P : PrimeRegister) (S : Finset ℕ) (hS : S ⊆ P.primes) :
    globalMajoranaChirality P S =
      ArithmeticFunction.moebius (∏ p ∈ S, p) := by
  rw [globalMajoranaChirality_eq_neg_one_pow_card P S hS]
  exact
    (PrimeBitWittenIndex.mobius_prime_product_eq_parity
      S (fun p hp => P.prime_mem p (hS hp))).symm

/-! ## 5. Witten character and finite Euler product -/

/--
Generic signed powerset/Euler-product identity.
-/
@[rep_depth thermo]
theorem powerset_signed_weight_eq_prod_one_sub
    {α R : Type*} [DecidableEq α] [CommRing R]
    (A : Finset α) (q : α → R) :
    (∑ S ∈ A.powerset, (-1 : R) ^ S.card * ∏ a ∈ S, q a) =
      ∏ a ∈ A, (1 - q a) := by
  classical
  refine Finset.induction_on A ?empty ?insert
  · simp
  · intro a A ha ih
    rw [Finset.sum_powerset_insert ha]
    rw [Finset.prod_insert ha]

    have hsecond :
        (∑ S ∈ A.powerset,
            (-1 : R) ^ (insert a S).card * ∏ x ∈ insert a S, q x)
          =
        (-q a) *
          (∑ S ∈ A.powerset, (-1 : R) ^ S.card * ∏ x ∈ S, q x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro S hS
      have haS : a ∉ S := by
        intro hmem
        exact ha ((Finset.mem_powerset.mp hS) hmem)
      have hcard : (insert a S).card = S.card + 1 :=
        Finset.card_insert_of_notMem haS
      rw [hcard, pow_succ]
      simp [Finset.prod_insert haS]
      ring

    rw [hsecond, ih]
    ring

/--
The finite Möbius/Witten character of the prime-Cantor Dirac lattice.

This is the finite algebraic trace

  `Tr(Γ exp(-sH))`

after substituting `q p = p^{-s}`.
-/
@[rep_depth thermo]
def cantorDiracWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.primes.powerset,
    (-1 : ℝ) ^ S.card * ∏ p ∈ S, q p

/--
Finite Euler-product form of the Cantor-lattice Dirac Witten character.
-/
@[rep_depth thermo]
theorem cantorDiracWittenCharacter_eq_eulerProduct
    (P : PrimeRegister) (q : ℕ → ℝ) :
    cantorDiracWittenCharacter P q =
      ∏ p ∈ P.primes, (1 - q p) := by
  simpa [cantorDiracWittenCharacter]
    using powerset_signed_weight_eq_prod_one_sub P.primes q

/--
Möbius readout of the Cantor-lattice Dirac Witten character.
-/
@[rep_depth thermo]
theorem cantorDiracWittenCharacter_eq_mobius_sum
    (P : PrimeRegister) (q : ℕ → ℝ) :
    cantorDiracWittenCharacter P q =
      ∑ S ∈ P.primes.powerset,
        ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℝ) *
          ∏ p ∈ S, q p := by
  classical
  unfold cantorDiracWittenCharacter
  refine Finset.sum_congr rfl ?_
  intro S hS
  have hSub : S ⊆ P.primes := Finset.mem_powerset.mp hS
  have hμ :
      ArithmeticFunction.moebius (∏ p ∈ S, p) =
        (-1 : ℤ) ^ S.card :=
    PrimeBitWittenIndex.mobius_prime_product_eq_parity
      S (fun p hp => P.prime_mem p (hSub hp))
  rw [hμ]
  norm_num

/--
Unit-weight Witten cancellation on every nonempty finite prime-Cantor lattice.
-/
@[rep_depth thermo]
theorem cantorDiracWittenCharacter_unit_cancel
    (P : PrimeRegister) (hP : P.primes.Nonempty) :
    cantorDiracWittenCharacter P (fun _ => (1 : ℝ)) = 0 := by
  rw [cantorDiracWittenCharacter_eq_eulerProduct]
  exact Finset.prod_eq_zero_iff.mpr
    (by
      rcases hP with ⟨p, hp⟩
      refine ⟨p, hp, ?_⟩
      ring)

/-! ## 6. Pfaffian skeleton -/

/--
The scalar Pfaffian of the 2×2 skew block

  `[0, a; -a, 0]`

is `a`.

This avoids importing a full Pfaffian API while retaining the exact
block-Pfaffian structure of the finite Majorana lattice.
-/
@[rep_depth krein]
def skewBlockPfaffian (a : ℝ) : ℝ :=
  a

/--
Finite block-Pfaffian product for the prime-Cantor Dirac lattice.
-/
@[rep_depth krein]
def cantorDiracPfaffianProduct
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  ∏ p ∈ P.primes, skewBlockPfaffian (1 - q p)

/--
The finite block-Pfaffian product equals the Witten character.
-/
@[rep_depth krein]
theorem cantorDiracPfaffianProduct_eq_wittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) :
    cantorDiracPfaffianProduct P q =
      cantorDiracWittenCharacter P q := by
  rw [cantorDiracPfaffianProduct, cantorDiracWittenCharacter_eq_eulerProduct]
  simp [skewBlockPfaffian]

/-! ## 7. Stable projected chiral index -/

/--
Stable projected chiral index of the Cantor-lattice Dirac operator.

The raw hyperbolic Dirac flow has stable and unstable branches. The reciprocal
Euler product lives on the stable Mellin branch.
-/
@[rep_depth krein]
def stableProjectedCantorDiracIndex
    (P : PrimeRegister) (qStable : ℕ → ℝ) : ℝ :=
  cantorDiracWittenCharacter P qStable

@[rep_depth krein]
theorem stableProjectedCantorDiracIndex_eq_pfaffian
    (P : PrimeRegister) (q : ℕ → ℝ) :
    stableProjectedCantorDiracIndex P q =
      cantorDiracPfaffianProduct P q := by
  rw [stableProjectedCantorDiracIndex,
      cantorDiracPfaffianProduct_eq_wittenCharacter]

/--
Raw hyperbolic chiral index as stable branch minus unstable branch.
-/
@[rep_depth krein]
def rawHyperbolicCantorDiracIndex
    (P : PrimeRegister) (qStable qUnstable : ℕ → ℝ) : ℝ :=
  stableProjectedCantorDiracIndex P qStable -
    stableProjectedCantorDiracIndex P qUnstable

@[rep_depth krein]
theorem rawHyperbolicCantorDiracIndex_eq_pfaffian_difference
    (P : PrimeRegister) (qStable qUnstable : ℕ → ℝ) :
    rawHyperbolicCantorDiracIndex P qStable qUnstable =
      cantorDiracPfaffianProduct P qStable -
        cantorDiracPfaffianProduct P qUnstable := by
  rw [rawHyperbolicCantorDiracIndex,
      stableProjectedCantorDiracIndex_eq_pfaffian,
      stableProjectedCantorDiracIndex_eq_pfaffian]

end InfoGeometry.Arithmetic.PrimeCantorLatticeDirac
