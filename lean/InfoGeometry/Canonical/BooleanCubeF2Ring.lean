/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Category.BoolRing
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.ZMod.Basic
import InfoGeometry.Canonical.PrimeBooleanCantorBridge
import InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
# Finite Boolean cubes and coordinatewise `F₂`

This module identifies the Boolean ring on subsets of `Fin n` with the
coordinate ring `Fin n → ZMod 2`. It uses Mathlib's Boolean-algebra-to-ring
construction, so symmetric difference is addition and intersection is
multiplication by construction.
-/

namespace InfoGeometry.Canonical.BooleanCubeF2Ring

open scoped symmDiff
open BooleanAlgebra
open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.PrimeBooleanCantorBridge
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-- The characteristic-word bounded lattice hom from finite subsets to bits. -/
def subsetWordHom (n : ℕ) : BoundedLatticeHom (Finset (Fin n)) (Fin n → Bool) where
  toFun S i := decide (i ∈ S)
  map_sup' S T := by
    funext i
    simp
  map_inf' S T := by
    funext i
    simp
  map_top' := by
    funext i
    simp
  map_bot' := by
    funext i
    simp

/-- The subset-to-word lattice hom is bijective, with inverse given by support. -/
theorem subsetWordHom_bijective (n : ℕ) : Function.Bijective (subsetWordHom n) := by
  constructor
  · intro S T h
    ext i
    have hi := congrFun h i
    simpa [subsetWordHom] using hi
  · intro w
    refine ⟨Finset.univ.filter fun i : Fin n => w i = true, ?_⟩
    funext i
    simp [subsetWordHom]

/-- Ring equivalence between the Boolean ring of subsets and the Boolean ring
of `n`-bit words. -/
noncomputable def subsetWordRingEquiv (n : ℕ) :
    AsBoolRing (Finset (Fin n)) ≃+* AsBoolRing (Fin n → Bool) := by
  let f := (subsetWordHom n).asBoolRing
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro S T h
    have hword := congrArg ofBoolRing h
    change subsetWordHom n (ofBoolRing S) = subsetWordHom n (ofBoolRing T) at hword
    have hset := (subsetWordHom_bijective n).1 hword
    exact (ofBoolRing_inj).mp hset
  · intro w
    refine ⟨toBoolRing (Finset.univ.filter fun i : Fin n => ofBoolRing w i = true), ?_⟩
    apply (ofBoolRing_inj).mpr
    change subsetWordHom n (Finset.univ.filter fun i : Fin n => ofBoolRing w i = true) =
      ofBoolRing w
    funext i
    simp [subsetWordHom]

/-- Encode a Boolean-ring bit as its field element in `ZMod 2`. -/
def boolF2Hom : AsBoolRing Bool →+* ZMod 2 where
  toFun b := if ofBoolRing b then 1 else 0
  map_zero' := by simp
  map_one' := by simp
  map_add' b c := by
    cases hb : ofBoolRing b <;> cases hc : ofBoolRing c
    · simp [ofBoolRing_add, hb, hc]
    · simp [ofBoolRing_add, hb, hc]
    · simp [ofBoolRing_add, hb, hc]
    · simp only [ofBoolRing_add, hb, hc]
      calc
        (0 : ZMod 2) = 2 := (ZMod.natCast_self 2).symm
        _ = 1 + 1 := by norm_num
  map_mul' b c := by
    cases hb : ofBoolRing b <;> cases hc : ofBoolRing c <;>
      simp [ofBoolRing_mul, hb, hc]

/-- The Boolean ring on one bit is the field `F₂`. -/
noncomputable def boolF2Equiv : AsBoolRing Bool ≃+* ZMod 2 :=
  RingEquiv.ofBijective boolF2Hom (by
    constructor
    · intro b c h
      apply (ofBoolRing_inj).mp
      cases hb : ofBoolRing b <;> cases hc : ofBoolRing c <;>
        simp [boolF2Hom, hb, hc] at h ⊢
    · intro z
      have hz : z = 0 ∨ z = 1 := by
        have hv := ZMod.val_lt z
        by_cases h0 : z.val = 0
        · exact Or.inl ((ZMod.val_eq_zero z).mp h0)
        · have h1 : z.val = 1 := by omega
          exact Or.inr ((ZMod.val_eq_one (by decide) z).mp h1)
      rcases hz with rfl | rfl
      · refine ⟨toBoolRing false, ?_⟩
        simp [boolF2Hom]
      · refine ⟨toBoolRing true, ?_⟩
        simp [boolF2Hom]
  )

/-- Pointwise passage from Boolean-word rings to coordinatewise `F₂`. -/
noncomputable def wordF2Equiv (n : ℕ) :
    AsBoolRing (Fin n → Bool) ≃+* (Fin n → ZMod 2) := by
  let e := RingEquiv.piCongrRight (fun _ : Fin n => boolF2Equiv)
  exact e

/-- Coordinate evaluation of the Boolean-word-to-`F₂` ring equivalence. -/
theorem wordF2Equiv_apply (n : ℕ) (w : AsBoolRing (Fin n → Bool)) (i : Fin n) :
    wordF2Equiv n w i = boolF2Equiv (toBoolRing (ofBoolRing w i)) := rfl

/-- The finite Boolean powerset ring is the coordinatewise `F₂` ring. -/
noncomputable def finiteBooleanCubeF2Equiv (n : ℕ) :
    AsBoolRing (Finset (Fin n)) ≃+* (Fin n → ZMod 2) :=
  (subsetWordRingEquiv n).trans (wordF2Equiv n)

/-- A finite Boolean Weyl element is the corresponding `F₂` support vector,
after choosing an enumeration of the prime cutoff. This is an equivalence of
carriers; the root-system owner does not equip `BooleanWeylGroup` itself with a
group or ring structure. -/
noncomputable def booleanWeylF2Equiv {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) :
    BooleanWeylGroup L ≃ (Fin L.primes.card → ZMod 2) :=
  (booleanWeylEquivBinaryWord e).trans (wordF2Equiv _).toEquiv

/-- Coordinate readout of the root-support-to-`F₂` equivalence. -/
theorem booleanWeylF2Equiv_apply {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (w : BooleanWeylGroup L)
    (i : Fin L.primes.card) :
    booleanWeylF2Equiv e w i = if (e i : ℕ) ∈ w.support then 1 else 0 := by
  change (if weylToWord e w i = true then (1 : ZMod 2) else 0) = _
  simp [weylToWord]

/-- The sign character determined by the number of nonzero coordinates of a
finite `F₂` vector. -/
def f2ParitySign {n : ℕ} (v : Fin n → ZMod 2) : ℝ :=
  (-1 : ℝ) ^ (Finset.univ.filter fun i => v i = 1).card

/-- Product form of the parity character, one factor per coordinate. -/
theorem f2ParitySign_eq_prod {n : ℕ} (v : Fin n → ZMod 2) :
    f2ParitySign v = ∏ i : Fin n, if v i = 1 then (-1 : ℝ) else 1 := by
  classical
  unfold f2ParitySign
  rw [Finset.prod_ite]
  simp

/-- Exhaustive values in the two-element field. -/
private theorem zmodTwo_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have ha := ZMod.val_lt a
  have hv : a.val = 0 ∨ a.val = 1 := by omega
  rcases hv with h | h
  · exact Or.inl ((ZMod.val_injective 2) h)
  · exact Or.inr ((ZMod.val_injective 2) h)

/-- The parity character sends the additive identity to the multiplicative
identity. -/
@[simp] theorem f2ParitySign_zero {n : ℕ} :
    f2ParitySign (0 : Fin n → ZMod 2) = 1 := by
  simp [f2ParitySign]

/-- The `F₂` support-parity readout is a group character from additive vectors
to the multiplicative signs `{+1,-1}`. -/
theorem f2ParitySign_add {n : ℕ} (v w : Fin n → ZMod 2) :
    f2ParitySign (v + w) = f2ParitySign v * f2ParitySign w := by
  classical
  rw [f2ParitySign_eq_prod, f2ParitySign_eq_prod, f2ParitySign_eq_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rcases zmodTwo_eq_zero_or_one (v i) with hv | hv <;>
    rcases zmodTwo_eq_zero_or_one (w i) with hw | hw <;> simp [hv, hw]

/-- The support of a Boolean Weyl element is in bijection with the nonzero
coordinates of its `F₂` vector, for any chosen enumeration of the prime set. -/
theorem booleanWeylF2Equiv_support_card {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (w : BooleanWeylGroup L) :
    (Finset.univ.filter fun i => booleanWeylF2Equiv e w i = 1).card = w.support.card := by
  classical
  refine Finset.card_bij (s := Finset.univ.filter fun i => booleanWeylF2Equiv e w i = 1)
    (t := w.support) (fun i _ => (e i : ℕ)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simpa [booleanWeylF2Equiv_apply] using hi
  · intro i hi j hj hij
    apply e.injective
    exact Subtype.ext hij
  · intro p hp
    have hpL : p ∈ L.primes := w.support_subset hp
    obtain ⟨i, hi⟩ := e.surjective ⟨p, hpL⟩
    have hval : (e i : ℕ) = p := congrArg Subtype.val hi
    refine ⟨i, ?_, hval⟩
    simp [booleanWeylF2Equiv_apply, hval, hp]

/-- The finite Weyl sign is exactly the parity sign of its `F₂` support vector. -/
theorem weylSign_eq_f2ParitySign {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (w : BooleanWeylGroup L) :
    weylSign w = f2ParitySign (booleanWeylF2Equiv e w) := by
  rw [f2ParitySign, booleanWeylF2Equiv_support_card]
  rfl

/-- Prime subset encoded by the nonzero coordinates of an `F₂` vector, using
a fixed enumeration of the finite prime root system. -/
def f2PrimeSupport {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (v : Fin L.primes.card → ZMod 2) : Finset ℕ :=
  (Finset.univ.filter fun i => v i = 1).image fun i => (e i : ℕ)

/-- The squarefree integer represented by an `F₂` support vector. -/
def f2SupportPrimeProduct {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (v : Fin L.primes.card → ZMod 2) : ℕ :=
  ∏ p ∈ f2PrimeSupport e v, p

/-- The nonzero `F₂` coordinates encode distinct primes from the root cutoff. -/
theorem f2PrimeSupport_card {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (v : Fin L.primes.card → ZMod 2) :
    (f2PrimeSupport e v).card = (Finset.univ.filter fun i => v i = 1).card := by
  classical
  unfold f2PrimeSupport
  rw [Finset.card_image_of_injective _ (fun i j hij => e.injective (Subtype.ext hij))]

/-- The prime product encoded by an `F₂` vector is squarefree. -/
theorem f2SupportPrimeProduct_squarefree {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (v : Fin L.primes.card → ZMod 2) :
    Squarefree (f2SupportPrimeProduct e v) := by
  classical
  let S := f2PrimeSupport e v
  have hprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    exact L.prime_mem (e i).val (e i).property
  unfold f2SupportPrimeProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro x hx y hy hxy
    have hx_prime := hprime x hx
    have hy_prime := hprime y hy
    simpa [Function.onFun, Nat.coprime_iff_isRelPrime] using
      ((Nat.coprime_primes hx_prime hy_prime).2 hxy)
  · intro x hx
    exact (hprime x hx).squarefree

/-- The `F₂` parity character is the Möbius value of its encoded squarefree
prime product. This theorem starts with an arbitrary bit vector, constructs its
arithmetic support, and identifies the two readouts. -/
theorem f2ParitySign_eq_mobius_f2SupportPrimeProduct {L : FormalPrimeRootLattice}
    (e : Fin L.primes.card ≃ L.primes) (v : Fin L.primes.card → ZMod 2) :
    f2ParitySign v = (ArithmeticFunction.moebius (f2SupportPrimeProduct e v) : ℝ) := by
  classical
  let S := f2PrimeSupport e v
  have hprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    exact L.prime_mem (e i).val (e i).property
  have hmob := InfoGeometry.Arithmetic.PrimeBitWittenIndex.mobius_prime_product_eq_parity
    S hprime
  have hcast : (ArithmeticFunction.moebius (∏ p ∈ S, p) : ℝ) =
      (-1 : ℝ) ^ S.card := by
    exact_mod_cast hmob
  change (-1 : ℝ) ^ (Finset.univ.filter fun i => v i = 1).card =
    (ArithmeticFunction.moebius (∏ p ∈ S, p) : ℝ)
  rw [hcast, ← f2PrimeSupport_card e v]

/-! ## The local Clifford-projector Boolean ring -/

open InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra
open InfoGeometry.Canonical.KreinProjectorLattice

/-- The existing order-preserving atom swap is the transposition of the two
Boolean coordinates. In particular, it is not coordinatewise bit-flip (which
would exchange bottom and top). -/
theorem kreinSectorBitEquiv_signFlip (a : KreinSector) :
    kreinSectorBitEquiv (signFlip a) = Prod.swap (kreinSectorBitEquiv a) := by
  cases a <;> rfl

/-- The four-sector projector lattice is a two-coordinate Boolean cube. -/
private def kreinSectorPairHom : BoundedLatticeHom KreinSector (Bool × Bool) where
  toFun := kreinSectorBitEquiv
  map_sup' := kreinSectorBitEquiv_sup
  map_inf' := kreinSectorBitEquiv_inf
  map_top' := rfl
  map_bot' := rfl

/-- At one site, the four complementary Clifford projectors form the Boolean
ring on two bits: the coordinates record the minus and plus atoms separately.
Composing with `boolF2Equiv` in each coordinate identifies it with `F₂ × F₂`.
This describes only the projector subalgebra, not the full Clifford algebra. -/
noncomputable def kreinSectorBoolRingEquiv :
    AsBoolRing KreinSector ≃+* AsBoolRing (Bool × Bool) := by
  let f := kreinSectorPairHom.asBoolRing
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      apply (ofBoolRing_inj).mp
      exact kreinSectorBitEquiv.injective ((ofBoolRing_inj).mp h)
    · intro b
      refine ⟨toBoolRing (kreinSectorBitEquiv.symm (ofBoolRing b)), ?_⟩
      apply (ofBoolRing_inj).mpr
      exact kreinSectorBitEquiv.apply_symm_apply (ofBoolRing b)
  exact RingEquiv.ofBijective f hf

/-- Reindex a pair of Boolean bits by the two-element finite type. -/
private def boolPairWordHom : BoundedLatticeHom (Bool × Bool) (Fin 2 → Bool) where
  toFun b i := if i.val = 0 then b.1 else b.2
  map_sup' b c := by
    rcases b with ⟨b₀, b₁⟩
    rcases c with ⟨c₀, c₁⟩
    funext i
    fin_cases i <;> rfl
  map_inf' b c := by
    rcases b with ⟨b₀, b₁⟩
    rcases c with ⟨c₀, c₁⟩
    funext i
    fin_cases i <;> rfl
  map_top' := by funext i; fin_cases i <;> rfl
  map_bot' := by funext i; fin_cases i <;> rfl

/-- The two-bit Boolean ring is the pointwise function ring on `Fin 2`. -/
private noncomputable def boolPairWordRingEquiv :
    AsBoolRing (Bool × Bool) ≃+* AsBoolRing (Fin 2 → Bool) := by
  let f := boolPairWordHom.asBoolRing
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      apply (ofBoolRing_inj).mp
      have h' : boolPairWordHom (ofBoolRing a) = boolPairWordHom (ofBoolRing b) := by
        change ofBoolRing (f a) = ofBoolRing (f b)
        exact congrArg ofBoolRing h
      apply Prod.ext
      · have hi' := congrFun h' ⟨0, by decide⟩
        simpa [boolPairWordHom] using hi'
      · have hi' := congrFun h' ⟨1, by decide⟩
        simpa [boolPairWordHom] using hi'
    · intro w
      let b : Bool × Bool := (w ⟨0, by decide⟩, w ⟨1, by decide⟩)
      refine ⟨toBoolRing b, ?_⟩
      apply (ofBoolRing_inj).mpr
      funext i
      fin_cases i <;> rfl
  exact RingEquiv.ofBijective f hf

/-- Evaluation of the reindexing equivalence on one Boolean pair. -/
private theorem boolPairWordRingEquiv_apply (a : AsBoolRing (Bool × Bool)) :
    boolPairWordRingEquiv a = toBoolRing (boolPairWordHom (ofBoolRing a)) := by
  rfl

/-- The local split-Clifford projector sectors form exactly the two-bit
`F₂`-vector ring. Coordinates are the minus- and plus-projector occupancies. -/
noncomputable def kreinSectorF2ProductEquiv :
    AsBoolRing KreinSector ≃+* (Fin 2 → ZMod 2) :=
  (kreinSectorBoolRingEquiv.trans boolPairWordRingEquiv).trans (wordF2Equiv 2)

/-- Evaluation of the first Boolean-ring equivalence on a sector. -/
theorem kreinSectorBoolRingEquiv_apply (a : AsBoolRing KreinSector) :
    kreinSectorBoolRingEquiv a =
      toBoolRing (kreinSectorBitEquiv (ofBoolRing a)) := by
  rfl

/-- In the pointwise `F₂²` representation, swapping the two projector atoms
acts by the corresponding reindexing ring automorphism. -/
theorem kreinSectorF2ProductEquiv_signFlip (a : KreinSector) :
    kreinSectorF2ProductEquiv (toBoolRing (signFlip a)) =
      RingEquiv.piCongrLeft' (fun _ : Fin 2 => ZMod 2) (Equiv.swap 0 1)
        (kreinSectorF2ProductEquiv (toBoolRing a)) := by
  cases a <;> ext i <;> fin_cases i
  all_goals
    simp only [kreinSectorF2ProductEquiv, RingEquiv.trans_apply]
    simp [wordF2Equiv_apply, boolPairWordRingEquiv_apply,
      kreinSectorBoolRingEquiv_apply, boolPairWordHom,
      kreinSectorBitEquiv, signFlip, boolF2Equiv, boolF2Hom]

end InfoGeometry.Canonical.BooleanCubeF2Ring
