import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Canonical.CantorCuntzCliffordBridge
import InfoGeometry.Canonical.CantorProjectiveLimit
import Mathlib.Topology.Constructions

/-!
# Cantor Boundary Cuntz Shifts

This module implements the algebraic/cylindrical boundary layer for Cuntz
shifts on the Cantor boundary.

The proof boundary is intentionally narrow:

* the symbolic Cantor carrier is `ℕ → Bool`;
* global left/right Cuntz boundary maps are front-prefix maps;
* finite UHF cylinder compatibility uses the stage-local operation that appends
  the newly created bit at depth `n`, matching `diagEmbedSucc`;
* Cuntz-to-CAR facts are re-exported from the existing abstract `CuntzO2Carrier`
  owner.

No topology, C*-completion, KMS state, phase transition, or zeta-zero theorem is
claimed here.

#### BUCKET 1: CLOSED FINITE THEOREMS
Symbolic branch readbacks for `prefixBit`/`leftShift`/`rightShift`, finite
prefix compatibility, stage-local UHF successor-cylinder compatibility,
boundary/Cuntz branch packet readbacks, CAR consequences inherited from the
existing `CuntzO2Carrier`, and binary orbit recursion readouts.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
Native Cuntz branch theorem readouts depend only on the explicit packet
fields and the existing `CuntzO2Carrier` premises.

#### BUCKET 3: OPEN CLOSURE DEBT
Full topological Cantor space, C*-completion, Cuntz representation on a Hilbert
space, KMS dynamics, BEC/Hagedorn interpretation, and zeta/RH consequences.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryCuntzShift

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorCuntzBasis
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Topology

/-! ## Symbolic boundary shifts -/

/-- Add a bit to the front of an infinite binary Cantor stream. -/
def prefixBit (b : Bool) (x : (ℕ → Bool)) : (ℕ → Bool) :=
  fun
    | 0 => b
    | n + 1 => x n

/-- The left Cuntz symbolic branch prefixes `false`. -/
def leftShift (x : (ℕ → Bool)) : (ℕ → Bool) :=
  prefixBit false x

/-- The right Cuntz symbolic branch prefixes `true`. -/
def rightShift (x : (ℕ → Bool)) : (ℕ → Bool) :=
  prefixBit true x

@[simp] theorem prefixBit_zero (b : Bool) (x : (ℕ → Bool)) :
    prefixBit b x 0 = b := by
  rfl

@[simp] theorem prefixBit_succ (b : Bool) (x : (ℕ → Bool)) (n : ℕ) :
    prefixBit b x (n + 1) = x n := by
  rfl

theorem continuous_prefixBit (b : Bool) :
    Continuous (prefixBit b) := by
  apply continuous_pi
  intro n
  cases n with
  | zero => exact continuous_const
  | succ n =>
      simpa [prefixBit] using (continuous_apply n :
        Continuous (fun x : (ℕ → Bool) => x n))

theorem continuous_leftShift :
    Continuous leftShift := by
  exact continuous_prefixBit false

theorem continuous_rightShift :
    Continuous rightShift := by
  exact continuous_prefixBit true

@[simp] theorem leftShift_zero (x : (ℕ → Bool)) :
    leftShift x 0 = false := by
  rfl

@[simp] theorem rightShift_zero (x : (ℕ → Bool)) :
    rightShift x 0 = true := by
  rfl

@[simp] theorem leftShift_succ (x : (ℕ → Bool)) (n : ℕ) :
    leftShift x (n + 1) = x n := by
  rfl

@[simp] theorem rightShift_succ (x : (ℕ → Bool)) (n : ℕ) :
    rightShift x (n + 1) = x n := by
  rfl

theorem prefixBit_injective (b : Bool) :
    Function.Injective (prefixBit b) := by
  intro x y hxy
  funext n
  have h := congrFun hxy (n + 1)
  simpa [prefixBit] using h

theorem leftShift_injective :
    Function.Injective leftShift := by
  simpa [leftShift] using prefixBit_injective false

theorem rightShift_injective :
    Function.Injective rightShift := by
  simpa [rightShift] using prefixBit_injective true

theorem leftShift_range_disjoint (x y : (ℕ → Bool)) :
    leftShift x ≠ rightShift y := by
  intro hxy
  have h := congrFun hxy 0
  simp [leftShift, rightShift, prefixBit] at h

theorem prefixBit_head_tail (x : (ℕ → Bool)) :
    prefixBit (x 0) (fun n => x (n + 1)) = x := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem prefixBit_eq_iff
    (b : Bool) (x y : (ℕ → Bool)) :
    prefixBit b x = y ↔
      y 0 = b ∧ ∀ n, y (n + 1) = x n := by
  constructor
  · intro h
    constructor
    · simpa [prefixBit] using (congrFun h 0).symm
    · intro n
      simpa [prefixBit] using (congrFun h (n + 1)).symm
  · rintro ⟨hhead, htail⟩
    funext n
    cases n with
    | zero => simpa [prefixBit] using hhead.symm
    | succ n => simpa [prefixBit] using (htail n).symm

theorem prefixBit_range_eq (b : Bool) :
    Set.range (prefixBit b) = {x : (ℕ → Bool) | x 0 = b} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    refine ⟨fun n => x (n + 1), ?_⟩
    have hhead : x 0 = b := hx
    simpa [hhead] using prefixBit_head_tail x

theorem isClosed_prefixBit_range (b : Bool) :
    IsClosed (Set.range (prefixBit b)) := by
  rw [prefixBit_range_eq]
  exact isClosed_singleton.preimage (continuous_apply 0)

theorem isOpen_prefixBit_range (b : Bool) :
    IsOpen (Set.range (prefixBit b)) := by
  rw [prefixBit_range_eq]
  have hc : Continuous (fun x : (ℕ → Bool) => x 0) := continuous_apply 0
  exact hc.isOpen_preimage ({b} : Set Bool)
    (isOpen_discrete ({b} : Set Bool))

theorem prefixBit_range_cover (x : (ℕ → Bool)) :
    (∃ y, prefixBit false y = x) ∨
      ∃ y, prefixBit true y = x := by
  cases h : x 0 with
  | false =>
      left
      exact ⟨fun n => x (n + 1), by
        simpa [h] using prefixBit_head_tail x⟩
  | true =>
      right
      exact ⟨fun n => x (n + 1), by
        simpa [h] using prefixBit_head_tail x⟩

theorem prefixBit_range_disjoint :
    Disjoint (Set.range (prefixBit false)) (Set.range (prefixBit true)) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  exact leftShift_range_disjoint x y (hx.trans hy.symm)

theorem prefixBit_range_partition :
    Set.range (prefixBit false) ∪ Set.range (prefixBit true) = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
  exact prefixBit_range_cover x

theorem prefixBit_unique_branch (x : (ℕ → Bool)) :
    ∃! p : Bool × (ℕ → Bool), prefixBit p.1 p.2 = x := by
  refine ⟨(x 0, fun n => x (n + 1)), ?_, ?_⟩
  · exact prefixBit_head_tail x
  · intro p hp
    rcases p with ⟨b, y⟩
    have hhead : b = x 0 := by
      have := congrFun hp 0
      simpa [prefixBit] using this
    subst b
    congr
    funext n
    have htail := congrFun hp (n + 1)
    simpa [prefixBit] using htail

theorem prefixBit_bijective_headFiber (b : Bool) :
    Function.Bijective
      (fun x : (ℕ → Bool) =>
        (⟨prefixBit b x, by
          rfl⟩ : {x : (ℕ → Bool) // x 0 = b})) := by
  constructor
  · intro x y hxy
    apply prefixBit_injective b
    exact Subtype.ext_iff.mp hxy
  · intro y
    refine ⟨fun n => y.1 (n + 1), ?_⟩
    apply Subtype.ext
    simpa [y.2] using prefixBit_head_tail y.1

theorem prefixBit_range_union :
    Set.range (prefixBit false) ∪ Set.range (prefixBit true) =
      Set.univ := by
  rw [prefixBit_range_eq, prefixBit_range_eq]
  ext x
  cases h : x 0 <;> simp [h]

theorem prefixBit_range_inter_eq_empty
    {b c : Bool} (hbc : b ≠ c) :
    Set.range (prefixBit b) ∩ Set.range (prefixBit c) = ∅ := by
  rw [prefixBit_range_eq, prefixBit_range_eq]
  ext x
  constructor
  · rintro ⟨hb, hc⟩
    exact False.elim (hbc (hb.symm.trans hc))
  · intro hx
    exact False.elim hx

theorem prefixBit_nested_succ_succ
    (a b : Bool) (x : (ℕ → Bool)) (n : ℕ) :
    prefixBit a (prefixBit b x) (n + 2) = x n := by
  rfl

theorem prefixBit_nested_prefix
    (a b : Bool) (x : (ℕ → Bool)) :
    prefixBit a (prefixBit b x) 0 = a ∧
      prefixBit a (prefixBit b x) 1 = b := by
  exact ⟨rfl, rfl⟩

/-- Prefixing fixes the first finite prefix bit. -/
theorem boundaryPrefix_prefixBit_zero (n : ℕ) (b : Bool) (x : (ℕ → Bool)) :
    boundaryPrefix (n + 1) (prefixBit b x) ⟨0, Nat.succ_pos n⟩ = b := by
  rfl

/-- The tail of the finite prefix after front-prefixing is the old prefix. -/
theorem boundaryPrefix_prefixBit_succ
    {n : ℕ} (b : Bool) (x : (ℕ → Bool)) (i : Fin n) :
    boundaryPrefix (n + 1) (prefixBit b x) ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ =
      boundaryPrefix n x i := by
  rfl

theorem boundaryPrefix_prefixBit
    (n : ℕ) (b : Bool) (x : (ℕ → Bool)) :
    boundaryPrefix (n + 1) (prefixBit b x) =
      Fin.cons b (boundaryPrefix n x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem projectiveProjection_prefixBit
    (n : ℕ) (b : Bool) (x : (ℕ → Bool)) :
    PrefixProjectiveLimit.π (n + 1)
        (PrefixProjectiveLimit.ofCantor (prefixBit b x)) =
      Fin.cons b
        (PrefixProjectiveLimit.π n
          (PrefixProjectiveLimit.ofCantor x)) := by
  change boundaryPrefix (n + 1) (prefixBit b x) =
    Fin.cons b (boundaryPrefix n x)
  exact boundaryPrefix_prefixBit n b x

theorem projectiveProjection_prefixBit_nested
    (n : ℕ) (a b : Bool) (x : (ℕ → Bool)) :
    PrefixProjectiveLimit.π (n + 2)
        (PrefixProjectiveLimit.ofCantor
          (prefixBit a (prefixBit b x))) =
      Fin.cons a (Fin.cons b
        (PrefixProjectiveLimit.π n
          (PrefixProjectiveLimit.ofCantor x))) := by
  rw [projectiveProjection_prefixBit (n + 1) a (prefixBit b x),
    projectiveProjection_prefixBit n b x]

/-! ## Stage-local branch extension compatible with UHF cylinders -/

/--
Insert the next finite-stage branch bit at depth `n`.

This is not the same as front-prefixing.  It is the operation compatible with
the existing UHF owner, where `diagEmbedSucc` duplicates a stage-`n` observable
over the newly added last bit.
-/
def appendBitAtDepth (n : ℕ) (b : Bool) (x : (ℕ → Bool)) : (ℕ → Bool) :=
  fun k => if k < n then x k else if k = n then b else x k

def appendBitAtDepthProjective
    (n : ℕ) (b : Bool)
    (p : PrefixProjectiveLimit) : PrefixProjectiveLimit :=
  PrefixProjectiveLimit.ofCantor
    (appendBitAtDepth n b (PrefixProjectiveLimit.toCantor p))

theorem appendBitAtDepthProjective_projection_le
    {m n : ℕ} (hmn : m ≤ n) (b : Bool)
    (p : PrefixProjectiveLimit) :
    PrefixProjectiveLimit.π m
        (appendBitAtDepthProjective n b p) =
      PrefixProjectiveLimit.π m p := by
  apply funext
  intro i
  have hi : i.1 < n := lt_of_lt_of_le i.2 hmn
  simpa [appendBitAtDepthProjective, PrefixProjectiveLimit.π,
    PrefixProjectiveLimit.ofCantor, boundaryPrefix, appendBitAtDepth, hi] using
    congrFun (PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word p m) i

theorem appendBitAtDepthProjective_projection_succ
    (n : ℕ) (b : Bool) (p : PrefixProjectiveLimit) :
    PrefixProjectiveLimit.π (n + 1)
        (appendBitAtDepthProjective n b p) =
      extendSucc n (PrefixProjectiveLimit.π n p) b := by
  apply funext
  intro i
  by_cases hi : i.1 < n
  · have hcoord := congrFun
        (PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word p n)
        ⟨i.1, hi⟩
    simpa [appendBitAtDepthProjective, PrefixProjectiveLimit.π,
      PrefixProjectiveLimit.ofCantor, boundaryPrefix, appendBitAtDepth,
      extendSucc, hi] using hcoord
  · have hle : n ≤ i.1 := Nat.le_of_not_gt hi
    have hEq : i = ⟨n, Nat.lt_succ_self n⟩ := by
      apply Fin.ext
      exact Nat.le_antisymm (Nat.lt_succ_iff.mp i.2) hle
    subst i
    simp [appendBitAtDepthProjective, PrefixProjectiveLimit.π,
      PrefixProjectiveLimit.ofCantor, boundaryPrefix, appendBitAtDepth,
      extendSucc]

theorem appendBitAtDepthProjective_toCantor_self
    (n : ℕ) (b : Bool) (p : PrefixProjectiveLimit) :
    PrefixProjectiveLimit.toCantor
        (appendBitAtDepthProjective n b p) n = b := by
  have hproj := congrArg
    (fun w : BitWord (n + 1) => w ⟨n, Nat.lt_succ_self n⟩)
    (appendBitAtDepthProjective_projection_succ n b p)
  simpa [PrefixProjectiveLimit.π, PrefixProjectiveLimit.toCantor,
    boundaryPrefix, extendSucc] using hproj

theorem continuous_appendBitAtDepth (n : ℕ) (b : Bool) :
    Continuous (appendBitAtDepth n b) := by
  apply continuous_pi
  intro k
  by_cases hlt : k < n
  · simpa [appendBitAtDepth, hlt] using
      (continuous_apply k : Continuous (fun x : (ℕ → Bool) => x k))
  · by_cases heq : k = n
    · subst k
      simpa [appendBitAtDepth] using
        (continuous_const : Continuous (fun _ : (ℕ → Bool) => b))
    · simpa [appendBitAtDepth, hlt, heq] using
        (continuous_apply k : Continuous (fun x : (ℕ → Bool) => x k))

theorem continuous_appendBitAtDepthProjective (n : ℕ) (b : Bool) :
    Continuous (appendBitAtDepthProjective n b) := by
  simpa [appendBitAtDepthProjective] using
    PrefixProjectiveLimit.continuous_ofCantor.comp
      ((continuous_appendBitAtDepth n b).comp
        PrefixProjectiveLimit.continuous_toCantor)

def appendLeftAtDepth (n : ℕ) (x : (ℕ → Bool)) : (ℕ → Bool) :=
  appendBitAtDepth n false x

theorem continuous_appendLeftAtDepth (n : ℕ) :
    Continuous (appendLeftAtDepth n) := by
  exact continuous_appendBitAtDepth n false

def appendRightAtDepth (n : ℕ) (x : (ℕ → Bool)) : (ℕ → Bool) :=
  appendBitAtDepth n true x

theorem continuous_appendRightAtDepth (n : ℕ) :
    Continuous (appendRightAtDepth n) := by
  exact continuous_appendBitAtDepth n true

@[simp] theorem appendBitAtDepth_of_lt
    {n k : ℕ} (hk : k < n) (b : Bool) (x : (ℕ → Bool)) :
    appendBitAtDepth n b x k = x k := by
  simp [appendBitAtDepth, hk]

@[simp] theorem appendBitAtDepth_self (n : ℕ) (b : Bool) (x : (ℕ → Bool)) :
    appendBitAtDepth n b x n = b := by
  simp [appendBitAtDepth]

@[simp] theorem appendBitAtDepth_of_gt
    {n k : ℕ} (hk : n < k) (b : Bool) (x : (ℕ → Bool)) :
    appendBitAtDepth n b x k = x k := by
  simp [appendBitAtDepth, Nat.not_lt_of_ge (Nat.le_of_lt hk), Nat.ne_of_gt hk]

theorem appendBitAtDepth_reconstruct
    (n : ℕ) (x : (ℕ → Bool)) :
    appendBitAtDepth n (x n) x = x := by
  funext k
  by_cases hk : k < n
  · simp [appendBitAtDepth, hk]
  · by_cases hkn : k = n
    · subst k
      simp [appendBitAtDepth]
    · have hnk : n < k := by omega
      simp [appendBitAtDepth, hk, hkn]

theorem appendBitAtDepth_eq_iff
    {n : ℕ} {a b : Bool} {x y : (ℕ → Bool)} :
    appendBitAtDepth n a x = appendBitAtDepth n b y ↔
      a = b ∧ ∀ k, k ≠ n → x k = y k := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hn := congrFun h n
      simpa [appendBitAtDepth] using hn
    · intro k hk
      by_cases hlt : k < n
      · have hk' := congrFun h k
        simpa [appendBitAtDepth, hlt] using hk'
      · have hgt : n < k := by omega
        have hk' := congrFun h k
        simpa [appendBitAtDepth, hlt, hk] using hk'
  · rintro ⟨hab, hxy⟩
    funext k
    by_cases hlt : k < n
    · simpa [appendBitAtDepth, hlt] using hxy k (Nat.ne_of_lt hlt)
    · by_cases hkn : k = n
      · subst k
        simp [appendBitAtDepth, hab]
      · have hgt : n < k := by omega
        simp [appendBitAtDepth, hlt, hkn, hxy k hkn]

theorem appendBitAtDepth_eq_self_iff
    (n : ℕ) (b : Bool) (x : (ℕ → Bool)) :
    appendBitAtDepth n b x = x ↔ x n = b := by
  constructor
  · intro h
    have hn := congrFun h n
    simpa [appendBitAtDepth] using hn.symm
  · intro hx
    simpa [hx] using appendBitAtDepth_reconstruct n x

theorem appendBitAtDepth_comm_of_ne
    {n m : ℕ} (hnm : n ≠ m) (a b : Bool) (x : (ℕ → Bool)) :
    appendBitAtDepth n a (appendBitAtDepth m b x) =
      appendBitAtDepth m b (appendBitAtDepth n a x) := by
  funext k
  by_cases hkn : k = n
  · subst k
    simp [appendBitAtDepth, hnm]
  · by_cases hkm : k = m
    · subst k
      simp [appendBitAtDepth, Ne.symm hnm]
    · by_cases hknlt : k < n <;>
        by_cases hkm_lt : k < m <;>
          simp [appendBitAtDepth, hkn, hkm, hknlt, hkm_lt]

theorem appendBitAtDepth_overwrite
    (n : ℕ) (a b : Bool) (x : (ℕ → Bool)) :
    appendBitAtDepth n a (appendBitAtDepth n b x) =
      appendBitAtDepth n a x := by
  funext k
  by_cases hkn : k < n
  · simp [appendBitAtDepth, hkn]
  · by_cases hkeq : k = n
    · subst k
      simp [appendBitAtDepth]
    · have hnk : n < k := by omega
      simp [appendBitAtDepth, hkn, hkeq]

theorem appendBitAtDepthProjective_reconstruct
    (n : ℕ) (p : PrefixProjectiveLimit) :
    appendBitAtDepthProjective n
        (PrefixProjectiveLimit.toCantor p n) p = p := by
  apply PrefixProjectiveLimit.ext
  funext k
  rw [← PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word
      (appendBitAtDepthProjective n
        (PrefixProjectiveLimit.toCantor p n) p) k,
    ← PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word p k]
  simpa [appendBitAtDepthProjective,
    PrefixProjectiveLimit.toCantor_ofCantor] using
    congrArg (boundaryPrefix k)
      (appendBitAtDepth_reconstruct n (PrefixProjectiveLimit.toCantor p))

theorem appendBitAtDepthProjective_overwrite
    (n : ℕ) (a b : Bool) (p : PrefixProjectiveLimit) :
    appendBitAtDepthProjective n a
        (appendBitAtDepthProjective n b p) =
      appendBitAtDepthProjective n a p := by
  apply PrefixProjectiveLimit.ext
  funext k
  rw [← PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word
      (appendBitAtDepthProjective n a
        (appendBitAtDepthProjective n b p)) k,
    ← PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word
      (appendBitAtDepthProjective n a p) k]
  simpa [appendBitAtDepthProjective,
    PrefixProjectiveLimit.toCantor_ofCantor] using
    congrArg (boundaryPrefix k)
      (appendBitAtDepth_overwrite n a b (PrefixProjectiveLimit.toCantor p))

theorem appendBitAtDepthProjective_comm_of_ne
    {n m : ℕ} (hnm : n ≠ m) (a b : Bool)
    (p : PrefixProjectiveLimit) :
    appendBitAtDepthProjective n a
        (appendBitAtDepthProjective m b p) =
      appendBitAtDepthProjective m b
        (appendBitAtDepthProjective n a p) := by
  apply PrefixProjectiveLimit.ext
  funext k
  rw [← PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word
      (appendBitAtDepthProjective n a
        (appendBitAtDepthProjective m b p)) k,
    ← PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word
      (appendBitAtDepthProjective m b
        (appendBitAtDepthProjective n a p)) k]
  simpa [appendBitAtDepthProjective,
    PrefixProjectiveLimit.toCantor_ofCantor] using
    congrArg (boundaryPrefix k)
      (appendBitAtDepth_comm_of_ne hnm a b
        (PrefixProjectiveLimit.toCantor p))

theorem appendBitAtDepthProjective_range_cover
    (n : ℕ) (p : PrefixProjectiveLimit) :
    (∃ q, appendBitAtDepthProjective n false q = p) ∨
      ∃ q, appendBitAtDepthProjective n true q = p := by
  cases h : PrefixProjectiveLimit.toCantor p n with
  | false =>
      left
      refine ⟨p, ?_⟩
      simpa [h] using appendBitAtDepthProjective_reconstruct n p
  | true =>
      right
      refine ⟨p, ?_⟩
      simpa [h] using appendBitAtDepthProjective_reconstruct n p

theorem appendBitAtDepthProjective_false_ne_true
    (n : ℕ) (p q : PrefixProjectiveLimit) :
    appendBitAtDepthProjective n false p ≠
      appendBitAtDepthProjective n true q := by
  intro h
  have hproj := congrArg
    (PrefixProjectiveLimit.π (n + 1)) h
  have hlast := congrFun hproj ⟨n, Nat.lt_succ_self n⟩
  rw [appendBitAtDepthProjective_projection_succ,
    appendBitAtDepthProjective_projection_succ] at hlast
  simpa [extendSucc] using hlast

theorem appendBitAtDepthProjective_eq_iff
    {n : ℕ} {a b : Bool} {p q : PrefixProjectiveLimit} :
    appendBitAtDepthProjective n a p =
        appendBitAtDepthProjective n b q ↔
      a = b ∧ ∀ k, k ≠ n →
        PrefixProjectiveLimit.toCantor p k =
          PrefixProjectiveLimit.toCantor q k := by
  constructor
  · intro h
    have hstream := congrArg PrefixProjectiveLimit.toCantor h
    have hstream' :
        appendBitAtDepth n a (PrefixProjectiveLimit.toCantor p) =
          appendBitAtDepth n b (PrefixProjectiveLimit.toCantor q) := by
      simpa [appendBitAtDepthProjective,
        PrefixProjectiveLimit.toCantor_ofCantor] using hstream
    exact (appendBitAtDepth_eq_iff).1 hstream'
  · rintro ⟨hab, hrest⟩
    have hstream :
        appendBitAtDepth n a (PrefixProjectiveLimit.toCantor p) =
          appendBitAtDepth n b (PrefixProjectiveLimit.toCantor q) :=
      (appendBitAtDepth_eq_iff).2 ⟨hab, hrest⟩
    have hto :
        PrefixProjectiveLimit.toCantor
            (appendBitAtDepthProjective n a p) =
          PrefixProjectiveLimit.toCantor
            (appendBitAtDepthProjective n b q) := by
      simpa [appendBitAtDepthProjective,
        PrefixProjectiveLimit.toCantor_ofCantor] using hstream
    exact PrefixProjectiveLimit.cantorEquivPrefixProjectiveLimit.symm.injective hto

theorem appendBitAtDepthProjective_eq_self_iff
    (n : ℕ) (b : Bool) (p : PrefixProjectiveLimit) :
    appendBitAtDepthProjective n b p = p ↔
      PrefixProjectiveLimit.toCantor p n = b := by
  constructor
  · intro h
    have hproj := congrArg (PrefixProjectiveLimit.π (n + 1)) h
    have hlast := congrFun hproj ⟨n, Nat.lt_succ_self n⟩
    rw [appendBitAtDepthProjective_projection_succ] at hlast
    simpa [extendSucc, PrefixProjectiveLimit.toCantor,
      boundaryPrefix] using hlast.symm
  · intro h
    simpa [h] using appendBitAtDepthProjective_reconstruct n p

theorem appendBitAtDepthProjective_range_eq
    (n : ℕ) (b : Bool) :
    Set.range (appendBitAtDepthProjective n b) =
      {p : PrefixProjectiveLimit |
        PrefixProjectiveLimit.toCantor p n = b} := by
  ext p
  change (∃ q, appendBitAtDepthProjective n b q = p) ↔
    PrefixProjectiveLimit.toCantor p n = b
  constructor
  · rintro ⟨q, rfl⟩
    exact appendBitAtDepthProjective_toCantor_self n b q
  · intro hp
    exact ⟨p, (appendBitAtDepthProjective_eq_self_iff n b p).2 hp⟩

theorem appendBitAtDepthProjective_fixedPoint_set_eq_range
    (n : ℕ) (b : Bool) :
    {p : PrefixProjectiveLimit |
        appendBitAtDepthProjective n b p = p} =
      Set.range (appendBitAtDepthProjective n b) := by
  ext p
  change appendBitAtDepthProjective n b p = p ↔
    p ∈ Set.range (appendBitAtDepthProjective n b)
  rw [appendBitAtDepthProjective_eq_self_iff,
    appendBitAtDepthProjective_range_eq]
  rfl

theorem appendBitAtDepthProjective_range_isClopen
    (n : ℕ) (b : Bool) :
    IsClopen (Set.range (appendBitAtDepthProjective n b)) := by
  rw [appendBitAtDepthProjective_range_eq]
  let hcont : Continuous
      (fun p : PrefixProjectiveLimit =>
        PrefixProjectiveLimit.toCantor p n) :=
    (continuous_apply n).comp PrefixProjectiveLimit.continuous_toCantor
  exact ⟨
    IsClosed.preimage hcont (isClosed_discrete ({b} : Set Bool)),
    IsOpen.preimage hcont (isOpen_discrete ({b} : Set Bool))⟩

theorem appendBitAtDepthProjective_range_union
    (n : ℕ) :
    Set.range (appendBitAtDepthProjective n false) ∪
        Set.range (appendBitAtDepthProjective n true) =
      Set.univ := by
  ext p
  constructor
  · intro hp
    trivial
  · intro hp
    rcases appendBitAtDepthProjective_range_cover n p with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem appendBitAtDepthProjective_range_inter_eq_empty
    (n : ℕ) :
    Set.range (appendBitAtDepthProjective n false) ∩
        Set.range (appendBitAtDepthProjective n true) =
      (∅ : Set PrefixProjectiveLimit) := by
  ext p
  constructor
  · rintro ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
    exact False.elim
      (appendBitAtDepthProjective_false_ne_true n q r
        (hq.trans hr.symm))
  · simp

theorem appendBitAtDepth_range_cover
    (n : ℕ) (x : (ℕ → Bool)) :
    (∃ y, appendBitAtDepth n false y = x) ∨
      ∃ y, appendBitAtDepth n true y = x := by
  cases h : x n with
  | false =>
      left
      exact ⟨x, by simpa [h] using appendBitAtDepth_reconstruct n x⟩
  | true =>
      right
      exact ⟨x, by simpa [h] using appendBitAtDepth_reconstruct n x⟩

theorem appendBitAtDepth_left_right_disjoint
    (n : ℕ) (x y : (ℕ → Bool)) :
    appendBitAtDepth n false x ≠ appendBitAtDepth n true y := by
  intro h
  have hn := congrFun h n
  simp [appendBitAtDepth] at hn

theorem appendBitAtDepth_range_eq (n : ℕ) (b : Bool) :
    Set.range (appendBitAtDepth n b) = {x : (ℕ → Bool) | x n = b} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [appendBitAtDepth]
  · intro hx
    refine ⟨x, ?_⟩
    rw [← hx]
    exact appendBitAtDepth_reconstruct n x

theorem appendBitAtDepth_range_eq_coordinate_preimage (n : ℕ) (b : Bool) :
    Set.range (appendBitAtDepth n b) =
      (fun x : (ℕ → Bool) => x n) ⁻¹' ({b} : Set Bool) := by
  rw [appendBitAtDepth_range_eq]
  rfl

theorem appendBitAtDepth_range_isClopen (n : ℕ) (b : Bool) :
    IsClopen (Set.range (appendBitAtDepth n b)) := by
  rw [appendBitAtDepth_range_eq_coordinate_preimage]
  exact ⟨IsClosed.preimage (continuous_apply n)
      (isClosed_discrete ({b} : Set Bool)),
    IsOpen.preimage (continuous_apply n)
      (isOpen_discrete ({b} : Set Bool))⟩

theorem appendBitAtDepth_range_union (n : ℕ) :
    Set.range (appendBitAtDepth n false) ∪
        Set.range (appendBitAtDepth n true) =
      Set.univ := by
  rw [appendBitAtDepth_range_eq, appendBitAtDepth_range_eq]
  ext x
  cases h : x n <;> simp [h]

theorem appendBitAtDepth_fixedPoint_set_eq_range
    (n : ℕ) (b : Bool) :
    {x : (ℕ → Bool) | appendBitAtDepth n b x = x} =
      Set.range (appendBitAtDepth n b) := by
  ext x
  change appendBitAtDepth n b x = x ↔ x ∈ Set.range (appendBitAtDepth n b)
  rw [appendBitAtDepth_eq_self_iff, appendBitAtDepth_range_eq]
  rfl

theorem appendBitAtDepth_false_ne_true
    (n : ℕ) (x y : (ℕ → Bool)) :
    appendBitAtDepth n false x ≠ appendBitAtDepth n true y := by
  intro h
  have hhead := congrFun h n
  simp at hhead

theorem appendBitAtDepth_idempotent
    (n : ℕ) (b : Bool) (x : (ℕ → Bool)) :
    appendBitAtDepth n b (appendBitAtDepth n b x) =
      appendBitAtDepth n b x := by
  have h := appendBitAtDepth_reconstruct n (appendBitAtDepth n b x)
  simpa using h

theorem appendBitAtDepth_comm_of_lt
    {m n : ℕ} (hmn : m < n) (b c : Bool) (x : (ℕ → Bool)) :
    appendBitAtDepth m b (appendBitAtDepth n c x) =
      appendBitAtDepth n c (appendBitAtDepth m b x) := by
  funext k
  by_cases hkm : k < m
  · simp [appendBitAtDepth, hkm, lt_trans hkm hmn]
  · by_cases hkm_eq : k = m
    · subst k
      simp [appendBitAtDepth, hmn]
    · by_cases hkn : k < n
      · simp [appendBitAtDepth, hkm, hkm_eq, hkn]
      · by_cases hkn_eq : k = n
        · subst k
          have hnm : n ≠ m := Ne.symm (Nat.ne_of_lt hmn)
          simp [appendBitAtDepth, hnm]
        · simp [appendBitAtDepth, hkm, hkm_eq, hkn, hkn_eq]

/--
The first `n+1` bits of the stage-local branch are exactly the finite word
obtained by extending the first `n` bits with the new branch bit.
-/
theorem boundaryPrefix_appendBitAtDepth_succ
    (n : ℕ) (b : Bool) (x : (ℕ → Bool)) :
    boundaryPrefix (n + 1) (appendBitAtDepth n b x) =
      extendSucc n (boundaryPrefix n x) b := by
  ext i
  unfold boundaryPrefix appendBitAtDepth extendSucc
  by_cases hi : i.1 < n
  · simp [hi]
  · have hin : i.1 = n := by omega
    simp [hin]

/--
Stage-local left/right branches are compatible with the diagonal UHF successor
embedding.
-/
theorem cylinder_diagEmbedSucc_appendBitAtDepth
    (n : ℕ) (b : Bool) (f : DiagAlg n) (x : (ℕ → Bool)) :
    cylinder (n + 1) (diagEmbedSucc n f) (appendBitAtDepth n b x) =
      cylinder n f x := by
  unfold cylinder
  rw [boundaryPrefix_appendBitAtDepth_succ, diagEmbedSucc_apply,
    prefixSucc_extendSucc]

theorem cylinder_diagEmbedSucc_appendLeftAtDepth
    (n : ℕ) (f : DiagAlg n) (x : (ℕ → Bool)) :
    cylinder (n + 1) (diagEmbedSucc n f) (appendLeftAtDepth n x) =
      cylinder n f x := by
  exact cylinder_diagEmbedSucc_appendBitAtDepth n false f x

theorem cylinder_diagEmbedSucc_appendRightAtDepth
    (n : ℕ) (f : DiagAlg n) (x : (ℕ → Bool)) :
    cylinder (n + 1) (diagEmbedSucc n f) (appendRightAtDepth n x) =
      cylinder n f x := by
  exact cylinder_diagEmbedSucc_appendBitAtDepth n true f x

theorem isCompact_prefixBit_range (b : Bool) :
    IsCompact (Set.range (prefixBit b)) := by
  exact (isClosed_prefixBit_range b).isCompact

theorem isCompact_appendBitAtDepth_range (n : ℕ) (b : Bool) :
    IsCompact (Set.range (appendBitAtDepth n b)) := by
  exact (appendBitAtDepth_range_isClopen n b).1.isCompact

theorem isCompact_appendBitAtDepthProjective_range (n : ℕ) (b : Bool) :
    IsCompact (Set.range (appendBitAtDepthProjective n b)) := by
  exact (appendBitAtDepthProjective_range_isClopen n b).isClosed.isCompact

end InfoGeometry.Canonical.CantorBoundaryCuntzShift

end noncomputable section
