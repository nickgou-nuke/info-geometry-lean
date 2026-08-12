import Mathlib.Tactic
import Mathlib.Topology.Homeomorph.Lemmas
import InfoGeometry.Canonical.CantorCylinderTopology
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# Cantor space as the projective limit of finite prefix spaces

A PR-shaped, domain-free projective-limit boundary for the binary Cantor stream.

The object formalized here is the concrete inverse-limit carrier of the finite
prefix spaces `Fin n → Bool` with bonding maps `prefixSucc`.  We prove it is
homeomorphic to the product Cantor stream `ℕ → Bool`.

This is deliberately not a physics statement and not a full Stone-duality/AF
C*-algebra theorem.  It is the canonical topological spine needed by those
layers.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimit

open scoped Topology
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-! Finite successor stages and their projective-limit bonding map. -/

/-- A binary word of length `n + 1` is its length-`n` prefix together with
the final bit. -/
def bitWordSuccEquiv (n : ℕ) :
    BitWord (n + 1) ≃ BitWord n × Bool where
  toFun w := (prefixSucc n w, w ⟨n, Nat.lt_succ_self n⟩)
  invFun p := extendSucc n p.1 p.2
  left_inv w := by
    funext i
    by_cases hi : i.1 < n
    · simp [prefixSucc, extendSucc, hi]
    · have hle : n ≤ i.1 := Nat.le_of_not_gt hi
      have hle' : i.1 ≤ n := Nat.lt_succ_iff.mp i.2
      have hEq : i.1 = n := Nat.le_antisymm hle' hle
      have hiEq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hEq
      subst i
      simp [extendSucc]
  right_inv p := by
    rcases p with ⟨w, b⟩
    apply Prod.ext
    · exact prefixSucc_extendSucc n w b
    · simp [extendSucc]

@[simp] theorem bitWordSuccEquiv_apply_prefix (n : ℕ) (w : BitWord (n + 1)) :
    (bitWordSuccEquiv n w).1 = prefixSucc n w := rfl

@[simp] theorem bitWordSuccEquiv_apply_last (n : ℕ) (w : BitWord (n + 1)) :
    (bitWordSuccEquiv n w).2 = w ⟨n, Nat.lt_succ_self n⟩ := rfl

/-- The finite binary tree grows by one independent terminal bit at each step. -/
theorem bitWord_card_succ (n : ℕ) :
    Fintype.card (BitWord (n + 1)) =
      Fintype.card (BitWord n) * Fintype.card Bool :=
  by
    simpa [Fintype.card_prod] using Fintype.card_congr (bitWordSuccEquiv n)

@[simp] theorem bitWord_card_succ_eq_two_mul (n : ℕ) :
    Fintype.card (BitWord (n + 1)) = 2 * Fintype.card (BitWord n) := by
  rw [bitWord_card_succ]
  simp [Nat.mul_comm]

theorem bitWord_card (n : ℕ) :
    Fintype.card (BitWord n) = 2 ^ n := by
  induction n with
  | zero => simp [UHFInductiveColimitBoundary.BitWord]
  | succ n ih =>
      rw [bitWord_card_succ_eq_two_mul, ih]
      simp [pow_succ, Nat.mul_comm]

/-- The concrete projective-limit carrier of the finite prefix spaces. -/
structure PrefixProjectiveLimit where
  word : ∀ n : ℕ, BitWord n
  coherent : ∀ n : ℕ, prefixSucc n (word (n + 1)) = word n

namespace PrefixProjectiveLimit

@[ext] theorem ext {p q : PrefixProjectiveLimit} (h : p.word = q.word) : p = q := by
  cases p
  cases q
  simp_all

instance : CoeFun PrefixProjectiveLimit (fun _ => ∀ n : ℕ, BitWord n) where
  coe p := p.word

/-- Projection to the `n`th finite prefix space. -/
def π (n : ℕ) (p : PrefixProjectiveLimit) : BitWord n :=
  p.word n

@[simp] theorem π_apply (n : ℕ) (p : PrefixProjectiveLimit) :
    π n p = p.word n := rfl

/-- Restriction of a finite binary word to an earlier prefix length. -/
def restrictPrefix {n m : ℕ} (h : n ≤ m) (w : BitWord m) : BitWord n :=
  fun i => w ⟨i.1, lt_of_lt_of_le i.2 h⟩

@[simp] theorem restrictPrefix_apply {n m : ℕ} (h : n ≤ m)
    (w : BitWord m) (i : Fin n) :
    restrictPrefix h w i = w ⟨i.1, lt_of_lt_of_le i.2 h⟩ := rfl

theorem ext_of_π_eq {p q : PrefixProjectiveLimit}
    (h : ∀ n : ℕ, π n p = π n q) : p = q := by
  apply PrefixProjectiveLimit.ext
  funext n
  exact h n

/-- The topology on the projective limit is the subspace topology inherited from
`∀ n, BitWord n`. -/
instance : TopologicalSpace PrefixProjectiveLimit :=
  TopologicalSpace.induced (fun p : PrefixProjectiveLimit => p.word) inferInstance

/-- The cone map from Cantor streams to coherent finite prefixes. -/
def ofCantor (x : (ℕ → Bool)) : PrefixProjectiveLimit where
  word := fun n => boundaryPrefix n x
  coherent := fun n => boundaryPrefix_succ_eq_prefixSucc n x

/-- Reconstruct a Cantor stream from a coherent family of finite prefixes. -/
def toCantor (p : PrefixProjectiveLimit) : (ℕ → Bool) :=
  fun k => p.word (k + 1) ⟨k, Nat.lt_succ_self k⟩

@[simp] theorem toCantor_ofCantor (x : (ℕ → Bool)) :
    toCantor (ofCantor x) = x := by
  ext k
  rfl

theorem ofCantor_const_false_ne_ofCantor_const_true :
    ofCantor (fun _ : ℕ => false) ≠
      ofCantor (fun _ : ℕ => true) := by
  intro h
  have hstream := congrArg toCantor h
  have hzero := congrFun hstream 0
  have hzero' : false = true := by
    simpa only [toCantor_ofCantor] using hzero
  cases hzero'

theorem boundaryPrefix_toCantor_eq_word (p : PrefixProjectiveLimit) (n : ℕ) :
    boundaryPrefix n (toCantor p) = p.word n := by
  induction n with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ m ih =>
      ext i
      by_cases hi : i.1 < m
      · have hcoh := congrFun (p.coherent m) ⟨i.1, hi⟩
        have hih := congrFun ih ⟨i.1, hi⟩
        simpa [boundaryPrefix, prefixSucc] using hih.trans hcoh.symm
      · cases i with
        | mk val hlt =>
            have hle : m ≤ val := Nat.le_of_not_gt (by simpa using hi)
            have hle' : val ≤ m := Nat.lt_succ_iff.mp hlt
            have heq : val = m := Nat.le_antisymm hle' hle
            subst heq
            simp [boundaryPrefix, toCantor]

@[simp] theorem ofCantor_toCantor (p : PrefixProjectiveLimit) :
    ofCantor (toCantor p) = p := by
  apply PrefixProjectiveLimit.ext
  funext n
  exact boundaryPrefix_toCantor_eq_word p n

/-- Type-level equivalence between Cantor streams and the prefix projective limit. -/
def cantorEquivPrefixProjectiveLimit : (ℕ → Bool) ≃ PrefixProjectiveLimit where
  toFun := ofCantor
  invFun := toCantor
  left_inv := toCantor_ofCantor
  right_inv := by intro p; exact ofCantor_toCantor p

/-- Each finite projection is continuous by construction of the induced topology. -/
theorem continuous_π (n : ℕ) : Continuous (π n) := by
  change Continuous (fun p : PrefixProjectiveLimit => p.word n)
  exact (continuous_apply n).comp continuous_induced_dom

theorem isClopen_projection_fiber (n : ℕ) (w : BitWord n) :
    IsOpen {p : PrefixProjectiveLimit | π n p = w} ∧
      IsClosed {p : PrefixProjectiveLimit | π n p = w} := by
  change IsOpen (π n ⁻¹' ({w} : Set (BitWord n))) ∧
    IsClosed (π n ⁻¹' ({w} : Set (BitWord n)))
  constructor
  · exact (continuous_π n).isOpen_preimage _ (isOpen_discrete _)
  · exact IsClosed.preimage (continuous_π n) (isClosed_discrete _)

/-- The cone map from Cantor streams to the projective-limit carrier is continuous. -/
theorem continuous_ofCantor : Continuous ofCantor := by
  rw [continuous_induced_rng]
  change Continuous (fun x : (ℕ → Bool) => fun n : ℕ => boundaryPrefix n x)
  exact continuous_pi fun n => by
    unfold boundaryPrefix
    continuity

/-- The reconstruction map from the projective-limit carrier to Cantor streams is continuous. -/
theorem continuous_toCantor : Continuous toCantor := by
  change Continuous (fun p : PrefixProjectiveLimit => fun k : ℕ => p.word (k + 1) ⟨k, Nat.lt_succ_self k⟩)
  exact continuous_pi fun k => by
    exact (continuous_apply ⟨k, Nat.lt_succ_self k⟩).comp (continuous_π (k + 1))

/-- Cantor space is homeomorphic to the concrete projective limit of finite prefix spaces. -/
def cantorHomeomorphPrefixProjectiveLimit : (ℕ → Bool) ≃ₜ PrefixProjectiveLimit where
  toEquiv := cantorEquivPrefixProjectiveLimit
  continuous_toFun := continuous_ofCantor
  continuous_invFun := continuous_toCantor

instance : CompactSpace PrefixProjectiveLimit := by
  letI : CompactSpace (ℕ → Bool) := ⟨isCompact_univ⟩
  exact cantorHomeomorphPrefixProjectiveLimit.compactSpace

instance : T2Space PrefixProjectiveLimit :=
  cantorHomeomorphPrefixProjectiveLimit.t2Space

/-- The `n`th projection of the homeomorphism is the ordinary boundary prefix. -/
theorem cantorHomeomorph_projection (x : (ℕ → Bool)) (n : ℕ) :
    π n (cantorHomeomorphPrefixProjectiveLimit x) = boundaryPrefix n x :=
  rfl

/-- The projective-limit coherence relation, exposed as a theorem. -/
theorem projection_coherent (p : PrefixProjectiveLimit) (n : ℕ) :
    prefixSucc n (π (n + 1) p) = π n p :=
  p.coherent n

theorem π_surjective (n : ℕ) :
    Function.Surjective (π n) := by
  intro w
  let x : ℕ → Bool := fun k =>
    if hk : k < n then w ⟨k, hk⟩ else false
  refine ⟨ofCantor x, ?_⟩
  change boundaryPrefix n x = w
  funext i
  simp [x, boundaryPrefix, i.2]

theorem projection_fiber_union (n : ℕ) :
    (⋃ w : BitWord n, {p : PrefixProjectiveLimit | π n p = w}) =
      Set.univ := by
  ext p
  simp

theorem projection_fiber_inter_eq_empty
    (n : ℕ) {w v : BitWord n} (hwv : w ≠ v) :
    {p : PrefixProjectiveLimit | π n p = w} ∩
        {p : PrefixProjectiveLimit | π n p = v} =
      (∅ : Set PrefixProjectiveLimit) := by
  ext p
  constructor
  · rintro ⟨hw, hv⟩
    exact False.elim (hwv (hw.symm.trans hv))
  · simp

theorem projection_eq_boundaryPrefix_toCantor
    (p : PrefixProjectiveLimit) (n : ℕ) :
    π n p = boundaryPrefix n (toCantor p) := by
  exact (boundaryPrefix_toCantor_eq_word p n).symm

theorem restrictPrefix_π {n m : ℕ} (p : PrefixProjectiveLimit) (h : n ≤ m) :
    restrictPrefix h (π m p) = π n p := by
  rw [projection_eq_boundaryPrefix_toCantor p m,
    projection_eq_boundaryPrefix_toCantor p n]
  funext i
  rfl

theorem restrictPrefix_comp {n m k : ℕ}
    (hnm : n ≤ m) (hmk : m ≤ k) (w : BitWord k) :
    restrictPrefix hnm (restrictPrefix hmk w) =
      restrictPrefix (le_trans hnm hmk) w := by
  funext i
  rfl

end PrefixProjectiveLimit

theorem ext_of_all_projections_eq
    {p q : PrefixProjectiveLimit}
    (h : ∀ n : ℕ, PrefixProjectiveLimit.π n p =
      PrefixProjectiveLimit.π n q) :
    p = q := by
  apply PrefixProjectiveLimit.ext
  funext n
  exact h n

end InfoGeometry.Canonical.CantorProjectiveLimit
