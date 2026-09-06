import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

noncomputable section

namespace InfoGeometry.Canonical.ErlangenInductiveClosure

-- 1. Symmetry-Adapted Local Coordinates (The Invariant Packet)
/-- 
The invariant packet at a finite stage A_n. 
It captures the TKK Jordan/Lie triple data and the KKT block constraints.
-/
@[rep_depth transport]
structure SupergradedClosureAt (A : Type*) [Ring A] where
  -- Grading predicates (can be formalized via ZMod 2 grading classes)
  is_odd : A → Prop
  is_even : A → Prop
  is_central : A → Prop
  
  -- The Invariants
  odd_nilpotency : ∀ x, is_odd x → x * x = 0
  odd_odd_closure : ∀ x y, is_odd x → is_odd y → is_even (x * y + y * x)
  central_lane : ∀ c x, is_central c → c * x = x * c
  
  -- KKT/Projector Identity (e.g., Idempotents sum to 1, vacuum stability)
  projector_identity : ∃ P, is_even P ∧ P * P = P

-- 2. Local-to-Global Inductive Chain (The Intertwiner)
/-- 
A bonding map between stage A and stage B that acts as a symmetry-preserving 
intertwiner, guaranteeing the invariant packet survives the transition.
-/
@[rep_depth transport]
structure BondingIntertwiner {A B : Type*} [Ring A] [Ring B] 
    (invA : SupergradedClosureAt A) (invB : SupergradedClosureAt B) where
  -- The algebraic homomorphism
  map : A →+* B
  -- Functorial transport of the grading and constraints
  preserves_odd : ∀ x, invA.is_odd x → invB.is_odd (map x)
  preserves_even : ∀ x, invA.is_even x → invB.is_even (map x)
  preserves_central : ∀ c, invA.is_central c → invB.is_central (map c)

-- 3. The Inductive Stability Theorem
/-- 
The core inductive lemma schema: If stage n satisfies the invariant packet, 
and the bonding map is a valid intertwiner, the invariants transport exactly.
-/
@[rep_depth transport]
theorem invariant_transport_stable 
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedClosureAt A) 
    (invB : SupergradedClosureAt B)
    (f : BondingIntertwiner invA invB)
    (x : A) (hx : invA.is_odd x) : 
    (f.map x) * (f.map x) = 0 := by
  -- The proof is structurally trivial because the intertwiner respects the algebra
  have h_odd_map : invB.is_odd (f.map x) := f.preserves_odd x hx
  exact invB.odd_nilpotency (f.map x) h_odd_map

/--
The even closure also securely transports.
-/
@[rep_depth transport]
theorem invariant_transport_even_stable
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedClosureAt A)
    (invB : SupergradedClosureAt B)
    (f : BondingIntertwiner invA invB)
    (x y : A) (hx : invA.is_odd x) (hy : invA.is_odd y) :
    invB.is_even (f.map x * f.map y + f.map y * f.map x) := by
  have h_odd_x : invB.is_odd (f.map x) := f.preserves_odd x hx
  have h_odd_y : invB.is_odd (f.map y) := f.preserves_odd y hy
  exact invB.odd_odd_closure (f.map x) (f.map y) h_odd_x h_odd_y

/--
The central lane transports and remains central relative to the intertwiner's image.
-/
@[rep_depth transport]
theorem invariant_transport_central_stable
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedClosureAt A)
    (invB : SupergradedClosureAt B)
    (f : BondingIntertwiner invA invB)
    (c : A) (hc : invA.is_central c)
    (x : A) :
    f.map c * f.map x = f.map x * f.map c := by
  calc
    f.map c * f.map x = f.map (c * x) := by simp
    _ = f.map (x * c) := by rw [invA.central_lane c x hc]
    _ = f.map x * f.map c := by simp

-- 4. Langlands-Style Operator View (The Limit Hook)
/--
The colimit extraction is implemented by the algebraic direct limit of the
actual bonding homomorphisms. Its invariant predicates are finite-stage image
predicates, so closure is proved by moving finitely many representatives to a
common stage.
-/
def ColimitInheritsInvariants
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1))) : Type _ :=
  @SupergradedClosureAt
    (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.DirectLimitSuperClosure
      (fun n => (Bonding n).map))
    inferInstance

namespace ColimitInheritsInvariants

abbrev ColimitStage
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1))) :=
  InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.DirectLimitSuperClosure
    (fun n => (Bonding n).map)

abbrev colimitRing
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1))) :
    Ring (ColimitStage Chain Invariants Bonding) := inferInstance

def stageImage
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1)))
    (n : ℕ) : Chain n →+* ColimitStage Chain Invariants Bonding :=
  InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf
    (fun n => (Bonding n).map) n

def isOdd
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1)))
    (x : ColimitStage Chain Invariants Bonding) : Prop :=
  ∃ n a, stageImage Chain Invariants Bonding n a = x ∧ (Invariants n).is_odd a

def isEven
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1)))
    (x : ColimitStage Chain Invariants Bonding) : Prop :=
  ∃ n a, stageImage Chain Invariants Bonding n a = x ∧ (Invariants n).is_even a

def isCentral
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1)))
    (x : ColimitStage Chain Invariants Bonding) : Prop :=
  ∃ n a, stageImage Chain Invariants Bonding n a = x ∧ (Invariants n).is_central a

theorem stageImage_preserves
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1)))
    (which : ∀ n, Chain n → Prop)
    (preserves : ∀ n x, which n x → which (n + 1) ((Bonding n).map x))
    {n m : ℕ} (h : n ≤ m) {a : Chain n} (ha : which n a) :
    which m
      (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap
        (fun n => (Bonding n).map) n m h a) := by
  induction h with
  | refl => simpa using ha
  | @step m h ih =>
      rw [InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap_succ
        (fun n => (Bonding n).map) n m h]
      exact preserves m _ ih

def fromStages
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1))) :
    ColimitInheritsInvariants Chain Invariants Bonding := by
  let bond := fun n => (Bonding n).map
  let image := stageImage Chain Invariants Bonding
  let odd := isOdd Chain Invariants Bonding
  let even := isEven Chain Invariants Bonding
  let central := isCentral Chain Invariants Bonding
  have odd_preserves : ∀ n x, (Invariants n).is_odd x →
      (Invariants (n + 1)).is_odd ((Bonding n).map x) :=
    fun n x hx => (Bonding n).preserves_odd x hx
  have even_preserves : ∀ n x, (Invariants n).is_even x →
      (Invariants (n + 1)).is_even ((Bonding n).map x) :=
    fun n x hx => (Bonding n).preserves_even x hx
  have central_preserves : ∀ n x, (Invariants n).is_central x →
      (Invariants (n + 1)).is_central ((Bonding n).map x) :=
    fun n x hx => (Bonding n).preserves_central x hx
  refine { is_odd := odd, is_even := even, is_central := central, odd_nilpotency := ?_, odd_odd_closure := ?_, central_lane := ?_, projector_identity := ?_ }
  · intro x hx
    obtain ⟨n, a, rfl, ha⟩ := hx
    simpa only [map_mul, map_zero] using congrArg (image n) ((Invariants n).odd_nilpotency a ha)
  · intro x y hx hy
    obtain ⟨n, a, rfl, ha⟩ := hx
    obtain ⟨m, b, rfl, hb⟩ := hy
    let k := max n m
    let hnk : n ≤ k := le_max_left _ _
    let hmk : m ≤ k := le_max_right _ _
    let a' := InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap bond n k hnk a
    let b' := InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap bond m k hmk b
    refine ⟨k, a' * b' + b' * a', ?_, ?_⟩
    · change InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond k
          (a' * b' + b' * a') =
        InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond n a *
            InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond m b +
          InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond m b *
            InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond n a
      rw [← InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_bondMap bond n k hnk a]
      rw [← InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_bondMap bond m k hmk b]
      simpa only [map_add, map_mul, a', b']
    · exact (Invariants k).odd_odd_closure a' b'
        (stageImage_preserves Chain Invariants Bonding _ odd_preserves hnk ha)
        (stageImage_preserves Chain Invariants Bonding _ odd_preserves hmk hb)
  · intro c x hc
    obtain ⟨n, a, rfl, ha⟩ := hc
    refine Quotient.inductionOn x ?_
    intro xb
    rcases xb with ⟨m, b⟩
    let k := max n m
    let hnk : n ≤ k := le_max_left _ _
    let hmk : m ≤ k := le_max_right _ _
    let a' := InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap bond n k hnk a
    let b' := InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap bond m k hmk b
    change InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond n a *
        InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond m b =
      InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond m b *
        InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond n a
    rw [← InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_bondMap bond n k hnk a]
    rw [← InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_bondMap bond m k hmk b]
    simpa only [map_mul] using congrArg (stageImage Chain Invariants Bonding k)
      ((Invariants k).central_lane a' b'
        (stageImage_preserves Chain Invariants Bonding _ central_preserves hnk ha))
  · obtain ⟨p, hp, hpp⟩ := (Invariants 0).projector_identity
    exact ⟨image 0 p, ⟨0, p, rfl, hp⟩, by simpa using congrArg (image 0) hpp⟩

end ColimitInheritsInvariants

end InfoGeometry.Canonical.ErlangenInductiveClosure
