import Mathlib.Tactic
import InfoGeometry.Canonical.StoneBridgeMathlib
import InfoGeometry.Canonical.StoneCantorMathlib
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.CantorBoundaryCuntzShift

/-!
# Boolean UHF projections and the Cantor Bratteli path space

This is the theorem-safe Stone/Bratteli bridge for the diagonal Boolean
projection lattice of the `2^∞` UHF skeleton already present in
`UHFInductiveColimitBoundary`.

The key point is not a new analytic C*-completion theorem.  The closed Lean
content is the exact inverse-limit identification:

* finite stages are binary words `Fin n → Bool`;
* bonding maps are prefix restrictions `prefixSucc`;
* coherent finite paths are equivalent to infinite binary Cantor words;
* atom/cylinder projections are idempotent and read the corresponding Cantor
  prefix.

This is the algebraic Stone-duality/Bratteli path-space core needed by the
MDPAS-to-Cantor bridge.

#### BUCKET 1: CLOSED FINITE THEOREMS
Finite Boolean cylinder operations, finite `Bool` evaluations, prefix-pullback
compatibility, Bratteli coherent path/Cantor boundary equivalence, and the
order-theoretic ultrafilter/Boolean-homomorphism equivalence for powersets.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`CantorStoneUltrafilter` assumes unique finite cylinder atoms at every depth;
from that property it reconstructs a coherent Cantor boundary point.

#### BUCKET 3: OPEN CLOSURE DEBT
No analytic C*-completion, compact Hausdorff classification, or full MDPA Stone
duality is claimed here.  This file proves the finite/profinite Boolean spine
used by those later layers.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryCuntzShift

/-- Boolean-valued diagonal projections at stage `n`. -/
def BooleanProjection (n : ℕ) : Type :=
  {p : DiagAlg n // ∀ w : BitWord n, p w * p w = p w}

/-- Atomic Boolean projection corresponding to one finite Bratteli vertex. -/
def atomProjection (n : ℕ) (w : BitWord n) : DiagAlg n :=
  fun v => if v = w then 1 else 0

/-- Atomic diagonal projections are idempotent. -/
theorem atomProjection_idempotent (n : ℕ) (w : BitWord n) :
    ∀ v : BitWord n, atomProjection n w v * atomProjection n w v = atomProjection n w v := by
  intro v
  by_cases h : v = w <;> simp [atomProjection, h]

theorem atomProjection_mul_of_ne
    (n : ℕ) {w₁ w₂ : BitWord n} (h : w₁ ≠ w₂) (v : BitWord n) :
    atomProjection n w₁ v * atomProjection n w₂ v = 0 := by
  have h' : w₂ ≠ w₁ := Ne.symm h
  by_cases h₁ : v = w₁ <;> by_cases h₂ : v = w₂ <;>
    simp [atomProjection, h₁, h₂, h, h']

theorem atomProjection_sum_univ (n : ℕ) (v : BitWord n) :
    ∑ w : BitWord n, atomProjection n w v = 1 := by
  classical
  simp [atomProjection]

/-- Atomic projections as elements of the finite Boolean projection lattice. -/
def atomBooleanProjection (n : ℕ) (w : BitWord n) : BooleanProjection n :=
  ⟨atomProjection n w, atomProjection_idempotent n w⟩

/-- The atom indexed by the boundary prefix evaluates to one on that boundary point. -/
theorem cylinder_atom_boundaryPrefix_self (n : ℕ) (x : (ℕ → Bool)) :
    cylinder n (atomProjection n (boundaryPrefix n x)) x = 1 := by
  simp [cylinder, atomProjection]

/-- An atom evaluates to zero away from its prefix cylinder. -/
theorem cylinder_atom_eq_zero_of_prefix_ne
    (n : ℕ) (w : BitWord n) (x : (ℕ → Bool))
    (h : boundaryPrefix n x ≠ w) :
    cylinder n (atomProjection n w) x = 0 := by
  simp [cylinder, atomProjection, h]

/-- Coherent paths through the binary Bratteli diagram of finite UHF projections. -/
structure CoherentBitPath where
  word : ∀ n : ℕ, BitWord n
  coherent : ∀ n : ℕ, prefixSucc n (word (n + 1)) = word n

/-- A Cantor boundary point determines a coherent family of finite prefixes. -/
def boundaryToCoherentPath (x : (ℕ → Bool)) : CoherentBitPath where
  word := fun n => boundaryPrefix n x
  coherent := fun n => boundaryPrefix_succ_eq_prefixSucc n x

/-- A coherent Bratteli path determines an infinite Cantor word by reading the new bit at each level. -/
def coherentPathToBoundary (p : CoherentBitPath) : (ℕ → Bool) :=
  fun n => p.word (n + 1) ⟨n, Nat.lt_succ_self n⟩

/-- Values in a coherent path are stable when passing to deeper levels. -/
theorem coherent_value_eq_terminal
    (p : CoherentBitPath) {i n : ℕ} (hi : i < n) :
    p.word n ⟨i, hi⟩ = p.word (i + 1) ⟨i, Nat.lt_succ_self i⟩ := by
  induction n with
  | zero => exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
      by_cases hin : i < n
      · have hstep : p.word (n + 1) ⟨i, Nat.lt_trans hin (Nat.lt_succ_self n)⟩ =
            p.word n ⟨i, hin⟩ := by
          have h := congrFun (p.coherent n) ⟨i, hin⟩
          simpa [prefixSucc] using h
        calc
          p.word (n + 1) ⟨i, hi⟩ =
              p.word (n + 1) ⟨i, Nat.lt_trans hin (Nat.lt_succ_self n)⟩ := by rfl
          _ = p.word n ⟨i, hin⟩ := hstep
          _ = p.word (i + 1) ⟨i, Nat.lt_succ_self i⟩ := ih hin
      · have hge : n ≤ i := Nat.le_of_not_gt hin
        have hle : i ≤ n := Nat.le_of_lt_succ hi
        have hin_eq : i = n := Nat.le_antisymm hle hge
        subst hin_eq
        rfl

/-- Reconstructing finite prefixes from the boundary associated to a coherent path. -/
theorem boundaryPrefix_coherentPathToBoundary (p : CoherentBitPath) (n : ℕ) :
    boundaryPrefix n (coherentPathToBoundary p) = p.word n := by
  ext i
  simp [boundaryPrefix, coherentPathToBoundary]
  exact (coherent_value_eq_terminal p i.2).symm

/-- Cantor boundary to Bratteli path and back is the identity. -/
theorem coherentPathToBoundary_boundaryToCoherentPath (x : (ℕ → Bool)) :
    coherentPathToBoundary (boundaryToCoherentPath x) = x := by
  funext n
  rfl

/-- Bratteli path to Cantor boundary and back is the identity. -/
theorem boundaryToCoherentPath_coherentPathToBoundary (p : CoherentBitPath) :
    boundaryToCoherentPath (coherentPathToBoundary p) = p := by
  cases p with
  | mk word coherent =>
      simp only [boundaryToCoherentPath]
      congr
      funext n
      exact boundaryPrefix_coherentPathToBoundary ⟨word, coherent⟩ n

/-- The Boolean-projection Bratteli path space is equivalent to the Cantor boundary. -/
def coherentPathEquivCantorBoundary : CoherentBitPath ≃ (ℕ → Bool) where
  toFun := coherentPathToBoundary
  invFun := boundaryToCoherentPath
  left_inv := boundaryToCoherentPath_coherentPathToBoundary
  right_inv := coherentPathToBoundary_boundaryToCoherentPath

/-- The Witt/UHF Boolean bits at depth `n` are exactly the first `n` Cantor bits. -/
theorem witt_bits_eq_cantor_prefix (p : CoherentBitPath) (n : ℕ) :
    boundaryPrefix n (coherentPathEquivCantorBoundary p) = p.word n :=
  boundaryPrefix_coherentPathToBoundary p n

/-- A Cantor boundary point is recovered from all of its finite UHF Boolean projection bits. -/
theorem cantor_boundary_ext_of_all_witt_bits
    {x y : (ℕ → Bool)}
    (h : ∀ n : ℕ, boundaryPrefix n x = boundaryPrefix n y) :
    x = y := by
  funext n
  have hn := congrFun (h (n + 1)) ⟨n, Nat.lt_succ_self n⟩
  exact hn

/-! ## Boolean algebra / Stone-side cylinder readout -/

/-- Boolean algebra of finite subsets of Bratteli vertices at depth `n`. -/
abbrev FiniteBooleanAlgebra (n : ℕ) := Set (BitWord n)

/-- Pull a Boolean event at depth `n` back along the prefix map from depth `n+1`. -/
def prefixPullback (n : ℕ) (A : FiniteBooleanAlgebra n) : FiniteBooleanAlgebra (n + 1) :=
  {w | prefixSucc n w ∈ A}

/-- Cantor cylinder determined by a finite Boolean event. -/
def cantorCylinder (n : ℕ) (A : FiniteBooleanAlgebra n) : Set (ℕ → Bool) :=
  {x | boundaryPrefix n x ∈ A}

@[simp] theorem mem_cantorCylinder (n : ℕ) (A : FiniteBooleanAlgebra n) (x : (ℕ → Bool)) :
    x ∈ cantorCylinder n A ↔ boundaryPrefix n x ∈ A :=
  Iff.rfl

/-- Stone contravariance: successor pullback on finite Boolean algebras gives the same Cantor cylinder. -/
theorem cantorCylinder_prefixPullback (n : ℕ) (A : FiniteBooleanAlgebra n) :
    cantorCylinder (n + 1) (prefixPullback n A) = cantorCylinder n A := by
  ext x
  simp [cantorCylinder, prefixPullback, boundaryPrefix_succ_eq_prefixSucc]

/-- Cylinder realization preserves finite Boolean union. -/
theorem cantorCylinder_union (n : ℕ) (A B : FiniteBooleanAlgebra n) :
    cantorCylinder n (A ∪ B) = cantorCylinder n A ∪ cantorCylinder n B := by
  ext x
  rfl

/-- Cylinder realization preserves finite Boolean intersection. -/
theorem cantorCylinder_inter (n : ℕ) (A B : FiniteBooleanAlgebra n) :
    cantorCylinder n (A ∩ B) = cantorCylinder n A ∩ cantorCylinder n B := by
  ext x
  rfl

/-- Cylinder realization preserves finite Boolean complement. -/
theorem cantorCylinder_compl (n : ℕ) (A : FiniteBooleanAlgebra n) :
    cantorCylinder n Aᶜ = (cantorCylinder n A)ᶜ := by
  ext x
  rfl

/-- The principal Stone ultrafilter at a Cantor point, stage by stage. -/
def pointStoneFilter (x : (ℕ → Bool)) (n : ℕ) : Set (FiniteBooleanAlgebra n) :=
  {A | boundaryPrefix n x ∈ A}

/-- Point ultrafilters are compatible with the Boolean-algebra pullback maps. -/
theorem pointStoneFilter_prefixPullback
    (x : (ℕ → Bool)) (n : ℕ) (A : FiniteBooleanAlgebra n) :
    prefixPullback n A ∈ pointStoneFilter x (n + 1) ↔ A ∈ pointStoneFilter x n := by
  simp [pointStoneFilter, prefixPullback, boundaryPrefix_succ_eq_prefixSucc]

/-! ### Finite Stone evaluation into the two-element Boolean algebra -/

/-- Evaluation of a finite Boolean cylinder event at one finite Bratteli word. -/
def boolEvalAt (n : ℕ) (w : BitWord n) (A : FiniteBooleanAlgebra n) : Bool :=
  by
    classical
    exact if w ∈ A then true else false

@[simp] theorem boolEvalAt_eq_true_iff
    (n : ℕ) (w : BitWord n) (A : FiniteBooleanAlgebra n) :
    boolEvalAt n w A = true ↔ w ∈ A := by
  classical
  by_cases h : w ∈ A <;> simp [boolEvalAt, h]

@[simp] theorem boolEvalAt_empty (n : ℕ) (w : BitWord n) :
    boolEvalAt n w (∅ : FiniteBooleanAlgebra n) = false := by
  classical
  simp [boolEvalAt]

@[simp] theorem boolEvalAt_univ (n : ℕ) (w : BitWord n) :
    boolEvalAt n w (Set.univ : FiniteBooleanAlgebra n) = true := by
  classical
  simp [boolEvalAt]

/-- Finite Stone evaluation preserves Boolean intersection. -/
theorem boolEvalAt_inter
    (n : ℕ) (w : BitWord n) (A B : FiniteBooleanAlgebra n) :
    boolEvalAt n w (A ∩ B) = (boolEvalAt n w A && boolEvalAt n w B) := by
  classical
  by_cases hA : w ∈ A <;> by_cases hB : w ∈ B <;> simp [boolEvalAt, hA, hB]

/-- Finite Stone evaluation preserves Boolean union. -/
theorem boolEvalAt_union
    (n : ℕ) (w : BitWord n) (A B : FiniteBooleanAlgebra n) :
    boolEvalAt n w (A ∪ B) = (boolEvalAt n w A || boolEvalAt n w B) := by
  classical
  by_cases hA : w ∈ A <;> by_cases hB : w ∈ B <;> simp [boolEvalAt, hA, hB]

/-- Finite Stone evaluation preserves Boolean complement. -/
theorem boolEvalAt_compl
    (n : ℕ) (w : BitWord n) (A : FiniteBooleanAlgebra n) :
    boolEvalAt n w Aᶜ = !(boolEvalAt n w A) := by
  classical
  by_cases hA : w ∈ A
  · have hc : w ∉ Aᶜ := by simpa using hA
    simp [boolEvalAt, hA, hc]
  · have hc : w ∈ Aᶜ := by simpa using hA
    simp [boolEvalAt, hA, hc]

/-- A Cantor boundary point evaluates every finite Boolean cylinder event to a bit. -/
def cantorBooleanEvaluation (x : (ℕ → Bool)) (n : ℕ) :
    FiniteBooleanAlgebra n → Bool :=
  boolEvalAt n (boundaryPrefix n x)

/-- The Cantor evaluation is exactly the principal Stone filter membership test. -/
theorem cantorBooleanEvaluation_eq_true_iff_pointStoneFilter
    (x : (ℕ → Bool)) (n : ℕ) (A : FiniteBooleanAlgebra n) :
    cantorBooleanEvaluation x n A = true ↔ A ∈ pointStoneFilter x n := by
  simp [cantorBooleanEvaluation, pointStoneFilter]

/-- Cantor Boolean evaluation is compatible with the finite prefix bonding maps. -/
theorem cantorBooleanEvaluation_prefixPullback
    (x : (ℕ → Bool)) (n : ℕ) (A : FiniteBooleanAlgebra n) :
    cantorBooleanEvaluation x (n + 1) (prefixPullback n A) =
      cantorBooleanEvaluation x n A := by
  classical
  by_cases h : boundaryPrefix n x ∈ A
  · have hs : boundaryPrefix (n + 1) x ∈ prefixPullback n A := by
      simpa [prefixPullback, boundaryPrefix_succ_eq_prefixSucc] using h
    simp [cantorBooleanEvaluation, boolEvalAt, h, hs]
  · have hs : boundaryPrefix (n + 1) x ∉ prefixPullback n A := by
      simpa [prefixPullback, boundaryPrefix_succ_eq_prefixSucc] using h
    simp [cantorBooleanEvaluation, boolEvalAt, h, hs]

/-! ### Finite exact-rational Bayesian states on cylinder events -/

/-- A finite exact-rational Bayesian state on the depth-`n` Boolean cylinder algebra. -/
structure FiniteBayesianState (n : ℕ) where
  weight : BitWord n → ℚ
  nonnegative : ∀ w, 0 ≤ weight w
  normalized : (∑ w, weight w) = 1

namespace FiniteBayesianState

/-- Exact mass assigned by a finite Bayesian state to a Boolean cylinder event. -/
def eventMass {n : ℕ} (P : FiniteBayesianState n) (A : FiniteBooleanAlgebra n) : ℚ :=
  by
    classical
    exact ∑ w, if h : w ∈ A then P.weight w else 0

theorem eventMass_empty {n : ℕ} (P : FiniteBayesianState n) :
    P.eventMass (∅ : FiniteBooleanAlgebra n) = 0 := by
  classical
  simp [eventMass]

theorem eventMass_univ {n : ℕ} (P : FiniteBayesianState n) :
    P.eventMass (Set.univ : FiniteBooleanAlgebra n) = 1 := by
  classical
  simp [eventMass, P.normalized]

theorem eventMass_nonnegative {n : ℕ}
    (P : FiniteBayesianState n) (A : FiniteBooleanAlgebra n) :
    0 ≤ P.eventMass A := by
  classical
  unfold eventMass
  exact Finset.sum_nonneg (fun w _ => by
    by_cases hw : w ∈ A
    · simp [hw, P.nonnegative w]
    · simp [hw])

theorem eventMass_union_of_disjoint {n : ℕ}
    (P : FiniteBayesianState n)
    (A B : FiniteBooleanAlgebra n)
    (hAB : Disjoint A B) :
    P.eventMass (A ∪ B) = P.eventMass A + P.eventMass B := by
  classical
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hA : w ∈ A <;> by_cases hB : w ∈ B
  · exact (Set.disjoint_left.mp hAB hA hB).elim
  · simp [hA, hB]
  · simp [hA, hB]
  · simp [hA, hB]

/-- The mass of an atomic cylinder is the weight of its unique finite word. -/
theorem eventMass_singleton {n : ℕ}
    (P : FiniteBayesianState n) (w : BitWord n) :
    P.eventMass ({w} : FiniteBooleanAlgebra n) = P.weight w := by
  classical
  simp [eventMass]

/-- Exact Bayesian conditioning weight after observing a finite cylinder event. -/
def conditionedWeight {n : ℕ}
    (P : FiniteBayesianState n) (A : FiniteBooleanAlgebra n) (w : BitWord n) : ℚ :=
  by
    classical
    exact if h : w ∈ A then P.weight w / P.eventMass A else 0

theorem conditionedWeight_of_not_mem {n : ℕ}
    (P : FiniteBayesianState n) (A : FiniteBooleanAlgebra n) {w : BitWord n}
    (hw : w ∉ A) :
    P.conditionedWeight A w = 0 := by
  classical
  simp [conditionedWeight, hw]

theorem conditionedWeight_of_mem {n : ℕ}
    (P : FiniteBayesianState n) (A : FiniteBooleanAlgebra n) {w : BitWord n}
    (hw : w ∈ A) :
    P.conditionedWeight A w = P.weight w / P.eventMass A := by
  classical
    simp [conditionedWeight, hw]

theorem conditionedWeight_nonnegative {n : ℕ}
    (P : FiniteBayesianState n) (A : FiniteBooleanAlgebra n)
    (hA : P.eventMass A ≠ 0) (w : BitWord n) :
    0 ≤ P.conditionedWeight A w := by
  by_cases hw : w ∈ A
  · rw [conditionedWeight_of_mem P A hw]
    exact div_nonneg (P.nonnegative w)
      (le_of_lt (lt_of_le_of_ne (P.eventMass_nonnegative A)
        (Ne.symm hA)))
  · rw [conditionedWeight_of_not_mem P A hw]

theorem conditionedWeight_mul_eventMass_of_mem {n : ℕ}
    (P : FiniteBayesianState n) (A : FiniteBooleanAlgebra n)
    (hA : P.eventMass A ≠ 0) {w : BitWord n} (hw : w ∈ A) :
    P.conditionedWeight A w * P.eventMass A = P.weight w := by
  rw [conditionedWeight_of_mem P A hw]
  field_simp

/-- The post-conditioning mass assigned to the observed event. -/
def conditionedEventMass {n : ℕ}
    (P : FiniteBayesianState n) (A : FiniteBooleanAlgebra n) : ℚ :=
  by
    classical
    exact ∑ w, if h : w ∈ A then P.conditionedWeight A w else 0

/-- Conditioning normalizes the observed event to exact mass one when the event has nonzero mass. -/
theorem conditioned_eventMass_self {n : ℕ}
    (P : FiniteBayesianState n) (A : FiniteBooleanAlgebra n)
    (hA : P.eventMass A ≠ 0) :
    P.conditionedEventMass A = 1 := by
  classical
  have hsum :
      (∑ w, if h : w ∈ A then P.weight w / P.eventMass A else 0) =
        P.eventMass A / P.eventMass A := by
    have hpoint :
        (∑ w, if h : w ∈ A then P.weight w / P.eventMass A else 0) =
          (∑ w, (if h : w ∈ A then P.weight w else 0) / P.eventMass A) := by
      congr 1
      ext w
      by_cases hw : w ∈ A <;> simp [hw]
    have hdiv :
        (∑ w, (if h : w ∈ A then P.weight w else 0) / P.eventMass A) =
          (∑ w, if h : w ∈ A then P.weight w else 0) / P.eventMass A := by
      simpa using
        (Finset.sum_div (s := Finset.univ)
          (f := fun w : BitWord n => if h : w ∈ A then P.weight w else 0)
          (P.eventMass A)).symm
    calc
      (∑ w, if h : w ∈ A then P.weight w / P.eventMass A else 0)
          = (∑ w, (if h : w ∈ A then P.weight w else 0) / P.eventMass A) := hpoint
      _ = (∑ w, if w ∈ A then P.weight w else 0) / P.eventMass A := hdiv
      _ = P.eventMass A / P.eventMass A := by rfl
  calc
    P.conditionedEventMass A
        = (∑ w, if h : w ∈ A then P.weight w / P.eventMass A else 0) := by
            unfold conditionedEventMass
            congr 1
            ext w
            by_cases hw : w ∈ A <;> simp [conditionedWeight, hw]
    _ = P.eventMass A / P.eventMass A := hsum
    _ = 1 := div_self hA

/-- Successor consistency for exact finite prefix expectations. -/
def SuccessorConsistentExpectation (E : ∀ n : ℕ, BitWord n → ℚ) :
    Prop :=
  ∀ n (w : BitWord n),
    E n w =
      E (n + 1) (extendSucc n w false) +
        E (n + 1) (extendSucc n w true)

/--
Successor persistence for cylinder expectations: a cylinder expectation at
depth `n` is the sum of the expectations of its two depth-`n+1` successors.
-/
theorem successor_persistence_of_consistent_expectation
    (E : ∀ n : ℕ, BitWord n → ℚ)
    (hE : SuccessorConsistentExpectation E)
    (n : ℕ) (w : BitWord n) :
    E n w =
      E (n + 1) (extendSucc n w false) +
        E (n + 1) (extendSucc n w true) :=
  hE n w

/--
Finite Bayesian successor persistence: if a depth-`n` state is the prefix
pushforward of a depth-`n+1` state on atoms, then atomic cylinder mass persists
as the sum of the two successor atom masses.
-/
theorem successor_persistence_eventMass_singleton
    {n : ℕ}
    (Pn : FiniteBayesianState n) (Pnext : FiniteBayesianState (n + 1))
    (hpush : ∀ w : BitWord n,
      Pn.weight w =
        Pnext.weight (extendSucc n w false) +
          Pnext.weight (extendSucc n w true))
    (w : BitWord n) :
    Pn.eventMass ({w} : FiniteBooleanAlgebra n) =
      Pnext.eventMass ({extendSucc n w false} : FiniteBooleanAlgebra (n + 1)) +
        Pnext.eventMass ({extendSucc n w true} : FiniteBooleanAlgebra (n + 1)) := by
  rw [eventMass_singleton, eventMass_singleton, eventMass_singleton]
  exact hpush w

end FiniteBayesianState

/-- The finite Stone point at a prefix word is the principal ultrafilter on words. -/
noncomputable def pointStoneUltrafilter (x : (ℕ → Bool)) (n : ℕ) :
    Ultrafilter (BitWord n) :=
  pure (boundaryPrefix n x)

/-- Principal Stone ultrafilters on `BitWord n` are exactly the finite words. -/
noncomputable def finiteStoneSpectrumEquivBitWord (n : ℕ) :
    Ultrafilter (BitWord n) ≃ BitWord n where
  toFun u := Classical.choose (Ultrafilter.eq_pure_of_finite u)
  invFun w := pure w
  left_inv u := by
    exact (Classical.choose_spec (Ultrafilter.eq_pure_of_finite u)).symm
  right_inv w := by
    have h := Classical.choose_spec (Ultrafilter.eq_pure_of_finite (pure w))
    exact (Ultrafilter.pure_injective h).symm

/-- The Stone point at a Cantor boundary reads back the same prefix word. -/
theorem pointStoneUltrafilter_readback
    (x : (ℕ → Bool)) (n : ℕ) :
    finiteStoneSpectrumEquivBitWord n (pointStoneUltrafilter x n) =
      boundaryPrefix n x := by
  exact (finiteStoneSpectrumEquivBitWord n).right_inv (boundaryPrefix n x)

/-- Membership in the Stone point is exactly membership of the prefix word. -/
theorem pointStoneUltrafilter_mem_iff
    (x : (ℕ → Bool)) (n : ℕ) (A : FiniteBooleanAlgebra n) :
    A ∈ pointStoneUltrafilter x n ↔ boundaryPrefix n x ∈ A := by
  rfl

/-- The finite Stone spectrum is compatible with the UHF pullback maps. -/
theorem finiteStoneSpectrum_prefixPullback
    (x : (ℕ → Bool)) (n : ℕ) (A : FiniteBooleanAlgebra n) :
    A ∈ pointStoneUltrafilter x n ↔ prefixPullback n A ∈ pointStoneUltrafilter x (n + 1) := by
  simp [pointStoneUltrafilter, prefixPullback, boundaryPrefix_succ_eq_prefixSucc]

/-- Atomic cylinder sets are exactly prefix equality classes. -/
def atomCylinder (n : ℕ) (w : BitWord n) : Set (ℕ → Bool) :=
  cantorCylinder n {w}

@[simp] theorem mem_atomCylinder (n : ℕ) (w : BitWord n) (x : (ℕ → Bool)) :
    x ∈ atomCylinder n w ↔ boundaryPrefix n x = w := by
  simp [atomCylinder, cantorCylinder]

/-- Atomic cylinders separate Cantor boundary points. -/
theorem atomCylinders_separate_points {x y : (ℕ → Bool)}
    (h : ∀ n (w : BitWord n), x ∈ atomCylinder n w ↔ y ∈ atomCylinder n w) :
    x = y := by
  apply cantor_boundary_ext_of_all_witt_bits
  intro n
  apply Set.mem_singleton_iff.mp
  have hx : x ∈ atomCylinder n (boundaryPrefix n x) := by simp
  have hy : y ∈ atomCylinder n (boundaryPrefix n x) := (h n (boundaryPrefix n x)).mp hx
  exact ((mem_atomCylinder n (boundaryPrefix n x) y).mp hy).symm

/-! ## Mathlib ultrafilter / Stone layer on Cantor cylinders -/

/-- A Stone ultrafilter on the Cantor boundary whose finite cylinder atoms are unique at each depth. -/
structure CantorStoneUltrafilter where
  filter : Ultrafilter (ℕ → Bool)
  atom_exists_unique : ∀ n : ℕ, ∃! w : BitWord n, atomCylinder n w ∈ filter

namespace CantorStoneUltrafilter

/-- The principal Cantor Stone ultrafilter associated to a boundary point. -/
def principal (x : (ℕ → Bool)) : CantorStoneUltrafilter where
  filter := pure x
  atom_exists_unique := by
    intro n
    refine ⟨boundaryPrefix n x, ?_, ?_⟩
    · simp
    · intro w hw
      have h : boundaryPrefix n x = w := by
        simpa [Filter.mem_pure] using hw
      exact h.symm

/-- The unique finite atom selected by a Cantor Stone ultrafilter. -/
noncomputable def selectedWord (U : CantorStoneUltrafilter) (n : ℕ) : BitWord n :=
  Classical.choose (U.atom_exists_unique n)

theorem selectedWord_mem (U : CantorStoneUltrafilter) (n : ℕ) :
    atomCylinder n (U.selectedWord n) ∈ U.filter :=
  (Classical.choose_spec (U.atom_exists_unique n)).1

theorem selectedWord_unique (U : CantorStoneUltrafilter) (n : ℕ)
    {w : BitWord n} (hw : atomCylinder n w ∈ U.filter) :
    w = U.selectedWord n :=
  (Classical.choose_spec (U.atom_exists_unique n)).2 w hw

/-- A deeper atom lies inside the prefix atom one level up the Bratteli diagram. -/
theorem atomCylinder_subset_prefixSucc (n : ℕ) (w : BitWord (n + 1)) :
    atomCylinder (n + 1) w ⊆ atomCylinder n (prefixSucc n w) := by
  intro x hx
  rw [mem_atomCylinder] at hx ⊢
  rw [← boundaryPrefix_succ_eq_prefixSucc n x, hx]

/-- The selected atoms of a Stone ultrafilter form a coherent Bratteli path. -/
theorem selectedWord_coherent (U : CantorStoneUltrafilter) (n : ℕ) :
    prefixSucc n (U.selectedWord (n + 1)) = U.selectedWord n := by
  apply U.selectedWord_unique n
  exact Filter.mem_of_superset (U.selectedWord_mem (n + 1))
    (atomCylinder_subset_prefixSucc n (U.selectedWord (n + 1)))

/-- Convert a Cantor Stone ultrafilter to a coherent Bratteli path. -/
noncomputable def toCoherentPath (U : CantorStoneUltrafilter) : CoherentBitPath where
  word := U.selectedWord
  coherent := U.selectedWord_coherent

/-- Convert a Cantor Stone ultrafilter to its Cantor boundary point. -/
noncomputable def toBoundary (U : CantorStoneUltrafilter) : (ℕ → Bool) :=
  coherentPathToBoundary U.toCoherentPath

/-- The boundary extracted from a Stone ultrafilter has exactly the selected finite atoms. -/
theorem boundaryPrefix_toBoundary (U : CantorStoneUltrafilter) (n : ℕ) :
    boundaryPrefix n U.toBoundary = U.selectedWord n :=
  boundaryPrefix_coherentPathToBoundary U.toCoherentPath n

/-- Principal Stone ultrafilters recover the original Cantor boundary point. -/
theorem toBoundary_principal (x : (ℕ → Bool)) :
    (principal x).toBoundary = x := by
  apply cantor_boundary_ext_of_all_witt_bits
  intro n
  rw [boundaryPrefix_toBoundary]
  exact (selectedWord_unique (principal x) n (by simp [principal])).symm

/-- Every Stone ultrafilter contains the atom of its extracted boundary at each finite depth. -/
theorem atom_of_toBoundary_mem (U : CantorStoneUltrafilter) (n : ℕ) :
    atomCylinder n (boundaryPrefix n U.toBoundary) ∈ U.filter := by
  rw [boundaryPrefix_toBoundary]
  exact selectedWord_mem U n

/-- Stone ultrafilter atoms are exactly Cantor prefixes of the extracted boundary. -/
theorem atom_mem_iff_prefix_eq (U : CantorStoneUltrafilter) (n : ℕ) (w : BitWord n) :
    atomCylinder n w ∈ U.filter ↔ boundaryPrefix n U.toBoundary = w := by
  constructor
  · intro hw
    rw [boundaryPrefix_toBoundary]
    exact (U.selectedWord_unique n hw).symm
  · intro hw
    rw [← hw]
    exact atom_of_toBoundary_mem U n

/-- The Boolean evaluation induced by the finite atom selected by a Stone ultrafilter. -/
def stoneBooleanEvaluation (U : CantorStoneUltrafilter) (n : ℕ) :
    FiniteBooleanAlgebra n → Bool :=
  boolEvalAt n (U.selectedWord n)

/-- Stone evaluation at depth `n` is membership of the selected finite atom word. -/
theorem stoneBooleanEvaluation_eq_true_iff_selected
    (U : CantorStoneUltrafilter) (n : ℕ) (A : FiniteBooleanAlgebra n) :
    stoneBooleanEvaluation U n A = true ↔ U.selectedWord n ∈ A := by
  simp [stoneBooleanEvaluation]

/-- For atoms, Stone Boolean evaluation is exactly ultrafilter membership. -/
theorem stoneBooleanEvaluation_atom_iff
    (U : CantorStoneUltrafilter) (n : ℕ) (w : BitWord n) :
    stoneBooleanEvaluation U n ({w} : FiniteBooleanAlgebra n) = true ↔
      atomCylinder n w ∈ U.filter := by
  constructor
  · intro h
    have hw : U.selectedWord n = w := by
      simpa using
        (stoneBooleanEvaluation_eq_true_iff_selected U n ({w} : FiniteBooleanAlgebra n)).mp h
    rw [← hw]
    exact U.selectedWord_mem n
  · intro h
    have hw : w = U.selectedWord n := U.selectedWord_unique n h
    rw [hw]
    simp [stoneBooleanEvaluation, boolEvalAt]

/--
Finite Stone readout theorem: order-theoretic ultrafilters and Cantor points
both produce genuine Boolean evaluations into `Bool`, and atom evaluation
agrees with membership in the selected cylinder atom.
-/
theorem finite_stone_boolean_evaluation_layer :
    (∀ x n (A : FiniteBooleanAlgebra n),
        cantorBooleanEvaluation x n A = true ↔ A ∈ pointStoneFilter x n) ∧
      (∀ x n (A : FiniteBooleanAlgebra n),
        cantorBooleanEvaluation x (n + 1) (prefixPullback n A) =
          cantorBooleanEvaluation x n A) ∧
      (∀ U : CantorStoneUltrafilter, ∀ n w,
        stoneBooleanEvaluation U n ({w} : FiniteBooleanAlgebra n) = true ↔
          atomCylinder n w ∈ U.filter) := by
  exact ⟨cantorBooleanEvaluation_eq_true_iff_pointStoneFilter,
    cantorBooleanEvaluation_prefixPullback,
    stoneBooleanEvaluation_atom_iff⟩

end CantorStoneUltrafilter

/-- The real ultrafilter Stone layer recovers Cantor points from unique cylinder atoms. -/
theorem cantor_stone_ultrafilter_layer :
    (∀ x : (ℕ → Bool), (CantorStoneUltrafilter.principal x).toBoundary = x) ∧
      (∀ U : CantorStoneUltrafilter, ∀ n w,
        atomCylinder n w ∈ U.filter ↔ boundaryPrefix n U.toBoundary = w) := by
  exact ⟨CantorStoneUltrafilter.toBoundary_principal,
    CantorStoneUltrafilter.atom_mem_iff_prefix_eq⟩

/--
Owner-backed Rosetta data: the inverse limit of finite Boolean projection
vertices in the UHF Bratteli diagram is the established Cantor bitword carrier,
the finite Boolean projection algebra maps contravariantly to Cantor cylinders,
and the Stone ultrafilter layer recovers Cantor points from their atom filters.
-/
theorem boolean_projection_bratteli_path_space_is_cantor :
    (∀ p n,
      boundaryPrefix n (coherentPathEquivCantorBoundary p) = p.word n) ∧
      (∀ x : (ℕ → Bool),
        coherentPathEquivCantorBoundary (boundaryToCoherentPath x) = x) ∧
      (∀ n (A : FiniteBooleanAlgebra n),
        cantorCylinder (n + 1) (prefixPullback n A) = cantorCylinder n A) ∧
      (∀ x n (A : FiniteBooleanAlgebra n),
        cantorBooleanEvaluation x (n + 1) (prefixPullback n A) =
          cantorBooleanEvaluation x n A) ∧
      (∀ x : (ℕ → Bool),
        (CantorStoneUltrafilter.principal x).toBoundary = x) := by
  exact ⟨witt_bits_eq_cantor_prefix,
    coherentPathToBoundary_boundaryToCoherentPath,
    cantorCylinder_prefixPullback,
    cantorBooleanEvaluation_prefixPullback,
    CantorStoneUltrafilter.toBoundary_principal⟩

theorem cantorBooleanEvaluation_eq_false_iff_pointStoneFilter
    (x : (ℕ → Bool)) (n : ℕ) (A : FiniteBooleanAlgebra n) :
    cantorBooleanEvaluation x n A = false ↔
      A ∉ pointStoneFilter x n := by
  cases he : cantorBooleanEvaluation x n A with
  | false =>
      constructor
      · intro _ hmem
        have htrue :=
          (cantorBooleanEvaluation_eq_true_iff_pointStoneFilter x n A).mpr hmem
        rw [he] at htrue
        cases htrue
      · intro _
        simpa using he
  | true =>
      constructor
      · intro hfalse
        cases hfalse
      · intro hnot
        exfalso
        apply hnot
        exact
          (cantorBooleanEvaluation_eq_true_iff_pointStoneFilter x n A).mp he

end InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge

end noncomputable section
