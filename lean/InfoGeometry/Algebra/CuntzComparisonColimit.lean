import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzGrothendieckCone
import InfoGeometry.Algebra.CuntzComparisonJiangSu

/-!
# Inductive Colimit Transfer of Cuntz Comparison and Jiang-Su Unperforation

This module proves that Cuntz comparison, quasitrace state families, and Jiang-Su
almost unperforation project functorially through directed inductive systems of
ordered commutative monoids.

In the Toms-Winter conjecture and the classification of nuclear C*-algebras,
stable domination in the Cuntz semigroup $Cu(A)$ is preserved under direct
inductive colimits $A = \varinjlim A_n$ (such as UHF and AF algebras).

Given a directed sequence of ordered commutative monoids $(S_n, \le_n)$ with order units
$u_n$ and order-preserving monoid homomorphisms $\iota_n : S_n \to S_{n+1}$ preserving the unit:

1. **State Pullback (`pullbackState`)**: Any normalized Cuntz state $\tau_{n+1}$ on $S_{n+1}$
   pulls back along $\iota_n$ to a genuine Cuntz state $\tau_n$ on $S_n$.
2. **Compatible State Families (`CompatibleStateFamily`)**: A coherent family of states
   satisfying $\tau_{n+1} \circ \iota_n = \tau_n$.
3. **Staged Iteration Compatibility (`tau_iota_seq`)**: Evaluating any compatible state family
   at stage $n+m$ on the $m$-step embedded element $\iota_{n, m}(x)$ is identically equal
   to its evaluation at stage $n$: $\tau_{n+m}(\iota_{n, m}(x)) = \tau_n(x)$.
4. **Grothendieck Cone Functoriality (`grothendieckCone_iota_seq`)**: Stable algebraic
   domination in $S_n$ implies stable algebraic domination at every subsequent stage $S_{n+m}$.
5. **Jiang-Su Unperforation Colimit Persistence (`almost_unperforated_colimit_persistent`)**:
   In an almost unperforated inductive system, any finite-stage scaling defect
   $(k+1)a \le kb$ persistently contracts into the Grothendieck cone at all future stages.
6. **Colimit Toms-Winter Strict Positivity (`colimit_toms_winter_positivity`)**: In any
   inductive tower admitting a compatible state family, the order unit sequence remains
   strictly positive ($\tau_n(u_n) = 1 > 0$) across the entire inductive hierarchy.
-/

namespace InfoGeometry.Algebra.CuntzComparisonColimit

open _root_.Algebra
open InfoGeometry.Algebra.CuntzGrothendieck
open InfoGeometry.Algebra.CuntzComparison

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- An inductive sequence of ordered commutative monoids with unit-preserving homomorphisms. -/
structure InductiveOrderedMonoid (S : ℕ → Type*)
    [∀ n, AddCommMonoid (S n)] [∀ n, PartialOrder (S n)] [∀ n, IsOrderedAddMonoid (S n)] where
  u : ∀ n, S n
  iota : ∀ n, S n → S (n + 1)
  iota_add : ∀ n (a b : S n), iota n (a + b) = iota n a + iota n b
  iota_mono : ∀ n (a b : S n), a ≤ b → iota n a ≤ iota n b
  iota_unit : ∀ n, iota n (u n) = u (n + 1)
  iota_zero : ∀ n, iota n 0 = 0

namespace InductiveOrderedMonoid

variable {S : ℕ → Type*}
variable [∀ n, AddCommMonoid (S n)] [∀ n, PartialOrder (S n)] [∀ n, IsOrderedAddMonoid (S n)]
variable (sys : InductiveOrderedMonoid S)

/-- Sequential iteration of the inductive embedding maps: $S_n \to S_{n+m}$. -/
def iota_seq (n : ℕ) : ∀ m : ℕ, S n → S (n + m)
  | 0, x => x
  | m + 1, x => sys.iota (n + m) (iota_seq n m x)

@[simp] theorem iota_seq_zero_step (n : ℕ) (x : S n) : sys.iota_seq n 0 x = x := rfl

@[simp] theorem iota_seq_succ_step (n m : ℕ) (x : S n) :
    sys.iota_seq n (m + 1) x = sys.iota (n + m) (sys.iota_seq n m x) := rfl

theorem iota_seq_add (n m : ℕ) (a b : S n) :
    sys.iota_seq n m (a + b) = sys.iota_seq n m a + sys.iota_seq n m b := by
  induction m with
  | zero => rfl
  | succ m ih =>
      dsimp [iota_seq]
      rw [ih, sys.iota_add]

theorem iota_seq_zero (n m : ℕ) :
    sys.iota_seq n m 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      dsimp [iota_seq]
      rw [ih, sys.iota_zero]

theorem iota_seq_mono (n m : ℕ) {a b : S n} (h : a ≤ b) :
    sys.iota_seq n m a ≤ sys.iota_seq n m b := by
  induction m with
  | zero => exact h
  | succ m ih =>
      dsimp [iota_seq]
      exact sys.iota_mono (n + m) _ _ ih

theorem iota_seq_unit (n m : ℕ) :
    sys.iota_seq n m (sys.u n) = sys.u (n + m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      dsimp [iota_seq]
      rw [ih]
      exact sys.iota_unit (n + m)

/-- Pullback of a normalized Cuntz state along an order-preserving unit-preserving homomorphism. -/
def pullbackState {n : ℕ} (τ : CuntzState (sys.u (n + 1))) : CuntzState (sys.u n) where
  toFun x := τ (sys.iota n x)
  map_add' a b := by
    rw [sys.iota_add, τ.map_add]
  monotone' a b h := by
    exact τ.monotone (sys.iota_mono n a b h)
  nonneg' a := τ.nonneg (sys.iota n a)
  normalized' := by
    rw [sys.iota_unit, τ.normalized]

@[simp] theorem pullbackState_apply {n : ℕ} (τ : CuntzState (sys.u (n + 1))) (x : S n) :
    sys.pullbackState τ x = τ (sys.iota n x) := rfl

end InductiveOrderedMonoid

variable {S : ℕ → Type*}
variable [∀ n, AddCommMonoid (S n)] [∀ n, PartialOrder (S n)] [∀ n, IsOrderedAddMonoid (S n)]
variable (sys : InductiveOrderedMonoid S)

/-- A coherent family of Cuntz states compatible with the inductive transition maps. -/
structure CompatibleStateFamily where
  state : ∀ n, CuntzState (sys.u n)
  coherent : ∀ n x, state (n + 1) (sys.iota n x) = state n x

/-- **Theorem: Inductive Colimit State Commutativity**
    Evaluating a compatible state family at stage $n+m$ on the $m$-step embedded element
    $\iota_{n, m}(x)$ is identically equal to evaluating the state at stage $n$:
    $\tau_{n+m}(\iota_{n, m}(x)) = \tau_n(x)$. -/
theorem tau_iota_seq (F : CompatibleStateFamily sys) (n m : ℕ) (x : S n) :
    F.state (n + m) (sys.iota_seq n m x) = F.state n x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      dsimp [InductiveOrderedMonoid.iota_seq]
      have hcoh := F.coherent (n + m) (sys.iota_seq n m x)
      change F.state (n + m + 1) (sys.iota (n + m) (sys.iota_seq n m x)) = F.state n x
      rw [hcoh, ih]

/-- **Theorem: Grothendieck Cone Functoriality under Inductive Embeddings**
    If $[b] - [a]$ lies in the Grothendieck cone of $S_n$, then for any $m \ge 0$,
    the embedded element $[\iota_{n,m}(b)] - [\iota_{n,m}(a)]$ lies in the Grothendieck cone of $S_{n+m}$. -/
theorem grothendieckCone_iota_seq (n m : ℕ) {a b : S n}
    (h : GrothendieckAddGroup.of b - GrothendieckAddGroup.of a ∈ (grothendieckCone (S := S n))) :
    GrothendieckAddGroup.of (sys.iota_seq n m b) - GrothendieckAddGroup.of (sys.iota_seq n m a) ∈
      (grothendieckCone (S := S (n + m))) := by
  rw [grothendieck_mem_cone_iff] at h ⊢
  rcases h with ⟨c, hc⟩
  refine ⟨sys.iota_seq n m c, ?_⟩
  have hmono := sys.iota_seq_mono n m hc
  rw [sys.iota_seq_add, sys.iota_seq_add] at hmono
  exact hmono

/-- **Theorem: Persistence of Jiang-Su Almost Unperforation along the Inductive Tower**
    In an almost unperforated inductive system, any finite-stage scaling defect
    $(k+1)a \le kb$ persistently contracts into the Grothendieck cone at all future stages. -/
theorem almost_unperforated_colimit_persistent
    (hunperf : ∀ n, IsAlmostUnperforated (S := S n))
    (n m k : ℕ) (a b : S n)
    (hscale : (k + 1) • a ≤ k • b) :
    GrothendieckAddGroup.of (sys.iota_seq n m b) - GrothendieckAddGroup.of (sys.iota_seq n m a) ∈
      (grothendieckCone (S := S (n + m))) := by
  have h_cone_n : GrothendieckAddGroup.of b - GrothendieckAddGroup.of a ∈ (grothendieckCone (S := S n)) :=
    almost_unperforated_mem_cone (hunperf n) k a b hscale
  exact grothendieckCone_iota_seq sys n m h_cone_n

/-- **Theorem: Colimit Toms-Winter Strict Positivity**
    In any inductive system admitting a compatible state family, the order unit sequence
    remains strictly positive ($\tau_n(u_n) = 1 > 0$) across the entire tower,
    guaranteeing that the inductive colimit order unit never collapses to zero. -/
theorem colimit_toms_winter_positivity
    (F : CompatibleStateFamily sys) (n m : ℕ) :
    0 < F.state (n + m) (sys.iota_seq n m (sys.u n)) := by
  rw [sys.iota_seq_unit n m]
  rw [(F.state (n + m)).normalized]
  exact zero_lt_one

/-- **Theorem: Colimit Domination Obstruction**
    The order unit sequence can never be stably dominated by zero at any stage in the colimit. -/
theorem colimit_order_unit_not_dominated_by_zero
    (F : CompatibleStateFamily sys) (n m : ℕ) :
    GrothendieckAddGroup.of (0 : S (n + m)) - GrothendieckAddGroup.of (sys.iota_seq n m (sys.u n)) ∉
      (grothendieckCone (S := S (n + m))) := by
  rw [sys.iota_seq_unit n m]
  intro hdom
  have hpos : 0 < F.state (n + m) (sys.u (n + m)) := by
    rw [(F.state (n + m)).normalized]
    exact zero_lt_one
  have hnonpos : F.state (n + m) (sys.u (n + m)) ≤ 0 := by
    rw [grothendieck_mem_cone_iff] at hdom
    rcases hdom with ⟨c, hc⟩
    rw [zero_add] at hc
    have hstate := (F.state (n + m)).monotone hc
    rw [(F.state (n + m)).map_add] at hstate
    linarith
  linarith

end InfoGeometry.Algebra.CuntzComparisonColimit
