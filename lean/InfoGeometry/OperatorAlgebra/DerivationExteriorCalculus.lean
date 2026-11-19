/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.Cochain
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.DerivationLieLaneRepresentation
import InfoGeometry.Geometry.AssociativeGaugeConnection
import InfoGeometry.Algebra.NonAssocIteratedLeibniz
import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.NCG.NoncommutativeDifferentialCalculus
import InfoGeometry.NCG.NoncommutativeConnectionCurvature
import InfoGeometry.NCG.NoncommutativeCyclicCocycle
import InfoGeometry.NCG.DerivationDifferential
import InfoGeometry.Modular.ExactSequence
import InfoGeometry.Spectral.Cohomology.deRham
import InfoGeometry.Continuous.DeRhamBridge

/-!
# Arbitrary-degree noncommutative exterior calculus and unified Leibniz derivation spine

This module provides:

1. **Tier 1 — Faithfulness-free Lie-action exterior calculus (`LieActionLane R A`)**:
   `ActionOperatorForm K n := K.L [⋀^(Fin n)]→ₗ[R] A`, structural `reindexForm`,
   division-free `alternatingOfCurry`, Cartan Lie derivative `lieDeriv`, and the
   arbitrary-degree Chevalley--Eilenberg differential `actionExteriorDerivative`
   with `d_{n+1} ∘ d_n = 0` without faithfulness or multiplication on `A`.

2. **Tier 2 — Faithful quotient and range factorizations (`DerivationLieLane R A`)**:
   `fullDerivationLieLane`, `lieSubalgebraLane`, `lieActionToDerivationHom`,
   `rangeDerivationLieLane`, `quotientDerivationLieLane`, and `pullbackRangeForm`
   (injective and `(d_n, ∧)`-equivariant).

3. **Tier 3 — Unified Leibniz derivation adapters**:
   Adapters into `NonAssocDerivation.derivations R A`, `DerivationLieLane`, and
   `LieActionLane` for `AssociativeGaugeConnection.IsLeibniz`,
   `NonAssocIteratedLeibniz.IsDerivation`, `AlternativeDerivations.NonAssocDerivation`,
   `NCG.Calculus.NCDerivation`, `NCG.DerivationDifferential.LieSystem` (unconditionally
   via `rangeSubalgebra` without requiring `bracket_self`, and via `toLieActionLane`
   when `bracket_self` holds), `NCG.AlgebraDerivation`, `NCG.CyclicAlgebraDerivation`,
   and `Modular.ExactSequence.Derivation`.

4. **Arbitrary-degree noncommutative DGA (`DerivationOperatorForm K n`)**:
   `ceExteriorDerivative`, `ceWedge` / `ceWedgeBil`, associativity `ceWedge_assoc`,
   Cartan's `lieDeriv_ceWedge`, graded Leibniz `ceExteriorDerivative_ceWedge`,
   arbitrary-degree `covariantExteriorDerivativeN`, `ceCurvature`, Ricci identity
   `covariantExteriorDerivativeN_comp`, and Bianchi identity `ceCurvature_bianchi`.

5. **Commutative specialization (`[CommRing A]`)**:
   Graded commutativity `ceWedge_comm_of_commRing`, vanishing of `ceWedge ω ω` for
   1-forms, reduction of covariant exterior derivatives and curvature, `DifferentialForms`
   (`BUCKET 1`), `deRhamComplex` (`BUCKET 1` DGA + `BUCKET 2` metric/HK parameters),
   and pointwise `Chart α` alignment with Mathlib `extDeriv`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane

/-! ## Structural `Fin`-reindexing, `curryLeft` extensionality, and division-free uncurrying -/

section AlternatingHelpers

variable {R M N : Type*} [CommRing R]

/-- Reindex an alternating form along a propositional degree equality `m = n`. -/
def reindexForm [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {m n : ℕ} (h : m = n) (ω : M [⋀^Fin m]→ₗ[R] N) : M [⋀^Fin n]→ₗ[R] N :=
  ω.domDomCongr (finCongr h)

@[simp] theorem reindexForm_apply
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {m n : ℕ} (h : m = n) (ω : M [⋀^Fin m]→ₗ[R] N) (v : Fin n → M) :
    reindexForm h ω v = ω (v ∘ finCongr h) :=
  rfl

@[simp] theorem reindexForm_rfl
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {n : ℕ} (ω : M [⋀^Fin n]→ₗ[R] N) :
    reindexForm (rfl : n = n) ω = ω := by
  ext v
  rfl

theorem reindexForm_trans
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {m n k : ℕ} (h₁ : m = n) (h₂ : n = k) (ω : M [⋀^Fin m]→ₗ[R] N) :
    reindexForm h₂ (reindexForm h₁ ω) = reindexForm (h₁.trans h₂) ω := by
  subst h₁ h₂
  rfl

private theorem fun_comp_finCongr {α : Type*} {a b c : ℕ} (w : Fin c → α)
    (h1 : b = c) (h2 : a = b) :
    (w ∘ finCongr h1) ∘ finCongr h2 = w ∘ finCongr (h2.trans h1) := by
  subst h1 h2
  rfl

private theorem fun_comp_finCongr_rfl {α : Type*} {a : ℕ} (w : Fin a → α) (h : a = a) :
    w ∘ finCongr h = w := by
  ext i
  simp [finCongr]

@[simp] theorem reindexForm_zero
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {m n : ℕ} (h : m = n) :
    reindexForm h (0 : M [⋀^Fin m]→ₗ[R] N) = 0 := by
  ext v
  rfl

@[simp] theorem reindexForm_add
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {m n : ℕ} (h : m = n) (ω η : M [⋀^Fin m]→ₗ[R] N) :
    reindexForm h (ω + η) = reindexForm h ω + reindexForm h η := by
  ext v
  rfl

@[simp] theorem reindexForm_sub
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {m n : ℕ} (h : m = n) (ω η : M [⋀^Fin m]→ₗ[R] N) :
    reindexForm h (ω - η) = reindexForm h ω - reindexForm h η := by
  ext v
  rfl

@[simp] theorem reindexForm_neg
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {m n : ℕ} (h : m = n) (ω : M [⋀^Fin m]→ₗ[R] N) :
    reindexForm h (-ω) = -reindexForm h ω := by
  ext v
  rfl

@[simp] theorem reindexForm_smul
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {m n : ℕ} (h : m = n) (c : R) (ω : M [⋀^Fin m]→ₗ[R] N) :
    reindexForm h (c • ω) = c • reindexForm h ω := by
  ext v
  rfl

@[simp] theorem reindexForm_curryLeft
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {m n : ℕ} (h : m + 1 = n + 1) (ω : M [⋀^Fin (m + 1)]→ₗ[R] N) (x : M) :
    (reindexForm h ω).curryLeft x = reindexForm (Nat.succ.inj h) (ω.curryLeft x) := by
  ext w
  change ω (Matrix.vecCons x w ∘ finCongr h) = ω (Matrix.vecCons x (w ∘ finCongr (Nat.succ.inj h)))
  congr 1
  ext i
  cases i using Fin.cases with
  | zero => rfl
  | succ k => rfl

theorem reindexForm_eq_cast
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {m n : ℕ} (h : m = n) (ω : M [⋀^Fin m]→ₗ[R] N) :
    reindexForm h ω =
      cast (congrArg (fun k => M [⋀^Fin k]→ₗ[R] N) h) ω := by
  subst h
  rfl

theorem alternating_ext_curryLeft
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {n : ℕ} {f g : M [⋀^Fin (n + 1)]→ₗ[R] N}
    (h : ∀ x : M, f.curryLeft x = g.curryLeft x) : f = g := by
  ext v
  rw [← Fin.cons_self_tail v]
  exact AlternatingMap.congr_fun (h (v 0)) (Fin.tail v)

@[simp] theorem curryLeft_sub_helper
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {n : ℕ} (f g : M [⋀^Fin (n + 1)]→ₗ[R] N) (x : M) :
    (f - g).curryLeft x = f.curryLeft x - g.curryLeft x := by
  ext w
  rfl

@[simp] theorem curryLeft_neg_helper
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (x : M) :
    (-f).curryLeft x = -(f.curryLeft x) := by
  ext w
  rfl

/-- Division-free uncurrying of `f : M →ₗ[R] (M [⋀^Fin n]→ₗ[R] N)` whose
values vanish whenever the first argument repeats in the remaining `n` slots. -/
def alternatingOfCurry
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {n : ℕ} (f : M →ₗ[R] (M [⋀^Fin n]→ₗ[R] N))
    (hdiag : ∀ (x : M) (w : Fin n → M) (j : Fin n), w j = x → f x w = 0) :
    M [⋀^Fin (n + 1)]→ₗ[R] N where
  toFun v := f (v 0) (Fin.tail v)
  map_update_add' v i x y := by
    have hd : (‹DecidableEq (Fin (n + 1))›) = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    subst hd
    induction i using Fin.cases with
    | zero =>
      have htail : ∀ a : M, Fin.tail (Function.update v 0 a) = Fin.tail v := fun a =>
        funext fun k => by simp [Fin.tail, Fin.succ_ne_zero]
      simp only [Function.update_self, htail, map_add, AlternatingMap.add_apply]
    | succ k =>
      have htail : ∀ a : M, Fin.tail (Function.update v k.succ a) =
          Function.update (Fin.tail v) k a := fun a =>
        funext fun j => by
          by_cases hjk : j = k <;> simp [Fin.tail, hjk, Fin.succ_inj]
      simp only [Function.update_of_ne (Fin.succ_ne_zero k).symm, htail,
        AlternatingMap.map_update_add]
  map_update_smul' v i c x := by
    have hd : (‹DecidableEq (Fin (n + 1))›) = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    subst hd
    induction i using Fin.cases with
    | zero =>
      have htail : ∀ a : M, Fin.tail (Function.update v 0 a) = Fin.tail v := fun a =>
        funext fun k => by simp [Fin.tail, Fin.succ_ne_zero]
      simp only [Function.update_self, htail, map_smul, AlternatingMap.smul_apply]
    | succ k =>
      have htail : ∀ a : M, Fin.tail (Function.update v k.succ a) =
          Function.update (Fin.tail v) k a := fun a =>
        funext fun j => by
          by_cases hjk : j = k <;> simp [Fin.tail, hjk, Fin.succ_inj]
      simp only [Function.update_of_ne (Fin.succ_ne_zero k).symm, htail,
        AlternatingMap.map_update_smul]
  map_eq_zero_of_eq' v i j hv hij := by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ k => exact hdiag (v 0) (Fin.tail v) k hv.symm
    | succ k =>
      induction j using Fin.cases with
      | zero => exact hdiag (v 0) (Fin.tail v) k hv
      | succ l =>
        have hkl : k ≠ l := fun h => hij (by rw [h])
        exact (f (v 0)).map_eq_zero_of_eq (Fin.tail v) hv hkl

@[simp] theorem alternatingOfCurry_apply
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {n : ℕ} (f : M →ₗ[R] (M [⋀^Fin n]→ₗ[R] N))
    (hdiag : ∀ (x : M) (w : Fin n → M) (j : Fin n), w j = x → f x w = 0)
    (v : Fin (n + 1) → M) :
    alternatingOfCurry f hdiag v = f (v 0) (Fin.tail v) :=
  rfl

@[simp] theorem alternatingOfCurry_curryLeft
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {n : ℕ} (f : M →ₗ[R] (M [⋀^Fin n]→ₗ[R] N))
    (hdiag : ∀ (x : M) (w : Fin n → M) (j : Fin n), w j = x → f x w = 0)
    (x : M) :
    (alternatingOfCurry f hdiag).curryLeft x = f x := by
  ext w
  rfl

theorem diag_of_curryLeft_self
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {n : ℕ} (f : M →ₗ[R] (M [⋀^Fin n]→ₗ[R] N))
    (h : match n with
      | 0 => True
      | _ + 1 => ∀ x : M, (f x).curryLeft x = 0) :
    ∀ (x : M) (w : Fin n → M) (j : Fin n), w j = x → f x w = 0 := by
  cases n with
  | zero =>
    intro _ _ j
    exact j.elim0
  | succ m =>
    intro x w j hw
    induction j using Fin.cases with
    | zero =>
      have h0 : w = Matrix.vecCons x (Fin.tail w) := by
        rw [← hw]
        exact (Fin.cons_self_tail w).symm
      rw [h0]
      exact AlternatingMap.congr_fun (h x) (Fin.tail w)
    | succ k =>
      have hswap : (f x) (w ∘ Equiv.swap (0 : Fin (m + 1)) k.succ) = -(f x) w :=
        (f x).map_swap w (Fin.succ_ne_zero k).symm
      have h0 : (w ∘ Equiv.swap (0 : Fin (m + 1)) k.succ) 0 = x := by
        simp [Equiv.swap_apply_left, hw]
      have hzero : (f x) (w ∘ Equiv.swap (0 : Fin (m + 1)) k.succ) = 0 := by
        have hw' : w ∘ Equiv.swap (0 : Fin (m + 1)) k.succ =
            Matrix.vecCons x (Fin.tail (w ∘ Equiv.swap (0 : Fin (m + 1)) k.succ)) := by
          rw [← h0]
          exact (Fin.cons_self_tail _).symm
        rw [hw']
        exact AlternatingMap.congr_fun (h x) _
      rw [hzero] at hswap
      exact neg_eq_zero.mp hswap.symm

end AlternatingHelpers

/-! ## Tier 1: Faithfulness-free Lie-action exterior calculus (`LieActionLane R A`) -/

section Tier1_LieActionCalculus

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- Alternating `n`-forms valued in `A` over an arbitrary `LieActionLane R A`
(without requiring faithfulness or multiplication on `A`). -/
abbrev ActionOperatorForm (K : LieActionLane R A) (n : ℕ) :=
  K.L [⋀^(Fin n)]→ₗ[R] A

/-- Cartan Lie derivative of an alternating form along `x : K.L`. -/
def lieDeriv (K : LieActionLane R A) (x : K.L) {n : ℕ}
    (ω : ActionOperatorForm K n) : ActionOperatorForm K n where
  toFun v := K.operatorAction x (ω v) - ∑ i : Fin n, ω (Function.update v i ⁅x, v i⁆)
  map_update_add' v i y z := by
    have hd : (‹DecidableEq (Fin n)›) = instDecidableEqFin n := Subsingleton.elim _ _
    subst hd
    have hact : K.operatorAction x (ω (Function.update v i (y + z))) =
        K.operatorAction x (ω (Function.update v i y)) +
          K.operatorAction x (ω (Function.update v i z)) := by
      rw [ω.map_update_add, map_add]
    rw [hact]
    have hsum : (∑ j : Fin n, ω (Function.update (Function.update v i (y + z)) j
          ⁅x, Function.update v i (y + z) j⁆)) =
        (∑ j : Fin n, ω (Function.update (Function.update v i y) j
          ⁅x, Function.update v i y j⁆)) +
        (∑ j : Fin n, ω (Function.update (Function.update v i z) j
          ⁅x, Function.update v i z j⁆)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hji : j = i
      · subst hji
        simp only [Function.update_self, Function.update_idem, lie_add, ω.map_update_add]
      · simp only [Function.update_of_ne hji]
        rw [Function.update_comm (Ne.symm hji),
          Function.update_comm (Ne.symm hji) (a := i),
          Function.update_comm (Ne.symm hji) (a := i), ω.map_update_add]
    rw [hsum]
    abel
  map_update_smul' v i c y := by
    have hd : (‹DecidableEq (Fin n)›) = instDecidableEqFin n := Subsingleton.elim _ _
    subst hd
    have hact : K.operatorAction x (ω (Function.update v i (c • y))) =
        c • K.operatorAction x (ω (Function.update v i y)) := by
      rw [ω.map_update_smul, map_smul]
    rw [hact]
    have hsum : (∑ j : Fin n, ω (Function.update (Function.update v i (c • y)) j
          ⁅x, Function.update v i (c • y) j⁆)) =
        c • ∑ j : Fin n, ω (Function.update (Function.update v i y) j
          ⁅x, Function.update v i y j⁆) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hji : j = i
      · subst hji
        simp only [Function.update_self, Function.update_idem, lie_smul, ω.map_update_smul]
      · simp only [Function.update_of_ne hji]
        rw [Function.update_comm (Ne.symm hji),
          Function.update_comm (Ne.symm hji) (a := i), ω.map_update_smul]
    rw [hsum, ← smul_sub]
  map_eq_zero_of_eq' v a b hv hab := by
    have hω : ω v = 0 := ω.map_eq_zero_of_eq v hv hab
    rw [hω, map_zero, zero_sub]
    have hsum : (∑ j : Fin n, ω (Function.update v j ⁅x, v j⁆)) =
        ω (Function.update v a ⁅x, v a⁆) + ω (Function.update v b ⁅x, v b⁆) := by
      refine Fintype.sum_eq_add a b hab ?_
      intro j ⟨hja, hjb⟩
      exact ω.map_eq_zero_of_eq _ (by
        simp [Function.update_of_ne hja.symm, Function.update_of_ne hjb.symm]; exact hv) hab
    rw [hsum]
    have hswap : Function.update v b ⁅x, v b⁆ =
        (Function.update v a ⁅x, v a⁆) ∘ Equiv.swap a b := by
      ext j
      by_cases hja : j = a
      · subst hja
        simp [Equiv.swap_apply_left, Function.update_of_ne hab, Function.update_of_ne hab.symm, hv]
      · by_cases hjb : j = b
        · subst hjb
          simp [Equiv.swap_apply_right, hv]
        · simp [Equiv.swap_apply_of_ne_of_ne hja hjb,
            Function.update_of_ne hja, Function.update_of_ne hjb]
    rw [hswap, ω.map_swap _ hab]
    simp

@[simp] theorem lieDeriv_apply (K : LieActionLane R A) (x : K.L) {n : ℕ}
    (ω : ActionOperatorForm K n) (v : Fin n → K.L) :
    lieDeriv K x ω v =
      K.operatorAction x (ω v) - ∑ i : Fin n, ω (Function.update v i ⁅x, v i⁆) :=
  rfl

/-- `lieDeriv` as an `R`-bilinear map in `(x, ω)`. -/
def lieDerivLM (K : LieActionLane R A) {n : ℕ} :
    K.L →ₗ[R] ActionOperatorForm K n →ₗ[R] ActionOperatorForm K n where
  toFun x :=
    { toFun := lieDeriv K x
      map_add' := fun ω₁ ω₂ => by
        ext v
        simp only [lieDeriv_apply, AlternatingMap.add_apply, map_add, Finset.sum_add_distrib]
        abel
      map_smul' := fun c ω => by
        ext v
        simp only [lieDeriv_apply, AlternatingMap.smul_apply, map_smul, Finset.smul_sum,
          RingHom.id_apply, smul_sub] }
  map_add' x y := by
    ext ω v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, AlternatingMap.add_apply,
      lieDeriv_apply, map_add, add_lie]
    have hsum : (∑ i : Fin n, ω (Function.update v i (⁅x, v i⁆ + ⁅y, v i⁆))) =
        (∑ i : Fin n, ω (Function.update v i ⁅x, v i⁆)) +
        (∑ i : Fin n, ω (Function.update v i ⁅y, v i⁆)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ω.map_update_add v i _ _
    rw [hsum]
    abel
  map_smul' c x := by
    ext ω v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, AlternatingMap.smul_apply,
      lieDeriv_apply, map_smul, smul_lie, RingHom.id_apply]
    have hsum : (∑ i : Fin n, ω (Function.update v i (c • ⁅x, v i⁆))) =
        c • ∑ i : Fin n, ω (Function.update v i ⁅x, v i⁆) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ω.map_update_smul v i _ _
    rw [hsum, smul_sub]

@[simp] theorem lieDerivLM_apply (K : LieActionLane R A) {n : ℕ}
    (x : K.L) (ω : ActionOperatorForm K n) :
    lieDerivLM K x ω = lieDeriv K x ω :=
  rfl

@[simp] theorem lieDeriv_zero (K : LieActionLane R A) (x : K.L) {n : ℕ} :
    lieDeriv K x (0 : ActionOperatorForm K n) = 0 := by
  ext v
  simp

@[simp] theorem lieDeriv_add (K : LieActionLane R A) (x : K.L) {n : ℕ}
    (ω η : ActionOperatorForm K n) :
    lieDeriv K x (ω + η) = lieDeriv K x ω + lieDeriv K x η :=
  (lieDerivLM K x).map_add ω η

@[simp] theorem lieDeriv_sub (K : LieActionLane R A) (x : K.L) {n : ℕ}
    (ω η : ActionOperatorForm K n) :
    lieDeriv K x (ω - η) = lieDeriv K x ω - lieDeriv K x η :=
  (lieDerivLM K x).map_sub ω η

@[simp] theorem lieDeriv_neg (K : LieActionLane R A) (x : K.L) {n : ℕ}
    (ω : ActionOperatorForm K n) :
    lieDeriv K x (-ω) = -lieDeriv K x ω :=
  (lieDerivLM K x).map_neg ω

@[simp] theorem lieDeriv_smul (K : LieActionLane R A) (x : K.L) {n : ℕ}
    (c : R) (ω : ActionOperatorForm K n) :
    lieDeriv K x (c • ω) = c • lieDeriv K x ω :=
  (lieDerivLM K x).map_smul c ω

theorem lieDeriv_curryLeft (K : LieActionLane R A) (x y : K.L) {n : ℕ}
    (ω : ActionOperatorForm K (n + 1)) :
    (lieDeriv K x ω).curryLeft y =
      lieDeriv K x (ω.curryLeft y) - ω.curryLeft ⁅x, y⁆ := by
  ext w
  simp only [AlternatingMap.curryLeft_apply_apply, lieDeriv_apply, AlternatingMap.sub_apply]
  rw [Fin.sum_univ_succ]
  have h0 : Function.update (Matrix.vecCons y w) 0 ⁅x, Matrix.vecCons y w 0⁆ =
      Matrix.vecCons ⁅x, y⁆ w := by
    ext i
    cases i using Fin.cases <;> simp
  have htail : ∀ i : Fin n,
      Function.update (Matrix.vecCons y w) i.succ ⁅x, Matrix.vecCons y w i.succ⁆ =
        Matrix.vecCons y (Function.update w i ⁅x, w i⁆) := by
    intro i
    ext j
    cases j using Fin.cases with
    | zero =>
      simp [Function.update_of_ne (Fin.succ_ne_zero i).symm]
    | succ k =>
      simp only [Matrix.vecCons, Fin.cons_succ]
      by_cases hki : k = i
      · subst hki; simp
      · have hne : k.succ ≠ i.succ := fun h => hki (Fin.succ_inj.mp h)
        simp [Function.update_of_ne hne, Function.update_of_ne hki]
  rw [h0]
  simp_rw [htail]
  abel

theorem lieDeriv_reindexForm (K : LieActionLane R A) (x : K.L) {m n : ℕ}
    (h : m = n) (ω : ActionOperatorForm K m) :
    lieDeriv K x (reindexForm h ω) = reindexForm h (lieDeriv K x ω) := by
  subst h
  rfl

theorem lieDeriv_lie (K : LieActionLane R A) (x y : K.L) {n : ℕ}
    (ω : ActionOperatorForm K n) :
    lieDeriv K ⁅x, y⁆ ω =
      lieDeriv K x (lieDeriv K y ω) - lieDeriv K y (lieDeriv K x ω) := by
  induction n with
  | zero =>
    ext v
    simp [lieDeriv_apply]
  | succ m ih =>
    apply alternating_ext_curryLeft
    intro z
    simp only [curryLeft_sub_helper, lieDeriv_curryLeft, lieDeriv_sub]
    rw [ih (ω.curryLeft z)]
    have hjac : ⁅⁅x, y⁆, z⁆ = ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆ := by
      have h1 := lie_jacobi x y z
      have h2 : ⁅z, ⁅x, y⁆⁆ = -⁅⁅x, y⁆, z⁆ := (lie_skew z ⁅x, y⁆).symm
      have h3 : ⁅y, ⁅z, x⁆⁆ = -⁅y, ⁅x, z⁆⁆ := by rw [(lie_skew z x).symm, lie_neg]
      rw [h2, h3] at h1
      calc ⁅⁅x, y⁆, z⁆ = ⁅⁅x, y⁆, z⁆ + (⁅x, ⁅y, z⁆⁆ + -⁅y, ⁅x, z⁆⁆ + -⁅⁅x, y⁆, z⁆) := by
            rw [h1, add_zero]
        _ = ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆ := by
            rw [sub_eq_add_neg]
            abel_nf
    rw [hjac, map_sub]
    abel

private structure ActionDiffPack (K : LieActionLane R A) (n : ℕ) where
  d : ActionOperatorForm K n →ₗ[R] ActionOperatorForm K (n + 1)
  currySelf : ∀ (ω : ActionOperatorForm K (n + 1)) (x : K.L),
    (d (ω.curryLeft x)).curryLeft x = lieDeriv K x (ω.curryLeft x)

private def buildActionDiffPack (K : LieActionLane R A) :
    ∀ n : ℕ, ActionDiffPack K n
  | 0 =>
    { d :=
        { toFun := fun ω =>
            alternatingOfCurry ((lieDerivLM K).flip ω) (fun _ _ j => j.elim0)
          map_add' := fun ω₁ ω₂ => by
            apply alternating_ext_curryLeft
            intro x
            simp
          map_smul' := fun c ω => by
            apply alternating_ext_curryLeft
            intro x
            simp }
      currySelf := fun ω x => by
        simp }
  | m + 1 =>
    let prev := buildActionDiffPack K m
    { d :=
        { toFun := fun ω =>
            alternatingOfCurry
              ((lieDerivLM K).flip ω - prev.d ∘ₗ ω.curryLeft)
              (diag_of_curryLeft_self _ (fun x => by
                simp only [LinearMap.sub_apply, LinearMap.flip_apply, lieDerivLM_apply,
                  LinearMap.comp_apply, curryLeft_sub_helper]
                rw [lieDeriv_curryLeft, lie_self, map_zero, sub_zero, prev.currySelf ω x,
                  sub_self]))
          map_add' := fun ω₁ ω₂ => by
            apply alternating_ext_curryLeft
            intro x
            simp only [alternatingOfCurry_curryLeft, AlternatingMap.curryLeft_add,
              LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
            abel
          map_smul' := fun c ω => by
            apply alternating_ext_curryLeft
            intro x
            simp only [alternatingOfCurry_curryLeft, AlternatingMap.curryLeft_smul,
              LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_smul,
              RingHom.id_apply, smul_sub] }
      currySelf := fun ω x => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, alternatingOfCurry_curryLeft,
          LinearMap.sub_apply, LinearMap.flip_apply, lieDerivLM_apply, LinearMap.comp_apply,
          AlternatingMap.curryLeft_same, map_zero, sub_zero] }

/-- Arbitrary-degree Chevalley--Eilenberg exterior derivative on `ActionOperatorForm K n`
for any `LieActionLane R A` (no faithfulness or multiplication on `A` required). -/
def actionExteriorDerivative (K : LieActionLane R A) (n : ℕ) :
    ActionOperatorForm K n →ₗ[R] ActionOperatorForm K (n + 1) :=
  (buildActionDiffPack K n).d

@[simp] theorem actionExteriorDerivative_zero_curryLeft (K : LieActionLane R A)
    (ω : ActionOperatorForm K 0) (x : K.L) :
    (actionExteriorDerivative K 0 ω).curryLeft x = lieDeriv K x ω :=
  rfl

@[simp] theorem actionExteriorDerivative_zero_apply (K : LieActionLane R A)
    (ω : ActionOperatorForm K 0) (v : Fin 1 → K.L) :
    actionExteriorDerivative K 0 ω v = K.operatorAction (v 0) (ω Fin.elim0) := by
  change lieDeriv K (v 0) ω (Fin.tail v) = _
  rw [lieDeriv_apply, Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
  have hv : Fin.tail v = Fin.elim0 := Subsingleton.elim _ _
  rw [hv]

@[simp] theorem actionExteriorDerivative_succ_curryLeft (K : LieActionLane R A) (n : ℕ)
    (ω : ActionOperatorForm K (n + 1)) (x : K.L) :
    (actionExteriorDerivative K (n + 1) ω).curryLeft x =
      lieDeriv K x ω - actionExteriorDerivative K n (ω.curryLeft x) :=
  rfl

theorem actionExteriorDerivative_reindexForm (K : LieActionLane R A)
    {m n : ℕ} (h : m = n) (ω : ActionOperatorForm K m) :
    actionExteriorDerivative K n (reindexForm h ω) =
      reindexForm (congrArg (· + 1) h) (actionExteriorDerivative K m ω) := by
  subst h
  rfl

private theorem lieDeriv_and_actionExteriorDerivative_comp (K : LieActionLane R A) :
    ∀ n : ℕ,
      (∀ (x : K.L) (ω : ActionOperatorForm K n),
        lieDeriv K x (actionExteriorDerivative K n ω) =
          actionExteriorDerivative K n (lieDeriv K x ω)) ∧
      (∀ ω : ActionOperatorForm K n,
        actionExteriorDerivative K (n + 1) (actionExteriorDerivative K n ω) = 0)
  | 0 => by
    have hlie : ∀ (x : K.L) (ω : ActionOperatorForm K 0),
        lieDeriv K x (actionExteriorDerivative K 0 ω) =
          actionExteriorDerivative K 0 (lieDeriv K x ω) := by
      intro x ω
      apply alternating_ext_curryLeft
      intro y
      rw [lieDeriv_curryLeft, actionExteriorDerivative_zero_curryLeft,
        actionExteriorDerivative_zero_curryLeft, actionExteriorDerivative_zero_curryLeft,
        lieDeriv_lie]
      abel
    refine ⟨hlie, ?_⟩
    intro ω
    apply alternating_ext_curryLeft
    intro x
    rw [actionExteriorDerivative_succ_curryLeft, hlie x ω,
      actionExteriorDerivative_zero_curryLeft, sub_self, AlternatingMap.curryLeft_zero,
      LinearMap.zero_apply]
  | m + 1 => by
    obtain ⟨ih_lie, ih_dd⟩ := lieDeriv_and_actionExteriorDerivative_comp K m
    have hlie : ∀ (x : K.L) (ω : ActionOperatorForm K (m + 1)),
        lieDeriv K x (actionExteriorDerivative K (m + 1) ω) =
          actionExteriorDerivative K (m + 1) (lieDeriv K x ω) := by
      intro x ω
      apply alternating_ext_curryLeft
      intro y
      rw [lieDeriv_curryLeft, actionExteriorDerivative_succ_curryLeft,
        actionExteriorDerivative_succ_curryLeft, actionExteriorDerivative_succ_curryLeft,
        lieDeriv_sub, ih_lie x (ω.curryLeft y), lieDeriv_curryLeft, lieDeriv_lie, map_sub]
      abel
    refine ⟨hlie, ?_⟩
    intro ω
    apply alternating_ext_curryLeft
    intro x
    rw [actionExteriorDerivative_succ_curryLeft, hlie x ω,
      actionExteriorDerivative_succ_curryLeft, map_sub, ih_dd (ω.curryLeft x),
      sub_zero, sub_self, AlternatingMap.curryLeft_zero, LinearMap.zero_apply]

theorem lieDeriv_actionExteriorDerivative (K : LieActionLane R A) (x : K.L)
    {n : ℕ} (ω : ActionOperatorForm K n) :
    lieDeriv K x (actionExteriorDerivative K n ω) =
      actionExteriorDerivative K n (lieDeriv K x ω) :=
  (lieDeriv_and_actionExteriorDerivative_comp K n).1 x ω

theorem actionExteriorDerivative_succ_comp (K : LieActionLane R A) (n : ℕ)
    (ω : ActionOperatorForm K n) :
    actionExteriorDerivative K (n + 1) (actionExteriorDerivative K n ω) = 0 :=
  (lieDeriv_and_actionExteriorDerivative_comp K n).2 ω

theorem actionExteriorDerivative_comp_eq_zero (K : LieActionLane R A) (n : ℕ) :
    (actionExteriorDerivative K (n + 1)).comp (actionExteriorDerivative K n) = 0 := by
  ext ω v
  exact AlternatingMap.congr_fun (actionExteriorDerivative_succ_comp K n ω) v

/-- Pullback of an alternating form along a linear map `φ : K₁.L →ₗ[R] K₂.L`. -/
def pullbackActionForm {K₁ K₂ : LieActionLane R A} (φ : K₁.L →ₗ[R] K₂.L) (n : ℕ) :
    ActionOperatorForm K₂ n →ₗ[R] ActionOperatorForm K₁ n where
  toFun ω := ω.compLinearMap φ
  map_add' ω₁ ω₂ := by ext v; rfl
  map_smul' c ω := by ext v; rfl

@[simp] theorem pullbackActionForm_apply {K₁ K₂ : LieActionLane R A}
    (φ : K₁.L →ₗ[R] K₂.L) (n : ℕ) (ω : ActionOperatorForm K₂ n) (v : Fin n → K₁.L) :
    pullbackActionForm φ n ω v = ω (fun i => φ (v i)) :=
  rfl

@[simp] theorem pullbackActionForm_curryLeft {K₁ K₂ : LieActionLane R A}
    (φ : K₁.L →ₗ[R] K₂.L) {n : ℕ} (ω : ActionOperatorForm K₂ (n + 1)) (x : K₁.L) :
    (pullbackActionForm φ (n + 1) ω).curryLeft x =
      pullbackActionForm φ n (ω.curryLeft (φ x)) :=
  AlternatingMap.curryLeft_compLinearMap φ ω x

theorem pullbackActionForm_lieDeriv {K₁ K₂ : LieActionLane R A}
    (φ : K₁.L →ₗ⁅R⁆ K₂.L)
    (hact : ∀ (x : K₁.L) (a : A), K₁.operatorAction x a = K₂.operatorAction (φ x) a)
    (x : K₁.L) {n : ℕ} (ω : ActionOperatorForm K₂ n) :
    lieDeriv K₁ x (pullbackActionForm (φ : K₁.L →ₗ[R] K₂.L) n ω) =
      pullbackActionForm (φ : K₁.L →ₗ[R] K₂.L) n (lieDeriv K₂ (φ x) ω) := by
  ext v
  simp only [lieDeriv_apply, pullbackActionForm_apply, LieHom.coe_toLinearMap]
  have hact' := hact x (ω (fun i => φ (v i)))
  dsimp [LieActionLane.operatorAction] at hact'
  rw [hact']
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hupdate : (fun j : Fin n => φ (Function.update v i ⁅x, v i⁆ j)) =
      Function.update (fun j : Fin n => φ (v j)) i ⁅φ x, φ (v i)⁆ := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp [φ.map_lie]
    · simp [Function.update_of_ne hji]
  exact congrArg ω hupdate

theorem pullbackActionForm_actionExteriorDerivative {K₁ K₂ : LieActionLane R A}
    (φ : K₁.L →ₗ⁅R⁆ K₂.L)
    (hact : ∀ (x : K₁.L) (a : A), K₁.operatorAction x a = K₂.operatorAction (φ x) a)
    (n : ℕ) (ω : ActionOperatorForm K₂ n) :
    actionExteriorDerivative K₁ n (pullbackActionForm (φ : K₁.L →ₗ[R] K₂.L) n ω) =
      pullbackActionForm (φ : K₁.L →ₗ[R] K₂.L) (n + 1) (actionExteriorDerivative K₂ n ω) := by
  induction n with
  | zero =>
    apply alternating_ext_curryLeft
    intro x
    rw [actionExteriorDerivative_zero_curryLeft, pullbackActionForm_curryLeft,
      actionExteriorDerivative_zero_curryLeft, pullbackActionForm_lieDeriv φ hact x ω]
    rfl
  | succ m ih =>
    apply alternating_ext_curryLeft
    intro x
    rw [actionExteriorDerivative_succ_curryLeft, pullbackActionForm_curryLeft,
      pullbackActionForm_curryLeft, actionExteriorDerivative_succ_curryLeft,
      pullbackActionForm_lieDeriv φ hact x ω]
    simp only [LieHom.coe_toLinearMap] at ih ⊢
    rw [ih (ω.curryLeft (φ x))]
    rfl

end Tier1_LieActionCalculus

section LeibnizPredicate

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Predicate asserting that every generator of a `LieActionLane R A` acts as a
Leibniz derivation of the multiplicative structure on `A`. -/
def IsLeibnizAction (K : LieActionLane R A) : Prop :=
  ∀ x : K.L, NonAssocDerivation.IsLeibniz R A (K.operatorAction x)

/-- Embed any faithful `DerivationLieLane R A` into `LieActionLane R A`.
Note that `ActionOperatorForm K.toLieActionLane n` is definitionally equal to
`DerivationOperatorForm K n`. -/
def _root_.InfoGeometry.Algebra.DerivationLieLane.toLieActionLane
    (K : DerivationLieLane R A) : LieActionLane R A where
  L := K.L
  lieRing := K.lieRing
  lieAlgebra := K.lieAlgebra
  act := K.operatorActionLieHom

theorem _root_.InfoGeometry.Algebra.DerivationLieLane.isLeibnizAction
    (K : DerivationLieLane R A) :
    IsLeibnizAction K.toLieActionLane :=
  K.operatorAction_leibniz

@[simp] theorem _root_.InfoGeometry.Algebra.DerivationLieLane.toLieActionLane_operatorAction
    (K : DerivationLieLane R A) (x : K.L) (a : A) :
    K.toLieActionLane.operatorAction x a = K.operatorAction x a :=
  rfl

end LeibnizPredicate

/-! ## Tier 2: Faithful quotient and range factorizations (`DerivationLieLane R A`) -/

section Tier2_FaithfulFactorization

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Canonical full faithful derivation lane for `(R, A)`. -/
def fullDerivationLieLane (R A : Type*) [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : DerivationLieLane R A where
  L := NonAssocDerivation.derivations R A
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := LieHom.id
  faithful := Function.injective_id

/-- Canonical faithful derivation lane on any Lie subalgebra of derivations. -/
def lieSubalgebraLane (S : LieSubalgebra R (NonAssocDerivation.derivations R A)) :
    DerivationLieLane R A where
  L := S
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := S.incl
  faithful := Subtype.coe_injective

/-- Lift any `LieActionLane` satisfying `IsLeibnizAction` to a Lie algebra
homomorphism into `NonAssocDerivation.derivations R A`. -/
def lieActionToDerivationHom (K : LieActionLane R A) (hK : IsLeibnizAction K) :
    K.L →ₗ⁅R⁆ NonAssocDerivation.derivations R A where
  toFun x := ⟨K.operatorAction x, hK x⟩
  map_add' x y := Subtype.ext (K.operatorAction.map_add x y)
  map_smul' r x := Subtype.ext (K.operatorAction.map_smul r x)
  map_lie' {x y} := Subtype.ext (by
    ext a
    exact K.operatorAction_commutator_apply x y a)

/-- Underlying `LieActionLane` associated with a (possibly non-faithful) Lie
algebra homomorphism into `NonAssocDerivation.derivations R A`. -/
def toLieActionLaneFromHom {L : Type*} [LieRing L] [LieAlgebra R L]
    (act : L →ₗ⁅R⁆ NonAssocDerivation.derivations R A) : LieActionLane R A where
  L := L
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act :=
    { toFun := fun x => (act x : Module.End R A)
      map_add' := fun x y => congrArg Subtype.val (act.map_add x y)
      map_smul' := fun r x => congrArg Subtype.val (act.map_smul r x)
      map_lie' := fun {x y} => by
        ext a
        simp [LieRing.of_associative_ring_bracket, Module.End.mul_apply] }

theorem toLieActionLaneFromHom_isLeibniz {L : Type*} [LieRing L] [LieAlgebra R L]
    (act : L →ₗ⁅R⁆ NonAssocDerivation.derivations R A) :
    IsLeibnizAction (toLieActionLaneFromHom act) :=
  fun x => (act x).property

/-- Range factorization of any (possibly non-faithful) Lie-derivation hom into
a faithful `DerivationLieLane`. -/
def rangeDerivationLieLane {L : Type*} [LieRing L] [LieAlgebra R L]
    (act : L →ₗ⁅R⁆ NonAssocDerivation.derivations R A) : DerivationLieLane R A :=
  lieSubalgebraLane act.range

/-- Quotient factorization `L ⧸ act.ker` into a faithful `DerivationLieLane`. -/
def quotientDerivationLieLane {L : Type*} [LieRing L] [LieAlgebra R L]
    (act : L →ₗ⁅R⁆ NonAssocDerivation.derivations R A) : DerivationLieLane R A where
  L := L ⧸ act.ker
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := act.range.incl.comp (LieHom.quotKerEquivRange act).toLieHom
  faithful := Subtype.coe_injective.comp (LieHom.quotKerEquivRange act).injective

/-- The canonical equivariant equivalence between the quotient lane and the
range lane via the Lie first isomorphism theorem. -/
def quotientDerivationLieLaneEquivRange {L : Type*} [LieRing L] [LieAlgebra R L]
    (act : L →ₗ⁅R⁆ NonAssocDerivation.derivations R A) :
    DerivationLaneEquiv (quotientDerivationLieLane act) (rangeDerivationLieLane act) where
  map := LieHom.quotKerEquivRange act
  equivariant _ := rfl

/-- Pullback of forms on the faithful range lane back to `ActionOperatorForm` on `L`.
Injective (since `act.rangeRestrict` is surjective) and commutes with `d_n`. -/
def pullbackRangeForm {L : Type*} [LieRing L] [LieAlgebra R L]
    (act : L →ₗ⁅R⁆ NonAssocDerivation.derivations R A) (n : ℕ) :
    ActionOperatorForm (rangeDerivationLieLane act).toLieActionLane n →ₗ[R]
      ActionOperatorForm (toLieActionLaneFromHom act) n :=
  pullbackActionForm (K₁ := toLieActionLaneFromHom act)
    (K₂ := (rangeDerivationLieLane act).toLieActionLane)
    (act.rangeRestrict : L →ₗ[R] act.range) n

theorem pullbackRangeForm_injective {L : Type*} [LieRing L] [LieAlgebra R L]
    (act : L →ₗ⁅R⁆ NonAssocDerivation.derivations R A) (n : ℕ) :
    Function.Injective (pullbackRangeForm act n) := by
  intro ω₁ ω₂ h
  ext v
  choose u hu using fun i => act.surjective_rangeRestrict (v i)
  have h1 := AlternatingMap.congr_fun h u
  change ω₁ (fun i => act.rangeRestrict (u i)) = ω₂ (fun i => act.rangeRestrict (u i)) at h1
  have huv : (fun i => act.rangeRestrict (u i)) = v := funext hu
  rwa [huv] at h1

theorem pullbackRangeForm_actionExteriorDerivative {L : Type*} [LieRing L] [LieAlgebra R L]
    (act : L →ₗ⁅R⁆ NonAssocDerivation.derivations R A) (n : ℕ)
    (ω : ActionOperatorForm (rangeDerivationLieLane act).toLieActionLane n) :
    actionExteriorDerivative (toLieActionLaneFromHom act) n (pullbackRangeForm act n ω) =
      pullbackRangeForm act (n + 1)
        (actionExteriorDerivative (rangeDerivationLieLane act).toLieActionLane n ω) :=
  pullbackActionForm_actionExteriorDerivative
    (K₁ := toLieActionLaneFromHom act)
    (K₂ := (rangeDerivationLieLane act).toLieActionLane)
    act.rangeRestrict (fun _ _ => rfl) n ω

end Tier2_FaithfulFactorization

/-! ## Tier 3: Unified Leibniz derivation adapters -/

section Tier3_Adapters

section CommScalarAdapters

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Equivalence between `NonAssocIteratedLeibniz.IsDerivation (LinearMap.mul R A)`
and `NonAssocDerivation.IsLeibniz R A`. -/
theorem iteratedIsDerivation_iff_isLeibniz (D : A →ₗ[R] A) :
    InfoGeometry.Algebra.NonAssocIteratedLeibniz.IsDerivation (LinearMap.mul R A) D ↔
      NonAssocDerivation.IsLeibniz R A D :=
  Iff.rfl

/-- Bundle a `NonAssocIteratedLeibniz.IsDerivation (LinearMap.mul R A)` endomorphism
into `NonAssocDerivation.derivations R A`. -/
def iteratedDerivationToDerivations (D : A →ₗ[R] A)
    (hD : InfoGeometry.Algebra.NonAssocIteratedLeibniz.IsDerivation (LinearMap.mul R A) D) :
    NonAssocDerivation.derivations R A :=
  ⟨D, hD⟩

/-- Equivalence between `InfoGeometry.Algebra.NonAssocDerivation R A` and
`NonAssocDerivation.derivations R A`. -/
def nonAssocDerivationEquivDerivations :
    InfoGeometry.Algebra.NonAssocDerivation R A ≃ NonAssocDerivation.derivations R A where
  toFun D := ⟨D.toLinearMap, D.leibniz'⟩
  invFun D := ⟨(D : Module.End R A), D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by ext x; rfl

end CommScalarAdapters

section AssociativeCommScalarAdapters

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Embed `Geometry.AssociativeGaugeConnection.IsLeibniz` into
`NonAssocDerivation.derivations R A`. -/
def associativeIsLeibnizToDerivations (D : Module.End R A)
    (hD : InfoGeometry.Geometry.AssociativeGaugeConnection.IsLeibniz D) :
    NonAssocDerivation.derivations R A :=
  ⟨D, hD⟩

/-- Embed `NCG.AlgebraDerivation R A` into `NonAssocDerivation.derivations R A`. -/
def algebraDerivationToDerivations (D : InfoGeometry.NCG.AlgebraDerivation R A) :
    NonAssocDerivation.derivations R A :=
  ⟨D.toLinearMap, D.leibniz'⟩

/-- Embed `NCG.CyclicAlgebraDerivation R A` into `NonAssocDerivation.derivations R A`. -/
def cyclicAlgebraDerivationToDerivations
    (D : InfoGeometry.NCG.CyclicAlgebraDerivation R A) :
    NonAssocDerivation.derivations R A :=
  ⟨D.toLinearMap, D.leibniz'⟩

end AssociativeCommScalarAdapters

section NoncommScalarToZAdapters

variable {R A : Type*} [Ring R] [Ring A] [Module R A]

/-- Restrict any `NCG.AlgebraDerivation R A` over a (possibly noncommutative) ring `R`
to a `ℤ`-linear `NCG.Calculus.NCDerivation A`. -/
def algebraDerivationToNCDerivation (D : InfoGeometry.NCG.AlgebraDerivation R A) :
    InfoGeometry.NCG.Calculus.NCDerivation A where
  toLinearMap := D.toLinearMap.restrictScalars ℤ
  leibniz' := D.leibniz'

/-- Restrict any `NCG.CyclicAlgebraDerivation R A` over a (possibly noncommutative) ring `R`
to a `ℤ`-linear `NCG.Calculus.NCDerivation A`. -/
def cyclicAlgebraDerivationToNCDerivation
    (D : InfoGeometry.NCG.CyclicAlgebraDerivation R A) :
    InfoGeometry.NCG.Calculus.NCDerivation A where
  toLinearMap := D.toLinearMap.restrictScalars ℤ
  leibniz' := D.leibniz'

end NoncommScalarToZAdapters

section IntAdapters

variable {A : Type*} [Ring A]

/-- Equivalence between `NCG.Calculus.NCDerivation A` and `NonAssocDerivation.derivations ℤ A`,
preserving addition, zero, negation, and commutator brackets. -/
def ncDerivationEquivDerivations :
    InfoGeometry.NCG.Calculus.NCDerivation A ≃ NonAssocDerivation.derivations ℤ A where
  toFun D := ⟨D.toLinearMap, D.leibniz'⟩
  invFun D := ⟨(D : Module.End ℤ A), D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by ext x; rfl

@[simp] theorem ncDerivationEquivDerivations_apply
    (D : InfoGeometry.NCG.Calculus.NCDerivation A) (x : A) :
    ((ncDerivationEquivDerivations D : NonAssocDerivation.derivations ℤ A) :
      Module.End ℤ A) x = D x :=
  rfl

theorem ncDerivationEquivDerivations_commutator
    (D E : InfoGeometry.NCG.Calculus.NCDerivation A) :
    ncDerivationEquivDerivations (InfoGeometry.NCG.Calculus.NCDerivation.commutator D E) =
      ⁅ncDerivationEquivDerivations D, ncDerivationEquivDerivations E⁆ := by
  apply Subtype.ext
  ext x
  rfl

/-- Unconditional Lie subalgebra of `NonAssocDerivation.derivations ℤ A` spanned by the
derivation image of an `NCG.DerivationDifferential.LieSystem A 𝔤` (no `bracket_self`
or faithfulness assumption on `𝔤` required). -/
def lieSystemRangeSubalgebra {𝔤 : Type*} [AddCommGroup 𝔤]
    (S : InfoGeometry.NCG.DerivationDifferential.LieSystem A 𝔤) :
    LieSubalgebra ℤ (NonAssocDerivation.derivations ℤ A) where
  carrier := { D | ∃ g : 𝔤, ncDerivationEquivDerivations (S.derivation g) = D }
  zero_mem' := ⟨0, by simp [S.derivation_zero]; rfl⟩
  add_mem' := by
    rintro _ _ ⟨g₁, rfl⟩ ⟨g₂, rfl⟩
    refine ⟨g₁ + g₂, ?_⟩
    rw [S.derivation_add]
    apply Subtype.ext
    ext a
    rfl
  smul_mem' := by
    rintro c _ ⟨g, rfl⟩
    induction c using Int.induction_on with
    | zero =>
      refine ⟨0, ?_⟩
      simp only [zero_smul, S.derivation_zero]
      rfl
    | succ k ih =>
      rcases ih with ⟨gk, hgk⟩
      refine ⟨gk + g, ?_⟩
      rw [add_smul, one_smul, S.derivation_add, ← hgk]
      apply Subtype.ext
      ext a
      rfl
    | pred k ih =>
      rcases ih with ⟨gk, hgk⟩
      refine ⟨gk + -g, ?_⟩
      have hneg : ∀ h : 𝔤, S.derivation (-h) = -S.derivation h := by
        intro h
        apply InfoGeometry.NCG.Calculus.NCDerivation.ext
        intro a
        have h0 : S.derivation (h + -h) a = (S.derivation h + S.derivation (-h)) a :=
          congrArg (fun D : InfoGeometry.NCG.Calculus.NCDerivation A => D a)
            (S.derivation_add h (-h))
        rw [add_neg_cancel, S.derivation_zero] at h0
        exact eq_neg_of_add_eq_zero_right h0.symm
      rw [S.derivation_add, hneg g]
      apply Subtype.ext
      ext a
      have hgk' : S.derivation gk a =
          ((-(k : ℤ)) • ncDerivationEquivDerivations (S.derivation g) :
            Module.End ℤ A) a :=
        congrArg (fun D : NonAssocDerivation.derivations ℤ A => (D : Module.End ℤ A) a) hgk
      show S.derivation gk a + (-S.derivation g) a =
        ((-(k : ℤ) - 1) • ncDerivationEquivDerivations (S.derivation g) :
          Module.End ℤ A) a
      rw [hgk']
      change (-(k : ℤ) • S.derivation g a) + -(S.derivation g a) =
        (-(k : ℤ) - 1) • S.derivation g a
      rw [sub_eq_add_neg, add_smul, neg_one_smul]
  lie_mem' := by
    rintro _ _ ⟨g₁, rfl⟩ ⟨g₂, rfl⟩
    refine ⟨S.bracket g₁ g₂, ?_⟩
    apply Subtype.ext
    ext a
    exact (S.bracket_action g₁ g₂ a).symm

/-- Note that even if `𝔤` has 2-torsion (`S.bracket g g ≠ 0`), `S.bracket g g` is
unconditionally in the kernel of `S.derivation`. -/
theorem lieSystem_bracket_self_mem_ker {𝔤 : Type*} [AddCommGroup 𝔤]
    (S : InfoGeometry.NCG.DerivationDifferential.LieSystem A 𝔤) (g : 𝔤) :
    S.derivation (S.bracket g g) = 0 := by
  apply InfoGeometry.NCG.Calculus.NCDerivation.ext
  intro a
  rw [← S.bracket_action g g a, sub_self]
  rfl

/-- Unconditional faithful `DerivationLieLane ℤ A` on the image of any `LieSystem A 𝔤`. -/
def lieSystemToDerivationLieLane {𝔤 : Type*} [AddCommGroup 𝔤]
    (S : InfoGeometry.NCG.DerivationDifferential.LieSystem A 𝔤) :
    DerivationLieLane ℤ A :=
  lieSubalgebraLane (lieSystemRangeSubalgebra S)

/-- Non-faithful `LieActionLane ℤ A` directly on `𝔤` whenever `S.bracket g g = 0`
(e.g., `innerLieSystem` or any torsion-free `LieSystem`), preserving forms that do not
vanish on `ker(S.derivation)`. -/
def lieSystemToLieActionLane {𝔤 : Type*} [AddCommGroup 𝔤]
    (S : InfoGeometry.NCG.DerivationDifferential.LieSystem A 𝔤)
    (hself : ∀ g : 𝔤, S.bracket g g = 0) : LieActionLane ℤ A :=
  letI : LieRing 𝔤 :=
    { bracket := S.bracket
      add_lie := S.bracket_add_left
      lie_add := S.bracket_add_right
      lie_self := hself
      leibniz_lie := fun x y z => by
        have hj := S.bracket_jacobi x y z
        have hs1 : S.bracket y (S.bracket z x) = -S.bracket y (S.bracket x z) := by
          rw [S.bracket_skew x z, S.bracket_neg_right]
        have hs2 : S.bracket z (S.bracket x y) = -S.bracket (S.bracket x y) z :=
          S.bracket_skew (S.bracket x y) z
        rw [hs1, hs2] at hj
        calc S.bracket x (S.bracket y z)
            = S.bracket x (S.bracket y z) -
                (S.bracket x (S.bracket y z) + -S.bracket y (S.bracket x z) +
                  -S.bracket (S.bracket x y) z) := by rw [hj, sub_zero]
          _ = S.bracket (S.bracket x y) z + S.bracket y (S.bracket x z) := by
                rw [sub_eq_add_neg]
                abel_nf }
  letI : LieAlgebra ℤ 𝔤 := inferInstance
  { L := 𝔤
    lieRing := ‹_›
    lieAlgebra := ‹_›
    act :=
      { toFun := fun g => (S.derivation g).toLinearMap
        map_add' := fun g₁ g₂ => by
          ext a
          simp [S.derivation_add]
        map_smul' := fun c g => by
          have h : ∀ k : ℤ, (S.derivation (k • g)).toLinearMap =
              k • (S.derivation g).toLinearMap := by
            intro k
            induction k using Int.induction_on with
            | zero => simp [S.derivation_zero]; rfl
            | succ m ih =>
              rw [add_smul, one_smul, S.derivation_add]
              ext a
              have hm := congrArg (fun T : A →ₗ[ℤ] A => T a) ih
              simp only [LinearMap.smul_apply] at hm
              change S.derivation ((m : ℤ) • g) a + S.derivation g a =
                (((m : ℤ) + 1) • (S.derivation g).toLinearMap) a
              rw [hm, LinearMap.smul_apply, add_smul, one_smul]
            | pred m ih =>
              have hneg : ∀ h : 𝔤, S.derivation (-h) = -S.derivation h := by
                intro h
                apply InfoGeometry.NCG.Calculus.NCDerivation.ext
                intro a
                have h0 : S.derivation (h + -h) a = (S.derivation h + S.derivation (-h)) a :=
                  congrArg (fun D : InfoGeometry.NCG.Calculus.NCDerivation A => D a)
                    (S.derivation_add h (-h))
                rw [add_neg_cancel, S.derivation_zero] at h0
                exact eq_neg_of_add_eq_zero_right h0.symm
              rw [sub_eq_add_neg, add_smul, neg_one_smul, S.derivation_add, hneg g]
              ext a
              have hm := congrArg (fun T : A →ₗ[ℤ] A => T a) ih
              simp only [LinearMap.smul_apply] at hm
              change S.derivation (-(m : ℤ) • g) a + -(S.derivation g a) =
                ((-(m : ℤ) + -1) • (S.derivation g).toLinearMap) a
              rw [hm, LinearMap.smul_apply, add_smul, neg_one_smul]
          simpa using h c
        map_lie' := fun {g₁ g₂} => by
          ext a
          exact (S.bracket_action g₁ g₂ a).symm } }

/-- Direct non-faithful `LieActionLane ℤ A` for the inner derivation action `a ↦ [a, -]`. -/
def innerLieActionLane (A : Type*) [Ring A] : LieActionLane ℤ A :=
  lieSystemToLieActionLane (InfoGeometry.NCG.DerivationDifferential.innerLieSystem (A := A))
    (fun g => by simp [InfoGeometry.NCG.DerivationDifferential.innerLieSystem,
      InfoGeometry.NCG.DerivationDifferential.innerSystem, InfoGeometry.NCG.bracket])

/-- Additive and commutator-preserving equivalence between `Modular.ExactSequence.Derivation A`
and `NonAssocDerivation.derivations ℤ A`. -/
def modularDerivationToDerivations :
    InfoGeometry.Modular.ExactSequence.Derivation A ≃+ NonAssocDerivation.derivations ℤ A where
  toFun D :=
    ⟨{ toFun := D.toFun
       map_add' := D.map_add'
       map_smul' := fun n x => by
         change D (n • x) = n • D x
         exact (AddMonoidHom.mk' D.toFun D.map_add').map_zsmul n x },
     D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by ext x; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl
  map_add' D₁ D₂ := by apply Subtype.ext; ext x; rfl

theorem modularDerivationToDerivations_commutator
    (D₁ D₂ : InfoGeometry.Modular.ExactSequence.Derivation A) :
    modularDerivationToDerivations
        (InfoGeometry.Modular.ExactSequence.Derivation.derivationCommutator D₁ D₂) =
      ⁅modularDerivationToDerivations D₁, modularDerivationToDerivations D₂⁆ := by
  apply Subtype.ext
  ext x
  rfl

/-- Canonical faithful `DerivationLieLane ℤ A` for `Modular.ExactSequence.Derivation A`. -/
def modularDerivationsLane (A : Type*) [Ring A] : DerivationLieLane ℤ A :=
  fullDerivationLieLane ℤ A

/-- The inner derivations `Modular.ExactSequence.Inn` packaged as a Lie ideal of
`NonAssocDerivation.derivations ℤ A` via `dual_flow_commutator`. -/
def modularInnerIdeal (A : Type*) [Ring A] :
    LieIdeal ℤ (NonAssocDerivation.derivations ℤ A) where
  carrier := { D | ∃ K : A, modularDerivationToDerivations
    (InfoGeometry.Modular.ExactSequence.modularDerivation K) = D }
  zero_mem' := ⟨0, by
    apply Subtype.ext
    ext x
    change (0 : A) * x - x * 0 = 0
    simp⟩
  add_mem' := by
    rintro _ _ ⟨K₁, rfl⟩ ⟨K₂, rfl⟩
    refine ⟨K₁ + K₂, ?_⟩
    apply Subtype.ext
    ext x
    exact InfoGeometry.Modular.ExactSequence.modularDerivation_add_apply K₁ K₂ x
  smul_mem' := by
    rintro c _ ⟨K, rfl⟩
    refine ⟨c • K, ?_⟩
    apply Subtype.ext
    ext x
    change (c • K) * x - x * (c • K) = c • (K * x - x * K)
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]
  lie_mem := by
    rintro D _ ⟨K, rfl⟩
    refine ⟨(D : Module.End ℤ A) K, ?_⟩
    have h := InfoGeometry.Modular.ExactSequence.commutator_eq_modularDerivation
      (modularDerivationToDerivations.symm D) K
    have h' := congrArg modularDerivationToDerivations h
    rw [modularDerivationToDerivations_commutator,
      AddEquiv.apply_symm_apply] at h'
    exact h'.symm

end IntAdapters

end Tier3_Adapters

/-! ## Arbitrary-degree noncommutative DGA (`DerivationOperatorForm K n`) -/

section NoncommutativeDGA

variable {R A : Type*}
variable [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Native derivation-based operator `n`-forms. -/
abbrev DerivationOperatorForm (K : DerivationLieLane R A) (n : ℕ) :=
  K.L [⋀^(Fin n)]→ₗ[R] A

/-- Cartan Lie derivative on `DerivationOperatorForm K n`. -/
abbrev ceLieDeriv (K : DerivationLieLane R A) (x : K.L) {n : ℕ}
    (ω : DerivationOperatorForm K n) : DerivationOperatorForm K n :=
  lieDeriv K.toLieActionLane x ω

/-- Arbitrary-degree Chevalley--Eilenberg exterior derivative on `DerivationOperatorForm K n`. -/
def ceExteriorDerivative (K : DerivationLieLane R A) (n : ℕ) :
    DerivationOperatorForm K n →ₗ[R] DerivationOperatorForm K (n + 1) :=
  actionExteriorDerivative K.toLieActionLane n

@[simp] theorem ceExteriorDerivative_zero_curryLeft (K : DerivationLieLane R A)
    (ω : DerivationOperatorForm K 0) (x : K.L) :
    (ceExteriorDerivative K 0 ω).curryLeft x = ceLieDeriv K x ω :=
  rfl

@[simp] theorem ceExteriorDerivative_succ_curryLeft (K : DerivationLieLane R A) (n : ℕ)
    (ω : DerivationOperatorForm K (n + 1)) (x : K.L) :
    (ceExteriorDerivative K (n + 1) ω).curryLeft x =
      ceLieDeriv K x ω - ceExteriorDerivative K n (ω.curryLeft x) :=
  rfl

theorem ceExteriorDerivative_succ_comp (K : DerivationLieLane R A) (n : ℕ)
    (ω : DerivationOperatorForm K n) :
    ceExteriorDerivative K (n + 1) (ceExteriorDerivative K n ω) = 0 :=
  actionExteriorDerivative_succ_comp K.toLieActionLane n ω

theorem ceExteriorDerivative_comp_eq_zero (K : DerivationLieLane R A) (n : ℕ) :
    (ceExteriorDerivative K (n + 1)).comp (ceExteriorDerivative K n) = 0 :=
  actionExteriorDerivative_comp_eq_zero K.toLieActionLane n

theorem ceExteriorDerivative_reindexForm (K : DerivationLieLane R A)
    {m n : ℕ} (h : m = n) (ω : DerivationOperatorForm K m) :
    ceExteriorDerivative K n (reindexForm h ω) =
      reindexForm (congrArg (· + 1) h) (ceExteriorDerivative K m ω) :=
  actionExteriorDerivative_reindexForm K.toLieActionLane h ω

/-- Degree-0 linear equivalence `A ≃ₗ[R] DerivationOperatorForm K 0`. -/
def zeroFormAlternatingEquiv (K : DerivationLieLane R A) :
    A ≃ₗ[R] DerivationOperatorForm K 0 :=
  AlternatingMap.constLinearEquivOfIsEmpty

@[simp] theorem zeroFormAlternatingEquiv_apply (K : DerivationLieLane R A)
    (a : A) (v : Fin 0 → K.L) :
    zeroFormAlternatingEquiv K a v = a :=
  rfl

@[simp] theorem zeroFormAlternatingEquiv_symm_apply (K : DerivationLieLane R A)
    (ω : DerivationOperatorForm K 0) :
    (zeroFormAlternatingEquiv K).symm ω = ω Fin.elim0 := by
  change ω _ = ω Fin.elim0
  congr 1
  exact Subsingleton.elim _ _

/-- Degree-1 linear equivalence `oneCochain R K.L A ≃ₗ[R] DerivationOperatorForm K 1`. -/
def oneFormAlternatingLinearEquiv (K : DerivationLieLane R A) :
    LieModule.Cohomology.oneCochain R K.L A ≃ₗ[R] DerivationOperatorForm K 1 where
  toLinearMap :=
    { toFun := AlternatingMap.ofSubsingleton R K.L A (0 : Fin 1)
      map_add' := fun ω₁ ω₂ => by ext v; rfl
      map_smul' := fun c ω => by ext v; rfl }
  invFun := fun η =>
    { toFun := fun x => η (fun _ => x)
      map_add' := fun x y => by
        have h : (fun _ : Fin 1 => x + y) = Function.update (fun _ => x) 0 (x + y) :=
          funext fun i => by fin_cases i; rfl
        have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
          funext fun i => by fin_cases i; rfl
        have h1 : (fun _ : Fin 1 => y) = Function.update (fun _ => x) 0 y :=
          funext fun i => by fin_cases i; rfl
        rw [h, η.map_update_add, ← h0, ← h1]
      map_smul' := fun c x => by
        have h : (fun _ : Fin 1 => c • x) = Function.update (fun _ => x) 0 (c • x) :=
          funext fun i => by fin_cases i; rfl
        have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
          funext fun i => by fin_cases i; rfl
        change η (fun _ => c • x) = c • η (fun _ => x)
        rw [h, η.map_update_smul, ← h0] }
  left_inv ω := by ext x; rfl
  right_inv η := by
    ext v
    change η (fun _ => v 0) = η v
    congr 1
    ext i
    rw [Fin.eq_zero i]

@[simp] theorem oneFormAlternatingLinearEquiv_apply (K : DerivationLieLane R A)
    (ω : LieModule.Cohomology.oneCochain R K.L A) (v : Fin 1 → K.L) :
    oneFormAlternatingLinearEquiv K ω v = ω (v 0) :=
  rfl

@[simp] theorem oneFormAlternatingLinearEquiv_symm_apply (K : DerivationLieLane R A)
    (η : DerivationOperatorForm K 1) (x : K.L) :
    (oneFormAlternatingLinearEquiv K).symm η x = η (fun _ => x) :=
  rfl

/-- Degree-2 linear equivalence `twoCochain R K.L A ≃ₗ[R] DerivationOperatorForm K 2`. -/
def twoCochainEquivDerivationOperatorForm (K : DerivationLieLane R A) :
    LieModule.Cohomology.twoCochain R K.L A ≃ₗ[R] DerivationOperatorForm K 2 where
  toFun ω :=
    { MultilinearMap.mk' (fun v : Fin 2 → K.L => ω.1 (v 0) (v 1))
        (fun v i x y => by fin_cases i <;> simp [Function.update])
        (fun v i c x => by fin_cases i <;> simp [Function.update]) with
      map_eq_zero_of_eq' := fun v i j hv hij => by
        fin_cases i <;> fin_cases j <;> dsimp at hv hij
        · exact (hij rfl).elim
        · change ω.1 (v 0) (v 1) = 0
          rw [hv]
          exact ω.2 (v 1)
        · change ω.1 (v 0) (v 1) = 0
          rw [hv]
          exact ω.2 (v 0)
        · exact (hij rfl).elim }
  map_add' ω₁ ω₂ := by ext v; rfl
  map_smul' c ω := by ext v; rfl
  invFun η :=
    ⟨LinearMap.mk₂ R (fun x y => η ![x, y])
      (fun x₁ x₂ y => by
        have h1 : ![x₁ + x₂, y] = Function.update ![x₁, y] 0 (x₁ + x₂) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x₁, y] = Function.update ![x₁, y] 0 x₁ := by
          ext i; fin_cases i <;> rfl
        have h2 : ![x₂, y] = Function.update ![x₁, y] 0 x₂ := by
          ext i; fin_cases i <;> rfl
        rw [h1, η.map_update_add, ← h0, ← h2])
      (fun c x y => by
        have h1 : ![c • x, y] = Function.update ![x, y] 0 (c • x) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x, y] = Function.update ![x, y] 0 x := by
          ext i; fin_cases i <;> rfl
        rw [h1, η.map_update_smul, ← h0])
      (fun x y₁ y₂ => by
        have h1 : ![x, y₁ + y₂] = Function.update ![x, y₁] 1 (y₁ + y₂) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x, y₁] = Function.update ![x, y₁] 1 y₁ := by
          ext i; fin_cases i <;> rfl
        have h2 : ![x, y₂] = Function.update ![x, y₁] 1 y₂ := by
          ext i; fin_cases i <;> rfl
        rw [h1, η.map_update_add, ← h0, ← h2])
      (fun c x y => by
        have h1 : ![x, c • y] = Function.update ![x, y] 1 (c • y) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x, y] = Function.update ![x, y] 1 y := by
          ext i; fin_cases i <;> rfl
        rw [h1, η.map_update_smul, ← h0]),
     fun x => η.map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)⟩
  left_inv ω := Subtype.ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)
  right_inv η := by
    ext v
    change η ![v 0, v 1] = η v
    congr 1
    ext i
    fin_cases i <;> rfl

@[simp] theorem twoCochainEquivDerivationOperatorForm_apply (K : DerivationLieLane R A)
    (ω : LieModule.Cohomology.twoCochain R K.L A) (v : Fin 2 → K.L) :
    twoCochainEquivDerivationOperatorForm K ω v = ω.1 (v 0) (v 1) :=
  rfl

@[simp] theorem twoCochainEquivDerivationOperatorForm_symm_apply (K : DerivationLieLane R A)
    (η : DerivationOperatorForm K 2) (x y : K.L) :
    ((twoCochainEquivDerivationOperatorForm K).symm η).1 x y = η ![x, y] :=
  rfl

/-- Canonical embedding of alternating 3-forms into `K.L →ₗ[R] K.L →ₗ[R] K.L →ₗ[R] A`. -/
def threeFormToThreeCochain (K : DerivationLieLane R A) :
    DerivationOperatorForm K 3 →ₗ[R] (K.L →ₗ[R] K.L →ₗ[R] K.L →ₗ[R] A) where
  toFun η :=
    LinearMap.mk₂ R (fun x y =>
      { toFun := fun z => η ![x, y, z]
        map_add' := fun z₁ z₂ => by
          have h1 : ![x, y, z₁ + z₂] = Function.update ![x, y, z₁] 2 (z₁ + z₂) := by
            ext i; fin_cases i <;> rfl
          have h0 : ![x, y, z₁] = Function.update ![x, y, z₁] 2 z₁ := by
            ext i; fin_cases i <;> rfl
          have h2 : ![x, y, z₂] = Function.update ![x, y, z₁] 2 z₂ := by
            ext i; fin_cases i <;> rfl
          rw [h1, η.map_update_add, ← h0, ← h2]
        map_smul' := fun c z => by
          have h1 : ![x, y, c • z] = Function.update ![x, y, z] 2 (c • z) := by
            ext i; fin_cases i <;> rfl
          have h0 : ![x, y, z] = Function.update ![x, y, z] 2 z := by
            ext i; fin_cases i <;> rfl
          change η ![x, y, c • z] = c • η ![x, y, z]
          rw [h1, η.map_update_smul, ← h0] })
      (fun x₁ x₂ y => by
        ext z
        have h1 : ![x₁ + x₂, y, z] = Function.update ![x₁, y, z] 0 (x₁ + x₂) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x₁, y, z] = Function.update ![x₁, y, z] 0 x₁ := by
          ext i; fin_cases i <;> rfl
        have h2 : ![x₂, y, z] = Function.update ![x₁, y, z] 0 x₂ := by
          ext i; fin_cases i <;> rfl
        change η ![x₁ + x₂, y, z] = η ![x₁, y, z] + η ![x₂, y, z]
        rw [h1, η.map_update_add, ← h0, ← h2])
      (fun c x y => by
        ext z
        have h1 : ![c • x, y, z] = Function.update ![x, y, z] 0 (c • x) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x, y, z] = Function.update ![x, y, z] 0 x := by
          ext i; fin_cases i <;> rfl
        change η ![c • x, y, z] = c • η ![x, y, z]
        rw [h1, η.map_update_smul, ← h0])
      (fun x y₁ y₂ => by
        ext z
        have h1 : ![x, y₁ + y₂, z] = Function.update ![x, y₁, z] 1 (y₁ + y₂) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x, y₁, z] = Function.update ![x, y₁, z] 1 y₁ := by
          ext i; fin_cases i <;> rfl
        have h2 : ![x, y₂, z] = Function.update ![x, y₁, z] 1 y₂ := by
          ext i; fin_cases i <;> rfl
        change η ![x, y₁ + y₂, z] = η ![x, y₁, z] + η ![x, y₂, z]
        rw [h1, η.map_update_add, ← h0, ← h2])
      (fun c x y => by
        ext z
        have h1 : ![x, c • y, z] = Function.update ![x, y, z] 1 (c • y) := by
          ext i; fin_cases i <;> rfl
        have h0 : ![x, y, z] = Function.update ![x, y, z] 1 y := by
          ext i; fin_cases i <;> rfl
        change η ![x, c • y, z] = c • η ![x, y, z]
        rw [h1, η.map_update_smul, ← h0])
  map_add' η₁ η₂ := by ext x y z; rfl
  map_smul' c η := by ext x y z; rfl

@[simp] theorem threeFormToThreeCochain_apply (K : DerivationLieLane R A)
    (η : DerivationOperatorForm K 3) (x y z : K.L) :
    threeFormToThreeCochain K η x y z = η ![x, y, z] :=
  rfl

theorem threeFormToThreeCochain_injective (K : DerivationLieLane R A) :
    Function.Injective (threeFormToThreeCochain K) := by
  intro η₁ η₂ h
  ext v
  have hv : v = ![v 0, v 1, v 2] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  exact congrArg (fun T : K.L →ₗ[R] K.L →ₗ[R] K.L →ₗ[R] A => T (v 0) (v 1) (v 2)) h

/-! ### Structural Noncommutative Graded Wedge Product (`ceWedgeBil` / `ceWedge`) -/

section WedgeConstruction

variable {R A : Type*}
variable [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

private def wedgeZeroLeft (K : LieActionLane R A) (q : ℕ) :
    ActionOperatorForm K 0 →ₗ[R] ActionOperatorForm K q →ₗ[R]
      ActionOperatorForm K (0 + q) where
  toFun a :=
    { toFun := fun η =>
        reindexForm (Nat.zero_add q).symm
          ((LinearMap.mul R A (a Fin.elim0)).compAlternatingMap η)
      map_add' := fun η₁ η₂ => by
        ext v
        simp
      map_smul' := fun c η => by
        ext v
        simp }
  map_add' a₁ a₂ := by
    ext η v
    simp
  map_smul' c a := by
    ext η v
    simp

private def wedgeSuccZero (K : LieActionLane R A) (p' : ℕ) :
    ActionOperatorForm K (p' + 1) →ₗ[R] ActionOperatorForm K 0 →ₗ[R]
      ActionOperatorForm K ((p' + 1) + 0) where
  toFun ω :=
    { toFun := fun b =>
        ((LinearMap.mul R A).flip (b Fin.elim0)).compAlternatingMap ω
      map_add' := fun b₁ b₂ => by
        ext v
        simp
      map_smul' := fun c b => by
        ext v
        simp }
  map_add' ω₁ ω₂ := by
    ext b v
    simp
  map_smul' c ω := by
    ext b v
    simp

private structure WedgeHistory (K : LieActionLane R A) (s : ℕ) where
  bil : ∀ {t : ℕ}, t ≤ s → ∀ {p q : ℕ}, p + q = t →
    ActionOperatorForm K p →ₗ[R] ActionOperatorForm K q →ₗ[R]
      ActionOperatorForm K (p + q)
  eq_zero_left : ∀ {t : ℕ} (ht : t ≤ s) {q : ℕ} (h : 0 + q = t),
    bil ht h = wedgeZeroLeft K q
  eq_succ_zero : ∀ {t : ℕ} (ht : t ≤ s) {p' : ℕ} (h : (p' + 1) + 0 = t),
    bil ht h = wedgeSuccZero K p'
  curry_succ_succ : ∀ {t : ℕ} (ht : t ≤ s) {p' q' : ℕ} (h : (p' + 1) + (q' + 1) = t)
    (ω : ActionOperatorForm K (p' + 1)) (η : ActionOperatorForm K (q' + 1)) (x : K.L),
    (bil ht h ω η).curryLeft x =
      reindexForm (by omega : p' + (q' + 1) = p' + 1 + q')
        (bil (by omega : p' + (q' + 1) ≤ s) rfl (ω.curryLeft x) η) +
        ((-1 : R) ^ (p' + 1)) •
          bil (by omega : (p' + 1) + q' ≤ s) rfl ω (η.curryLeft x)

private def wedgeNewBil (K : LieActionLane R A) {s : ℕ} (prev : WedgeHistory K s) :
    ∀ {p q : ℕ}, p + q = s + 1 →
      ActionOperatorForm K p →ₗ[R] ActionOperatorForm K q →ₗ[R]
        ActionOperatorForm K (p + q)
  | 0, q, _ => wedgeZeroLeft K q
  | p' + 1, 0, _ => wedgeSuccZero K p'
  | p' + 1, q' + 1, hpq =>
    { toFun := fun ω =>
        { toFun := fun η =>
            alternatingOfCurry
              { toFun := fun x =>
                  reindexForm (by omega : p' + (q' + 1) = p' + 1 + q')
                    (prev.bil (by omega) rfl (ω.curryLeft x) η) +
                    ((-1 : R) ^ (p' + 1)) •
                      prev.bil (by omega) rfl ω (η.curryLeft x)
                map_add' := fun x y => by
                  simp only [map_add, LinearMap.add_apply, reindexForm_add, smul_add]
                  abel
                map_smul' := fun c x => by
                  simp only [map_smul, LinearMap.smul_apply, reindexForm_smul, RingHom.id_apply]
                  rw [smul_add, smul_comm c ((-1 : R) ^ (p' + 1))] }
              (diag_of_curryLeft_self _ (by
                cases q' with
                | zero =>
                  intro x
                  dsimp
                  cases p' with
                  | zero =>
                    rw [prev.eq_zero_left (by omega : 0 + 1 ≤ s) rfl]
                    rw [prev.eq_succ_zero (by omega : 1 + 0 ≤ s) rfl]
                    ext w
                    have hw : w = Fin.elim0 := funext fun i => i.elim0
                    subst hw
                    simp [wedgeZeroLeft, wedgeSuccZero, pow_one]
                  | succ k =>
                    rw [reindexForm_curryLeft]
                    rw [prev.curry_succ_succ (by omega : (k + 1) + 1 ≤ s) rfl,
                      AlternatingMap.curryLeft_same, map_zero, LinearMap.zero_apply,
                      reindexForm_zero, reindexForm_add, reindexForm_zero, zero_add]
                    ext w
                    simp only [AlternatingMap.add_apply, reindexForm_apply, AlternatingMap.smul_apply,
                      AlternatingMap.curryLeft_apply_apply]
                    rw [prev.eq_succ_zero (by omega : (k + 1) + 0 ≤ s) rfl,
                      prev.eq_succ_zero (by omega : (k + 2) + 0 ≤ s) rfl]
                    simp only [wedgeSuccZero, LinearMap.coe_mk, AddHom.coe_mk,
                      LinearMap.compAlternatingMap_apply, LinearMap.flip_apply,
                      LinearMap.mul_apply', AlternatingMap.zero_apply,
                      fun_comp_finCongr_rfl]
                    have hpow : ((-1 : R) ^ (k + 1) + (-1 : R) ^ (k + 2)) = 0 := by
                      rw [pow_succ]
                      ring
                    change (-1 : R) ^ (k + 1) • ((ω.curryLeft x) w * (η.curryLeft x) Fin.elim0) +
                        (-1 : R) ^ (k + 2) • ((ω.curryLeft x) w * (η.curryLeft x) Fin.elim0) = 0
                    rw [← add_smul, hpow, zero_smul]
                | succ l =>
                  intro x
                  dsimp
                  cases p' with
                  | zero =>
                    rw [prev.eq_zero_left (by omega : 0 + (l + 2) ≤ s) rfl]
                    rw [prev.curry_succ_succ (by omega : 1 + (l + 1) ≤ s) rfl]
                    rw [prev.eq_zero_left (by omega : 0 + (l + 1) ≤ s) rfl]
                    rw [AlternatingMap.curryLeft_same, map_zero, smul_zero, add_zero]
                    ext w
                    simp [wedgeZeroLeft, pow_one]
                  | succ k =>
                    rw [reindexForm_curryLeft]
                    rw [prev.curry_succ_succ (by omega : (k + 1) + (l + 2) ≤ s) rfl]
                    rw [AlternatingMap.curryLeft_same, map_zero, LinearMap.zero_apply,
                      reindexForm_zero, reindexForm_add, reindexForm_zero, zero_add]
                    rw [prev.curry_succ_succ (by omega : (k + 2) + (l + 1) ≤ s) rfl]
                    rw [AlternatingMap.curryLeft_same, map_zero, smul_zero, add_zero]
                    ext w
                    simp only [AlternatingMap.add_apply, reindexForm_apply,
                      AlternatingMap.smul_apply, AlternatingMap.zero_apply]
                    have hpow : ((-1 : R) ^ (k + 1) + (-1 : R) ^ (k + 2)) = 0 := by
                      rw [pow_succ]
                      ring
                    rw [← add_smul, hpow, zero_smul] ))
          map_add' := fun η₁ η₂ => by
            apply alternating_ext_curryLeft
            intro x
            simp only [alternatingOfCurry_curryLeft, AlternatingMap.curryLeft_add,
              LinearMap.coe_mk, AddHom.coe_mk, map_add, LinearMap.add_apply]
            simp only [reindexForm_add, smul_add]
            abel
          map_smul' := fun c η => by
            apply alternating_ext_curryLeft
            intro x
            simp only [alternatingOfCurry_curryLeft, AlternatingMap.curryLeft_smul,
              LinearMap.coe_mk, AddHom.coe_mk, map_smul, LinearMap.smul_apply,
              RingHom.id_apply]
            simp only [reindexForm_smul]
            rw [smul_add, smul_comm c ((-1 : R) ^ (p' + 1))] }
      map_add' := fun ω₁ ω₂ => by
        apply LinearMap.ext
        intro η
        apply alternating_ext_curryLeft
        intro x
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
          alternatingOfCurry_curryLeft, AlternatingMap.curryLeft_add, map_add,
          reindexForm_add, smul_add]
        abel
      map_smul' := fun c ω => by
        apply LinearMap.ext
        intro η
        apply alternating_ext_curryLeft
        intro x
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
          alternatingOfCurry_curryLeft, AlternatingMap.curryLeft_smul,
          map_smul, reindexForm_smul, RingHom.id_apply]
        rw [smul_add, smul_comm c ((-1 : R) ^ (p' + 1))] }

private def buildWedgeHistory (K : LieActionLane R A) :
    ∀ s : ℕ, WedgeHistory K s
  | 0 =>
    { bil := fun {t} ht {p q} hpq =>
        match p, q with
        | 0, 0 => wedgeZeroLeft K 0
        | 0, _ + 1 => False.elim (by omega)
        | _ + 1, _ => False.elim (by omega)
      eq_zero_left := fun {t} ht {q} h => by
        cases q with
        | zero => rfl
        | succ _ => exact False.elim (by omega)
      eq_succ_zero := fun {t} ht {p'} h => False.elim (by omega)
      curry_succ_succ := fun {t} ht {p' q'} h => False.elim (by omega) }
  | s + 1 =>
    let prev := buildWedgeHistory K s
    { bil := fun {t} ht {p q} hpq =>
        if hts : t = s + 1 then
          wedgeNewBil K prev (hts ▸ hpq)
        else
          prev.bil (by omega) hpq
      eq_zero_left := fun {t} ht {q} h => by
        by_cases hts : t = s + 1
        · subst hts
          split_ifs
          all_goals first | exact absurd rfl (by assumption) | dsimp [wedgeNewBil]
        · split_ifs
          all_goals first | exact absurd (by assumption) hts | exact prev.eq_zero_left (by omega) h
      eq_succ_zero := fun {t} ht {p'} h => by
        by_cases hts : t = s + 1
        · subst hts
          split_ifs
          all_goals first | exact absurd rfl (by assumption) | dsimp [wedgeNewBil]
        · split_ifs
          all_goals first | exact absurd (by assumption) hts | exact prev.eq_succ_zero (by omega) h
      curry_succ_succ := fun {t} ht {p' q'} h ω η x => by
        by_cases hts : t = s + 1
        · subst hts
          dsimp
          split_ifs
          all_goals first | omega | simp only [wedgeNewBil, alternatingOfCurry_curryLeft, LinearMap.coe_mk, AddHom.coe_mk]
        · dsimp
          split_ifs
          all_goals first | omega | exact prev.curry_succ_succ (by omega) h ω η x }

private theorem buildWedgeHistory_bil_eq (K : LieActionLane R A)
    {s₁ s₂ t : ℕ} (h₁ : t ≤ s₁) (h₂ : t ≤ s₂) {p q : ℕ} (hpq : p + q = t) :
    (buildWedgeHistory K s₁).bil h₁ hpq = (buildWedgeHistory K s₂).bil h₂ hpq := by
  induction s₁ generalizing s₂ with
  | zero =>
    have ht0 : t = 0 := by omega
    subst ht0
    induction s₂ with
    | zero => rfl
    | succ s₂' ih =>
      dsimp [buildWedgeHistory]
      exact ih (Nat.zero_le s₂')
  | succ s₁' ih₁ =>
    by_cases hts₁ : t = s₁' + 1
    · subst hts₁
      induction s₂ with
      | zero => exact False.elim (by omega)
      | succ s₂' ih₂ =>
        by_cases hts₂ : s₁' + 1 = s₂' + 1
        · obtain rfl : s₁' = s₂' := Nat.succ.inj hts₂
          rfl
        · have hs : s₁' + 1 ≤ s₂' := by omega
          conv_rhs => dsimp [buildWedgeHistory]
          split_ifs
          exact ih₂ hs
    · have hs₁ : t ≤ s₁' := by omega
      conv_lhs => dsimp [buildWedgeHistory]
      split_ifs
      exact ih₁ hs₁ h₂

/-- Bilinear noncommutative graded wedge product on `ActionOperatorForm`. -/
def actionWedgeBil (K : LieActionLane R A) (p q : ℕ) :
    ActionOperatorForm K p →ₗ[R] ActionOperatorForm K q →ₗ[R]
      ActionOperatorForm K (p + q) :=
  (buildWedgeHistory K (p + q)).bil le_rfl rfl

/-- Graded wedge product on `ActionOperatorForm`. -/
def actionWedge (K : LieActionLane R A) {p q : ℕ}
    (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q) :
    ActionOperatorForm K (p + q) :=
  actionWedgeBil K p q ω η

@[simp] theorem actionWedge_zero_left (K : LieActionLane R A) {q : ℕ}
    (a : ActionOperatorForm K 0) (η : ActionOperatorForm K q) :
    actionWedge K a η =
      reindexForm (Nat.zero_add q).symm
        ((LinearMap.mul R A (a Fin.elim0)).compAlternatingMap η) := by
  dsimp [actionWedge, actionWedgeBil]
  rw [(buildWedgeHistory K (0 + q)).eq_zero_left le_rfl rfl]
  rfl

@[simp] theorem actionWedge_succ_zero (K : LieActionLane R A) {p' : ℕ}
    (ω : ActionOperatorForm K (p' + 1)) (b : ActionOperatorForm K 0) :
    actionWedge K ω b =
      ((LinearMap.mul R A).flip (b Fin.elim0)).compAlternatingMap ω := by
  dsimp [actionWedge, actionWedgeBil]
  rw [(buildWedgeHistory K ((p' + 1) + 0)).eq_succ_zero le_rfl rfl]
  rfl

@[simp] theorem actionWedge_zero_zero_apply (K : LieActionLane R A)
    (a b : ActionOperatorForm K 0) (v : Fin 0 → K.L) :
    actionWedge K a b v = a Fin.elim0 * b Fin.elim0 := by
  rw [actionWedge_zero_left]
  simp only [reindexForm_apply, LinearMap.compAlternatingMap_apply, LinearMap.mul_apply']
  congr 1
  congr 1
  exact funext fun i => i.elim0

@[simp] theorem actionWedge_succ_succ_curryLeft (K : LieActionLane R A) {p' q' : ℕ}
    (ω : ActionOperatorForm K (p' + 1)) (η : ActionOperatorForm K (q' + 1)) (x : K.L) :
    (actionWedge K ω η).curryLeft x =
      reindexForm (by omega : p' + (q' + 1) = p' + 1 + q')
        (actionWedge K (ω.curryLeft x) η) +
        ((-1 : R) ^ (p' + 1)) • actionWedge K ω (η.curryLeft x) := by
  dsimp [actionWedge, actionWedgeBil]
  rw [(buildWedgeHistory K ((p' + 1) + (q' + 1))).curry_succ_succ le_rfl rfl ω η x]
  rw [buildWedgeHistory_bil_eq K (by omega : p' + (q' + 1) ≤ (p' + 1) + (q' + 1)) le_rfl rfl]
  rw [buildWedgeHistory_bil_eq K (by omega : (p' + 1) + q' ≤ (p' + 1) + (q' + 1)) le_rfl rfl]

theorem actionWedge_zero_right (K : LieActionLane R A) {p : ℕ}
    (ω : ActionOperatorForm K p) (b : ActionOperatorForm K 0) :
    actionWedge K ω b = ((LinearMap.mul R A).flip (b Fin.elim0)).compAlternatingMap ω := by
  cases p with
  | zero =>
    ext v
    have hv : v = Fin.elim0 := funext fun i => i.elim0
    subst hv
    simp
  | succ p' =>
    exact actionWedge_succ_zero K ω b

@[simp] theorem actionWedge_one_one_apply (K : LieActionLane R A)
    (ω η : ActionOperatorForm K 1) (x y : K.L) :
    actionWedge K ω η ![x, y] = ω ![x] * η ![y] - ω ![y] * η ![x] := by
  have h0 : ![x, y] = Matrix.vecCons x ![y] := by
    ext i; fin_cases i <;> rfl
  rw [h0, ← AlternatingMap.curryLeft_apply_apply]
  rw [actionWedge_succ_succ_curryLeft]
  simp only [AlternatingMap.add_apply, reindexForm_apply, actionWedge_zero_left,
    AlternatingMap.smul_apply, actionWedge_succ_zero, LinearMap.compAlternatingMap_apply,
    LinearMap.mul_apply', LinearMap.flip_apply, AlternatingMap.curryLeft_apply_apply]
  have h1 : (Matrix.vecCons x (Fin.elim0 : Fin 0 → K.L)) = ![x] := by
    ext i; fin_cases i; rfl
  have h3 : ((![y] ∘ finCongr (by omega : 0 + 1 = 0 + 1 + 0)) ∘
      finCongr (Nat.zero_add 1).symm) = ![y] := by
    ext i; fin_cases i; rfl
  rw [h1, h3]
  simp [pow_one, sub_eq_add_neg]

theorem actionWedge_reindexForm_left (K : LieActionLane R A)
    {p₁ p₂ q : ℕ} (h : p₁ = p₂)
    (ω : ActionOperatorForm K p₁) (η : ActionOperatorForm K q) :
    actionWedge K (reindexForm h ω) η =
      reindexForm (congrArg (· + q) h) (actionWedge K ω η) := by
  subst h
  simp

theorem actionWedge_reindexForm_right (K : LieActionLane R A)
    {p q₁ q₂ : ℕ} (h : q₁ = q₂)
    (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q₁) :
    actionWedge K ω (reindexForm h η) =
      reindexForm (congrArg (p + ·) h) (actionWedge K ω η) := by
  subst h
  simp

theorem actionWedge_add_left (K : LieActionLane R A) {p q : ℕ}
    (ω₁ ω₂ : ActionOperatorForm K p) (η : ActionOperatorForm K q) :
    actionWedge K (ω₁ + ω₂) η = actionWedge K ω₁ η + actionWedge K ω₂ η := by
  simp [actionWedge]

theorem actionWedge_add_right (K : LieActionLane R A) {p q : ℕ}
    (ω : ActionOperatorForm K p) (η₁ η₂ : ActionOperatorForm K q) :
    actionWedge K ω (η₁ + η₂) = actionWedge K ω η₁ + actionWedge K ω η₂ := by
  simp [actionWedge]

theorem actionWedge_sub_left (K : LieActionLane R A) {p q : ℕ}
    (ω₁ ω₂ : ActionOperatorForm K p) (η : ActionOperatorForm K q) :
    actionWedge K (ω₁ - ω₂) η = actionWedge K ω₁ η - actionWedge K ω₂ η := by
  simp [actionWedge]

theorem actionWedge_sub_right (K : LieActionLane R A) {p q : ℕ}
    (ω : ActionOperatorForm K p) (η₁ η₂ : ActionOperatorForm K q) :
    actionWedge K ω (η₁ - η₂) = actionWedge K ω η₁ - actionWedge K ω η₂ := by
  simp [actionWedge]

theorem actionWedge_smul_left (K : LieActionLane R A) {p q : ℕ} (c : R)
    (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q) :
    actionWedge K (c • ω) η = c • actionWedge K ω η := by
  simp [actionWedge]

theorem actionWedge_smul_right (K : LieActionLane R A) {p q : ℕ} (c : R)
    (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q) :
    actionWedge K ω (c • η) = c • actionWedge K ω η := by
  simp [actionWedge]

theorem actionWedge_zero_val_left (K : LieActionLane R A) {p q : ℕ}
    (η : ActionOperatorForm K q) :
    actionWedge K (0 : ActionOperatorForm K p) η = 0 := by
  simp [actionWedge]

theorem actionWedge_zero_val_right (K : LieActionLane R A) {p q : ℕ}
    (ω : ActionOperatorForm K p) :
    actionWedge K ω (0 : ActionOperatorForm K q) = 0 := by
  simp [actionWedge]

theorem pullbackActionForm_actionWedge {K₁ K₂ : LieActionLane R A}
    (φ : K₁.L →ₗ[R] K₂.L) {p q : ℕ}
    (ω : ActionOperatorForm K₂ p) (η : ActionOperatorForm K₂ q) :
    pullbackActionForm φ (p + q) (actionWedge K₂ ω η) =
      actionWedge K₁ (pullbackActionForm φ p ω) (pullbackActionForm φ q η) := by
  induction p generalizing q with
  | zero =>
    ext v
    simp only [pullbackActionForm_apply, actionWedge_zero_left, reindexForm_apply,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply']
    have h0 : (fun i : Fin 0 => φ i.elim0) = Fin.elim0 := funext fun i => i.elim0
    rw [h0]
    rfl
  | succ p' ihp =>
    induction q with
    | zero =>
      ext v
      simp only [pullbackActionForm_apply, actionWedge_zero_right,
        LinearMap.compAlternatingMap_apply, LinearMap.flip_apply, LinearMap.mul_apply']
      have h0 : (fun i : Fin 0 => φ i.elim0) = Fin.elim0 := funext fun i => i.elim0
      rw [h0]
    | succ q' ihq =>
      apply alternating_ext_curryLeft
      intro x
      let α : ActionOperatorForm K₂ ((p' + 1) + (q' + 1)) := actionWedge K₂ ω η
      have hcur : (pullbackActionForm φ ((p' + 1) + (q' + 1)) α).curryLeft x =
          pullbackActionForm φ (p' + 1 + q')
            ((α : ActionOperatorForm K₂ ((p' + 1 + q') + 1)).curryLeft (φ x)) := by
        ext w
        simp only [AlternatingMap.curryLeft_apply_apply, pullbackActionForm_apply]
        congr 1
        ext i
        induction i using Fin.cases <;> rfl
      change (pullbackActionForm φ ((p' + 1) + (q' + 1)) α).curryLeft x = _
      rw [hcur]
      dsimp only [α]
      rw [actionWedge_succ_succ_curryLeft, actionWedge_succ_succ_curryLeft]
      simp only [map_add, map_smul, pullbackActionForm_curryLeft]
      congr 1
      · ext w
        simp only [reindexForm_apply, pullbackActionForm_apply]
        have := AlternatingMap.congr_fun (ihp (ω.curryLeft (φ x)) η) (w ∘ finCongr (by omega))
        simp only [pullbackActionForm_apply] at this
        have harg : (fun i => φ (w (finCongr (by omega : p' + (q' + 1) = p' + 1 + q') i))) =
            (fun i => φ (w i)) ∘ finCongr (by omega : p' + (q' + 1) = p' + 1 + q') := rfl
        exact (congrArg (actionWedge K₂ (ω.curryLeft (φ x)) η) harg.symm).trans this
      · rw [← ihq (η.curryLeft (φ x))]

/-- Bilinear noncommutative graded wedge product on `DerivationOperatorForm`. -/
def ceWedgeBil (K : DerivationLieLane R A) (p q : ℕ) :
    DerivationOperatorForm K p →ₗ[R] DerivationOperatorForm K q →ₗ[R]
      DerivationOperatorForm K (p + q) :=
  actionWedgeBil K.toLieActionLane p q

/-- Graded wedge product on `DerivationOperatorForm`. -/
def ceWedge (K : DerivationLieLane R A) {p q : ℕ}
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    DerivationOperatorForm K (p + q) :=
  ceWedgeBil K p q ω η

@[simp] theorem ceWedge_zero_left (K : DerivationLieLane R A) {q : ℕ}
    (a : DerivationOperatorForm K 0) (η : DerivationOperatorForm K q) :
    ceWedge K a η =
      reindexForm (Nat.zero_add q).symm
        ((LinearMap.mul R A (a Fin.elim0)).compAlternatingMap η) :=
  actionWedge_zero_left K.toLieActionLane a η

@[simp] theorem ceWedge_zero_right (K : DerivationLieLane R A) {p : ℕ}
    (ω : DerivationOperatorForm K p) (b : DerivationOperatorForm K 0) :
    ceWedge K ω b = ((LinearMap.mul R A).flip (b Fin.elim0)).compAlternatingMap ω :=
  actionWedge_zero_right K.toLieActionLane ω b

@[simp] theorem ceWedge_one_one_apply (K : DerivationLieLane R A)
    (ω η : DerivationOperatorForm K 1) (x y : K.L) :
    ceWedge K ω η ![x, y] = ω ![x] * η ![y] - ω ![y] * η ![x] :=
  actionWedge_one_one_apply K.toLieActionLane ω η x y

@[simp] theorem ceWedge_succ_succ_curryLeft (K : DerivationLieLane R A) {p' q' : ℕ}
    (ω : DerivationOperatorForm K (p' + 1)) (η : DerivationOperatorForm K (q' + 1)) (x : K.L) :
    (ceWedge K ω η).curryLeft x =
      reindexForm (by omega : p' + (q' + 1) = p' + 1 + q')
        (ceWedge K (ω.curryLeft x) η) +
        ((-1 : R) ^ (p' + 1)) • ceWedge K ω (η.curryLeft x) :=
  actionWedge_succ_succ_curryLeft K.toLieActionLane ω η x

theorem ceWedge_reindexForm_left (K : DerivationLieLane R A)
    {p₁ p₂ q : ℕ} (h : p₁ = p₂)
    (ω : DerivationOperatorForm K p₁) (η : DerivationOperatorForm K q) :
    ceWedge K (reindexForm h ω) η =
      reindexForm (congrArg (· + q) h) (ceWedge K ω η) :=
  actionWedge_reindexForm_left K.toLieActionLane h ω η

theorem ceWedge_reindexForm_right (K : DerivationLieLane R A)
    {p q₁ q₂ : ℕ} (h : q₁ = q₂)
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q₁) :
    ceWedge K ω (reindexForm h η) =
      reindexForm (congrArg (p + ·) h) (ceWedge K ω η) :=
  actionWedge_reindexForm_right K.toLieActionLane h ω η

theorem lieDeriv_actionWedge (K : LieActionLane R A) (hK : IsLeibnizAction K)
    (x : K.L) {p q : ℕ}
    (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q) :
    lieDeriv K x (actionWedge K ω η) =
      actionWedge K (lieDeriv K x ω) η + actionWedge K ω (lieDeriv K x η) := by
  induction p generalizing q with
  | zero =>
    ext v
    simp only [actionWedge_zero_left, lieDeriv_apply, reindexForm_apply,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply', AlternatingMap.add_apply]
    rw [hK x (ω Fin.elim0) (η (v ∘ finCongr (Nat.zero_add q).symm))]
    have hsum1 : ∑ i : Fin (0 + q), η (Function.update v i ⁅x, v i⁆ ∘ finCongr (Nat.zero_add q).symm) =
        ∑ j : Fin q, η (Function.update (v ∘ finCongr (Nat.zero_add q).symm) j
          ⁅x, (v ∘ finCongr (Nat.zero_add q).symm) j⁆) := by
      apply Fintype.sum_equiv (finCongr (Nat.zero_add q))
      intro i
      refine congrArg η (funext fun j => ?_)
      by_cases hij : j = (finCongr (Nat.zero_add q)) i
      · subst hij
        simp
      · have hji : (finCongr (Nat.zero_add q)).symm j ≠ i := fun h =>
          hij (by rw [← h]; simp)
        have h1 : Function.update v i ⁅x, v i⁆ ((finCongr (Nat.zero_add q)).symm j) =
            v ((finCongr (Nat.zero_add q)).symm j) := Function.update_of_ne hji _ v
        have h2 : Function.update (v ∘ finCongr (Nat.zero_add q).symm)
            ((finCongr (Nat.zero_add q)) i)
            ⁅x, (v ∘ finCongr (Nat.zero_add q).symm) ((finCongr (Nat.zero_add q)) i)⁆ j =
            v ((finCongr (Nat.zero_add q)).symm j) :=
          Function.update_of_ne hij _ _
        exact h1.trans h2.symm
    have hsum0 : ∑ i : Fin 0, ω (Function.update Fin.elim0 i ⁅x, Fin.elim0 i⁆) = 0 := by simp
    rw [← Finset.mul_sum, hsum1, hsum0, sub_zero, mul_sub]
    abel
  | succ p' ihp =>
    induction q with
    | zero =>
      ext v
      simp only [actionWedge_zero_right, lieDeriv_apply, LinearMap.compAlternatingMap_apply,
        LinearMap.flip_apply, LinearMap.mul_apply', AlternatingMap.add_apply]
      rw [hK x (ω v) (η Fin.elim0)]
      have hsum0 : ∑ i : Fin 0, η (Function.update Fin.elim0 i ⁅x, Fin.elim0 i⁆) = 0 := by simp
      have hsum1 : ∑ i : Fin (p' + 1 + 0),
          ω (Function.update v i ⁅x, v i⁆) * η Fin.elim0 =
          (∑ i : Fin (p' + 1), ω (Function.update v i ⁅x, v i⁆)) * η Fin.elim0 := by
        rw [Finset.sum_mul]
      rw [hsum1, hsum0, sub_zero, sub_mul]
      abel
    | succ q' ihq =>
      apply alternating_ext_curryLeft
      intro y
      rw [lieDeriv_curryLeft, actionWedge_succ_succ_curryLeft, actionWedge_succ_succ_curryLeft,
        AlternatingMap.curryLeft_add, LinearMap.add_apply, actionWedge_succ_succ_curryLeft,
        actionWedge_succ_succ_curryLeft]
      simp only [lieDeriv_add, lieDeriv_reindexForm, lieDeriv_smul,
        lieDeriv_curryLeft, actionWedge_sub_left, actionWedge_sub_right,
        reindexForm_sub, smul_sub]
      rw [ihp (ω.curryLeft y) η, ihq (η.curryLeft y)]
      simp only [reindexForm_add, smul_add]
      abel

theorem lieDeriv_ceWedge (K : DerivationLieLane R A) (x : K.L) {p q : ℕ}
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    lieDeriv K.toLieActionLane x (ceWedge K ω η) =
      ceWedge K (lieDeriv K.toLieActionLane x ω) η +
        ceWedge K ω (lieDeriv K.toLieActionLane x η) :=
  lieDeriv_actionWedge K.toLieActionLane K.isLeibnizAction x ω η

theorem actionExteriorDerivative_actionWedge (K : LieActionLane R A) (hK : IsLeibnizAction K) :
    ∀ (p q : ℕ) (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q),
      actionExteriorDerivative K (p + q) (actionWedge K ω η) =
        reindexForm (by omega : (p + 1) + q = p + q + 1)
          (actionWedge K (actionExteriorDerivative K p ω) η) +
          ((-1 : R) ^ p) •
            reindexForm (by omega : p + (q + 1) = p + q + 1)
              (actionWedge K ω (actionExteriorDerivative K q η))
  | 0, 0, ω, η => by
    apply alternating_ext_curryLeft
    intro x
    rw [actionExteriorDerivative_zero_curryLeft, lieDeriv_actionWedge K hK x ω η]
    rw [AlternatingMap.curryLeft_add, LinearMap.add_apply, reindexForm_curryLeft,
      AlternatingMap.curryLeft_smul, LinearMap.smul_apply, reindexForm_curryLeft]
    simp only [actionWedge_succ_zero, actionWedge_zero_left, actionExteriorDerivative_zero_curryLeft,
      pow_zero, one_smul, reindexForm_rfl, AlternatingMap.curryLeft_compAlternatingMap]
    ext w
    have hw : w = Fin.elim0 := funext fun i => i.elim0
    subst hw
    simp [LinearMap.flip_apply]
  | 0, q' + 1, ω, η => by
    apply alternating_ext_curryLeft
    intro x
    let α : ActionOperatorForm K (0 + (q' + 1)) := actionWedge K ω η
    have hlhs : (actionExteriorDerivative K (0 + (q' + 1)) α).curryLeft x =
        lieDeriv K x (α : ActionOperatorForm K ((0 + q') + 1)) -
          actionExteriorDerivative K (0 + q')
            ((α : ActionOperatorForm K ((0 + q') + 1)).curryLeft x) :=
      actionExteriorDerivative_succ_curryLeft K (n := 0 + q') α x
    change (actionExteriorDerivative K (0 + (q' + 1)) α).curryLeft x = _
    rw [hlhs]
    dsimp only [α]
    rw [lieDeriv_actionWedge K hK x ω η]
    rw [AlternatingMap.curryLeft_add, LinearMap.add_apply, reindexForm_curryLeft,
      AlternatingMap.curryLeft_smul, LinearMap.smul_apply, reindexForm_curryLeft]
    have h1 : (actionWedge K ω η).curryLeft x =
        actionWedge K ω (η.curryLeft x) := by
      rw [actionWedge_zero_left, reindexForm_curryLeft, actionWedge_zero_left]
      ext w
      simp [reindexForm_apply]
    rw [h1]
    have ih := actionExteriorDerivative_actionWedge K hK 0 q' ω (η.curryLeft x)
    rw [ih]
    rw [actionWedge_succ_succ_curryLeft]
    simp only [actionWedge_zero_left, reindexForm_curryLeft,
      actionExteriorDerivative_zero_curryLeft, pow_zero, one_smul, zero_add, pow_one,
      actionExteriorDerivative_succ_curryLeft,
      reindexForm_add, reindexForm_smul, reindexForm_trans,
      AlternatingMap.curryLeft_compAlternatingMap]
    ext w
    simp only [AlternatingMap.add_apply, AlternatingMap.neg_apply,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply', reindexForm_apply,
      lieDeriv_apply, sub_eq_add_neg, neg_one_smul, mul_add, mul_neg]
    abel
  | p' + 1, 0, ω, η => by
    apply alternating_ext_curryLeft
    intro x
    rw [actionExteriorDerivative_succ_curryLeft K (n := p' + 0), lieDeriv_actionWedge K hK x ω η]
    have h1 : (actionWedge K ω η).curryLeft x =
        actionWedge K (ω.curryLeft x) η := by
      rw [actionWedge_zero_right, actionWedge_zero_right]
      rfl
    rw [h1]
    have ih : actionExteriorDerivative K (p' + 0) (actionWedge K (ω.curryLeft x) η) =
        reindexForm (by omega : (p' + 1) + 0 = (p' + 0) + 1)
          (actionWedge K (actionExteriorDerivative K p' (ω.curryLeft x)) η) +
          ((-1 : R) ^ p') •
            reindexForm (by omega : p' + (0 + 1) = (p' + 0) + 1)
              (actionWedge K (ω.curryLeft x) (actionExteriorDerivative K 0 η)) :=
      actionExteriorDerivative_actionWedge K hK p' 0 (ω.curryLeft x) η
    rw [ih]
    rw [AlternatingMap.curryLeft_add, LinearMap.add_apply, reindexForm_curryLeft,
      AlternatingMap.curryLeft_smul, LinearMap.smul_apply, reindexForm_curryLeft]
    rw [actionWedge_succ_zero, actionWedge_succ_succ_curryLeft]
    have hmul : (actionWedge K (actionExteriorDerivative K (p' + 1) ω) η).curryLeft x =
        ((LinearMap.mul R A).flip (η Fin.elim0)).compAlternatingMap
          ((actionExteriorDerivative K (p' + 1) ω).curryLeft x) := by
      rw [actionWedge_succ_zero]
      rfl
    rw [hmul, actionExteriorDerivative_succ_curryLeft]
    simp only [actionExteriorDerivative_zero_curryLeft,
      reindexForm_add, reindexForm_smul, pow_succ, smul_add]
    ext w
    simp only [AlternatingMap.add_apply, AlternatingMap.sub_apply, AlternatingMap.smul_apply,
      actionWedge_zero_right, LinearMap.compAlternatingMap_apply, LinearMap.flip_apply,
      LinearMap.mul_apply', reindexForm_apply, smul_smul, fun_comp_finCongr_rfl]
    have hsq : ((-1 : R) ^ p' * -1) * ((-1 : R) ^ p' * -1) = 1 := by
      have h : ((-1 : R) * (-1)) = 1 := by ring
      calc ((-1 : R) ^ p' * -1) * ((-1 : R) ^ p' * -1)
          = ((-1 : R) ^ p' * (-1 : R) ^ p') * ((-1) * (-1)) := by ring
        _ = ((-1 : R) * (-1)) ^ p' * 1 := by rw [← mul_pow, h]
        _ = 1 := by simp [h]
    rw [hsq, one_smul, sub_mul]
    simp only [mul_neg, mul_one, neg_smul]
    abel
  | p' + 1, q' + 1, ω, η => by
    apply alternating_ext_curryLeft
    intro x
    let α : ActionOperatorForm K ((p' + 1) + (q' + 1)) := actionWedge K ω η
    have hlhs : (actionExteriorDerivative K ((p' + 1) + (q' + 1)) α).curryLeft x =
        lieDeriv K x (α : ActionOperatorForm K ((p' + 1 + q') + 1)) -
          actionExteriorDerivative K (p' + 1 + q')
            ((α : ActionOperatorForm K ((p' + 1 + q') + 1)).curryLeft x) :=
      actionExteriorDerivative_succ_curryLeft K (n := p' + 1 + q') α x
    change (actionExteriorDerivative K ((p' + 1) + (q' + 1)) α).curryLeft x = _
    rw [hlhs]
    dsimp only [α]
    rw [lieDeriv_actionWedge K hK x ω η]
    have hcur : (actionWedge K ω η).curryLeft x =
        reindexForm (by omega : p' + (q' + 1) = p' + 1 + q')
          (actionWedge K (ω.curryLeft x) η) +
        ((-1 : R) ^ (p' + 1)) • actionWedge K ω (η.curryLeft x) :=
      actionWedge_succ_succ_curryLeft K ω η x
    rw [hcur, map_add, map_smul, actionExteriorDerivative_reindexForm]
    have ihL := actionExteriorDerivative_actionWedge K hK p' (q' + 1) (ω.curryLeft x) η
    have ihR := actionExteriorDerivative_actionWedge K hK (p' + 1) q' ω (η.curryLeft x)
    rw [ihL, ihR]
    rw [AlternatingMap.curryLeft_add, LinearMap.add_apply, reindexForm_curryLeft,
      AlternatingMap.curryLeft_smul, LinearMap.smul_apply, reindexForm_curryLeft]
    rw [actionWedge_succ_succ_curryLeft, actionWedge_succ_succ_curryLeft]
    simp only [actionExteriorDerivative_succ_curryLeft, actionWedge_sub_left,
      actionWedge_sub_right, reindexForm_sub, reindexForm_add, reindexForm_smul,
      reindexForm_trans, smul_add, smul_sub, smul_smul, pow_succ]
    ext w
    simp only [AlternatingMap.add_apply, AlternatingMap.sub_apply, AlternatingMap.smul_apply,
      reindexForm_apply, fun_comp_finCongr_rfl]
    have hp : (-1 : R) ^ p' * (-1 : R) ^ p' = 1 := by
      rw [← mul_pow]
      have hneg1 : (-1 : R) * -1 = 1 := by ring
      simp [hneg1]
    simp only [mul_neg, mul_one, neg_mul, neg_neg, neg_smul, hp, one_smul]
    abel

/-- Graded Leibniz rule for `ceExteriorDerivative` and `ceWedge` at arbitrary degrees `p, q : ℕ`. -/
theorem ceExteriorDerivative_ceWedge (K : DerivationLieLane R A) {p q : ℕ}
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    ceExteriorDerivative K (p + q) (ceWedge K ω η) =
      reindexForm (by omega : (p + 1) + q = p + q + 1)
        (ceWedge K (ceExteriorDerivative K p ω) η) +
        ((-1 : R) ^ p) •
          reindexForm (by omega : p + (q + 1) = p + q + 1)
            (ceWedge K ω (ceExteriorDerivative K q η)) :=
  actionExteriorDerivative_actionWedge K.toLieActionLane K.isLeibnizAction p q ω η

end WedgeConstruction

end NoncommutativeDGA

section AssociativeWedgeAndCurvature

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Associativity of `actionWedge` over an associative algebra `A`. -/
theorem actionWedge_assoc (K : LieActionLane R A) :
    ∀ (p q r : ℕ) (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q)
      (θ : ActionOperatorForm K r),
      reindexForm (Nat.add_assoc p q r) (actionWedge K (actionWedge K ω η) θ) =
        actionWedge K ω (actionWedge K η θ)
  | 0, 0, r, ω, η, θ => by
    ext v
    simp only [reindexForm_apply, actionWedge_zero_left,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply', mul_assoc]
    congr 2
  | 0, q' + 1, 0, ω, η, θ => by
    ext v
    simp only [reindexForm_apply, actionWedge_zero_left, actionWedge_zero_right,
      LinearMap.compAlternatingMap_apply, LinearMap.flip_apply, LinearMap.mul_apply', mul_assoc]
    congr 2
  | 0, q' + 1, r' + 1, ω, η, θ => by
    apply alternating_ext_curryLeft
    intro x
    rw [reindexForm_curryLeft, actionWedge_succ_succ_curryLeft]
    have hL : (actionWedge K ω η).curryLeft x =
        reindexForm (by omega : 0 + q' = 0 + (q' + 1) - 1)
          (actionWedge K ω (η.curryLeft x)) := by
      rw [actionWedge_zero_left, reindexForm_curryLeft, actionWedge_zero_left, reindexForm_trans]
      rfl
    have hR : (actionWedge K ω (actionWedge K η θ)).curryLeft x =
        reindexForm (by omega : 0 + (q' + 1 + r') = 0 + (q' + 1 + (r' + 1)) - 1)
          (actionWedge K ω ((actionWedge K η θ).curryLeft x)) := by
      rw [actionWedge_zero_left, reindexForm_curryLeft, actionWedge_zero_left, reindexForm_trans]
      rfl
    rw [hL, actionWedge_reindexForm_left, hR, actionWedge_succ_succ_curryLeft,
      actionWedge_add_right, actionWedge_smul_right, actionWedge_reindexForm_right]
    have ih1 := actionWedge_assoc K 0 q' (r' + 1) ω (η.curryLeft x) θ
    have ih2 := actionWedge_assoc K 0 (q' + 1) r' ω η (θ.curryLeft x)
    rw [← ih1, ← ih2]
    simp only [reindexForm_add, reindexForm_smul, reindexForm_trans]
    ext w
    simp only [AlternatingMap.add_apply, AlternatingMap.smul_apply, reindexForm_apply]
    rw [show (-1 : R) ^ (Nat.add 0 q' + 1) = (-1 : R) ^ (q' + 1) by
      change (-1 : R) ^ (0 + q' + 1) = _
      rw [Nat.zero_add]]
  | p' + 1, 0, 0, ω, η, θ => by
    ext v
    simp only [reindexForm_apply, actionWedge_zero_right, LinearMap.compAlternatingMap_apply,
      LinearMap.flip_apply, LinearMap.mul_apply', mul_assoc]
    congr 2
  | p' + 1, 0, r' + 1, ω, η, θ => by
    apply alternating_ext_curryLeft
    intro x
    rw [reindexForm_curryLeft, actionWedge_succ_succ_curryLeft,
      actionWedge_succ_succ_curryLeft]
    have h0 : (actionWedge K ω η).curryLeft x = actionWedge K (ω.curryLeft x) η := by
      rw [actionWedge_zero_right, actionWedge_zero_right]
      rfl
    rw [h0]
    have h1 : (actionWedge K η θ).curryLeft x =
        reindexForm (by omega : 0 + r' = (0 + (r' + 1)) - 1)
          (actionWedge K η (θ.curryLeft x)) := by
      rw [actionWedge_zero_left, reindexForm_curryLeft, actionWedge_zero_left, reindexForm_trans]
      rfl
    rw [h1, actionWedge_reindexForm_right]
    have ih1 := actionWedge_assoc K p' 0 (r' + 1) (ω.curryLeft x) η θ
    have ih2 := actionWedge_assoc K (p' + 1) 0 r' ω η (θ.curryLeft x)
    rw [← ih1, ← ih2]
    simp only [reindexForm_add, reindexForm_smul, reindexForm_trans]
  | p' + 1, q' + 1, 0, ω, η, θ => by
    apply alternating_ext_curryLeft
    intro x
    rw [reindexForm_curryLeft]
    have hL : (actionWedge K (actionWedge K ω η) θ).curryLeft x =
        actionWedge K ((actionWedge K ω η).curryLeft x) θ := by
      rw [actionWedge_zero_right, actionWedge_zero_right]
      rfl
    have hR' : (actionWedge K η θ).curryLeft x = actionWedge K (η.curryLeft x) θ := by
      rw [actionWedge_zero_right, actionWedge_zero_right]
      rfl
    rw [hL, actionWedge_succ_succ_curryLeft, actionWedge_succ_succ_curryLeft, hR',
      actionWedge_add_left, actionWedge_smul_left, actionWedge_reindexForm_left]
    have ih1 := actionWedge_assoc K p' (q' + 1) 0 (ω.curryLeft x) η θ
    have ih2 := actionWedge_assoc K (p' + 1) q' 0 ω (η.curryLeft x) θ
    rw [← ih1, ← ih2]
    simp only [reindexForm_add, reindexForm_smul, reindexForm_trans]
  | p' + 1, q' + 1, r' + 1, ω, η, θ => by
    apply alternating_ext_curryLeft
    intro x
    rw [reindexForm_curryLeft]
    rw [actionWedge_succ_succ_curryLeft, actionWedge_succ_succ_curryLeft,
      actionWedge_succ_succ_curryLeft, actionWedge_succ_succ_curryLeft]
    simp only [reindexForm_add, reindexForm_smul,
      actionWedge_add_left, actionWedge_smul_left,
      actionWedge_add_right, actionWedge_smul_right,
      actionWedge_reindexForm_left, actionWedge_reindexForm_right, reindexForm_trans]
    have ih1 := actionWedge_assoc K p' (q' + 1) (r' + 1) (ω.curryLeft x) η θ
    have ih2 := actionWedge_assoc K (p' + 1) q' (r' + 1) ω (η.curryLeft x) θ
    have ih3 := actionWedge_assoc K (p' + 1) (q' + 1) r' ω η (θ.curryLeft x)
    rw [← ih1, ← ih2, ← ih3]
    simp only [reindexForm_trans, smul_add, smul_smul, pow_add, add_assoc]
    ext w
    simp only [AlternatingMap.add_apply, AlternatingMap.smul_apply, reindexForm_apply]
    rw [show (-1 : R) ^ ((p' + 1).add q') * (-1 : R) ^ 1 =
        (-1 : R) ^ p' * (-1 : R) ^ 1 * ((-1 : R) ^ q' * (-1 : R) ^ 1) by
      change (-1 : R) ^ (p' + 1 + q') * (-1 : R) ^ 1 = _
      rw [pow_add, pow_add, pow_one]
      ring]
termination_by p q r => p + q + r

theorem ceWedge_assoc (K : DerivationLieLane R A) {p q r : ℕ}
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q)
    (θ : DerivationOperatorForm K r) :
    reindexForm (Nat.add_assoc p q r) (ceWedge K (ceWedge K ω η) θ) =
      ceWedge K ω (ceWedge K η θ) :=
  actionWedge_assoc K.toLieActionLane p q r ω η θ

@[simp] theorem ceWedge_add_left (K : DerivationLieLane R A) {p q : ℕ}
    (ω₁ ω₂ : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    ceWedge K (ω₁ + ω₂) η = ceWedge K ω₁ η + ceWedge K ω₂ η :=
  actionWedge_add_left K.toLieActionLane ω₁ ω₂ η

@[simp] theorem ceWedge_add_right (K : DerivationLieLane R A) {p q : ℕ}
    (ω : DerivationOperatorForm K p) (η₁ η₂ : DerivationOperatorForm K q) :
    ceWedge K ω (η₁ + η₂) = ceWedge K ω η₁ + ceWedge K ω η₂ :=
  actionWedge_add_right K.toLieActionLane ω η₁ η₂

@[simp] theorem ceWedge_sub_left (K : DerivationLieLane R A) {p q : ℕ}
    (ω₁ ω₂ : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    ceWedge K (ω₁ - ω₂) η = ceWedge K ω₁ η - ceWedge K ω₂ η :=
  actionWedge_sub_left K.toLieActionLane ω₁ ω₂ η

@[simp] theorem ceWedge_sub_right (K : DerivationLieLane R A) {p q : ℕ}
    (ω : DerivationOperatorForm K p) (η₁ η₂ : DerivationOperatorForm K q) :
    ceWedge K ω (η₁ - η₂) = ceWedge K ω η₁ - ceWedge K ω η₂ :=
  actionWedge_sub_right K.toLieActionLane ω η₁ η₂

@[simp] theorem ceWedge_smul_left (K : DerivationLieLane R A) {p q : ℕ} (c : R)
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    ceWedge K (c • ω) η = c • ceWedge K ω η :=
  actionWedge_smul_left K.toLieActionLane c ω η

@[simp] theorem ceWedge_smul_right (K : DerivationLieLane R A) {p q : ℕ} (c : R)
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    ceWedge K ω (c • η) = c • ceWedge K ω η :=
  actionWedge_smul_right K.toLieActionLane c ω η

/-- Arbitrary-degree curvature `F = dΓ + Γ ∧ Γ` on `DerivationOperatorForm K 1`. -/
def ceCurvature (K : DerivationLieLane R A) (Γ : DerivationOperatorForm K 1) :
    DerivationOperatorForm K 2 :=
  ceExteriorDerivative K 1 Γ + ceWedge K Γ Γ

/-- Arbitrary-degree covariant exterior derivative
`d_Γ ω = dω + Γ ∧ ω - (-1)^n ω ∧ Γ`. -/
def covariantExteriorDerivativeN (K : DerivationLieLane R A)
    (Γ : DerivationOperatorForm K 1) (n : ℕ) :
    DerivationOperatorForm K n →ₗ[R] DerivationOperatorForm K (n + 1) where
  toFun ω :=
    ceExteriorDerivative K n ω +
      reindexForm (Nat.add_comm 1 n) (ceWedge K Γ ω) -
        ((-1 : R) ^ n) • ceWedge K ω Γ
  map_add' ω₁ ω₂ := by
    simp only [map_add, ceWedge_add_right, ceWedge_add_left, reindexForm_add, smul_add]
    abel
  map_smul' c ω := by
    simp only [map_smul, ceWedge_smul_right, ceWedge_smul_left, reindexForm_smul, RingHom.id_apply]
    rw [smul_sub, smul_add, smul_comm c ((-1 : R) ^ n)]

/-- Arbitrary-degree Ricci identity: `d_Γ (d_Γ ω) = F ∧ ω - ω ∧ F`. -/
theorem covariantExteriorDerivativeN_comp (K : DerivationLieLane R A)
    (Γ : DerivationOperatorForm K 1) (n : ℕ) (ω : DerivationOperatorForm K n) :
    covariantExteriorDerivativeN K Γ (n + 1) (covariantExteriorDerivativeN K Γ n ω) =
      reindexForm (Nat.add_comm 2 n) (ceWedge K (ceCurvature K Γ) ω) -
        ceWedge K ω (ceCurvature K Γ) := by
  dsimp [covariantExteriorDerivativeN, ceCurvature]
  simp only [map_add, map_sub, map_smul, ceExteriorDerivative_succ_comp, zero_add,
    ceExteriorDerivative_reindexForm, ceExteriorDerivative_ceWedge,
    ceWedge_add_left, ceWedge_add_right, ceWedge_sub_left, ceWedge_sub_right,
    ceWedge_smul_left, ceWedge_smul_right,
    reindexForm_add, reindexForm_sub, reindexForm_smul, reindexForm_trans,
    pow_one, neg_one_smul, smul_add, smul_smul]
  have hsq : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
    rw [← mul_pow]
    have hneg1 : (-1 : R) * -1 = 1 := by ring
    simp [hneg1]
  have hsucc : (-1 : R) ^ (n + 1) = -((-1 : R) ^ n) := by
    rw [pow_succ]
    ring
  rw [hsucc, hsq, one_smul]
  have hassoc1 :
      reindexForm (by omega : (1 + 1) + n = n + 2) (ceWedge K (ceWedge K Γ Γ) ω) =
        reindexForm (by omega : 1 + (n + 1) = n + 2)
          (ceWedge K Γ (reindexForm (Nat.add_comm 1 n) (ceWedge K Γ ω))) := by
    rw [ceWedge_reindexForm_right, reindexForm_trans, ← ceWedge_assoc K Γ Γ ω, reindexForm_trans]
  have hassoc2 :
      reindexForm (by omega : 1 + (n + 1) = n + 2)
          (ceWedge K Γ (ceWedge K ω Γ)) =
        ceWedge K (reindexForm (Nat.add_comm 1 n) (ceWedge K Γ ω)) Γ := by
    rw [ceWedge_reindexForm_left, ← ceWedge_assoc K Γ ω Γ, reindexForm_trans]
  have hassoc3 :
      ceWedge K (ceWedge K ω Γ) Γ = ceWedge K ω (ceWedge K Γ Γ) := by
    simpa [reindexForm_rfl] using ceWedge_assoc K ω Γ Γ
  rw [← hassoc1, hassoc2, hassoc3]
  ext v
  simp only [AlternatingMap.add_apply, AlternatingMap.sub_apply, AlternatingMap.neg_apply,
    AlternatingMap.smul_apply, reindexForm_apply, fun_comp_finCongr_rfl]
  simp only [sub_eq_add_neg, smul_add, smul_neg, smul_smul, neg_mul, neg_neg, hsq,
    one_smul, neg_smul]
  abel

theorem covariantExteriorDerivativeN_comp_of_flat (K : DerivationLieLane R A)
    (Γ : DerivationOperatorForm K 1) (hΓ : ceCurvature K Γ = 0)
    (n : ℕ) (ω : DerivationOperatorForm K n) :
    covariantExteriorDerivativeN K Γ (n + 1) (covariantExteriorDerivativeN K Γ n ω) = 0 := by
  rw [covariantExteriorDerivativeN_comp, hΓ]
  simp [ceWedge]

/-- Arbitrary-degree covariant Bianchi identity: `d_Γ F = 0`. -/
theorem ceCurvature_bianchi (K : DerivationLieLane R A)
    (Γ : DerivationOperatorForm K 1) :
    covariantExteriorDerivativeN K Γ 2 (ceCurvature K Γ) = 0 := by
  dsimp [covariantExteriorDerivativeN, ceCurvature]
  rw [map_add, ceExteriorDerivative_succ_comp, zero_add]
  have hdw : ceExteriorDerivative K 2 (ceWedge K Γ Γ) =
      reindexForm (by omega : (1 + 1) + 1 = 2 + 1) (ceWedge K (ceExteriorDerivative K 1 Γ) Γ) +
        ((-1 : R) ^ (1 : ℕ)) •
          reindexForm (by omega : 1 + (1 + 1) = 2 + 1) (ceWedge K Γ (ceExteriorDerivative K 1 Γ)) :=
    ceExteriorDerivative_ceWedge K Γ Γ
  rw [hdw]
  simp only [ceWedge_add_left, ceWedge_add_right, reindexForm_add, pow_one, neg_one_smul, pow_two]
  have h1 : (-1 : R) * (-1 : R) = 1 := by ring
  rw [h1, one_smul]
  have hassoc : ceWedge K (ceWedge K Γ Γ) Γ = ceWedge K Γ (ceWedge K Γ Γ) := by
    simpa [reindexForm_rfl] using ceWedge_assoc K Γ Γ Γ
  rw [hassoc]
  ext v
  have hv : v ∘ finCongr (Nat.add_comm 1 2) = v := funext fun i => rfl
  simp only [AlternatingMap.add_apply, AlternatingMap.sub_apply, AlternatingMap.neg_apply,
    AlternatingMap.zero_apply, reindexForm_apply, hv]
  abel

end AssociativeWedgeAndCurvature

/-! ## Commutative specialization (`[CommRing A]`) and `deRhamComplex` / `DeRhamBridge` -/

section CommutativeSpecialization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem actionWedge_comm_of_commRing (K : LieActionLane R A) :
    ∀ (p q : ℕ) (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q),
      actionWedge K ω η =
        ((-1 : R) ^ (p * q)) •
          reindexForm (Nat.add_comm q p) (actionWedge K η ω)
  | 0, q, ω, η => by
    ext v
    simp only [Nat.zero_mul, pow_zero, one_smul, reindexForm_apply, actionWedge_zero_left,
      actionWedge_zero_right, LinearMap.compAlternatingMap_apply, LinearMap.mul_apply',
      LinearMap.flip_apply]
    rw [mul_comm]
  | p' + 1, 0, ω, η => by
    ext v
    simp only [Nat.mul_zero, pow_zero, one_smul, reindexForm_apply, actionWedge_zero_left,
      actionWedge_zero_right, LinearMap.compAlternatingMap_apply, LinearMap.mul_apply',
      LinearMap.flip_apply]
    rw [mul_comm]
    congr 2
  | p' + 1, q' + 1, ω, η => by
    apply alternating_ext_curryLeft
    intro x
    change (actionWedge K ω η).curryLeft x =
      (((-1 : R) ^ ((p' + 1) * (q' + 1))) •
        reindexForm (Nat.add_comm (q' + 1) (p' + 1)) (actionWedge K η ω)).curryLeft x
    rw [actionWedge_succ_succ_curryLeft, AlternatingMap.curryLeft_smul, LinearMap.smul_apply,
      reindexForm_curryLeft, actionWedge_succ_succ_curryLeft]
    rw [actionWedge_comm_of_commRing K p' (q' + 1) (ω.curryLeft x) η]
    rw [actionWedge_comm_of_commRing K (p' + 1) q' ω (η.curryLeft x)]
    simp only [reindexForm_add, reindexForm_smul, reindexForm_trans, smul_add, smul_smul]
    have hpow1 : ((-1 : R) ^ ((p' + 1) * (q' + 1)) * (-1 : R) ^ (q' + 1)) =
        (-1 : R) ^ (p' * (q' + 1)) := by
      have hexp : (p' + 1) * (q' + 1) + (q' + 1) = p' * (q' + 1) + (q' + 1) * 2 := by ring
      have hneg1 : (-1 : R) ^ 2 = 1 := by ring
      rw [← pow_add, hexp, pow_add]
      conv_lhs => rhs; rw [mul_comm, pow_mul, hneg1, one_pow]
      rw [mul_one]
    have hpow2 : ((-1 : R) ^ (p' + 1) * (-1 : R) ^ ((p' + 1) * q')) =
        (-1 : R) ^ ((p' + 1) * (q' + 1)) := by
      rw [← pow_add]
      congr 1
      ring
    ext w
    simp only [AlternatingMap.add_apply, AlternatingMap.smul_apply, reindexForm_apply]
    rw [hpow1, hpow2, add_comm]

theorem ceWedge_comm_of_commRing (K : DerivationLieLane R A) {p q : ℕ}
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    ceWedge K ω η =
      ((-1 : R) ^ (p * q)) •
        reindexForm (Nat.add_comm q p) (ceWedge K η ω) :=
  actionWedge_comm_of_commRing K.toLieActionLane p q ω η

theorem ceWedge_comm_cast_of_commRing (K : DerivationLieLane R A) {p q : ℕ}
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    ceWedge K ω η =
      cast (congrArg (DerivationOperatorForm K) (Nat.add_comm q p))
        (((-1 : R) ^ (p * q)) • ceWedge K η ω) := by
  rw [ceWedge_comm_of_commRing K ω η, ← reindexForm_smul, reindexForm_eq_cast]

theorem ceWedge_self_one_eq_zero_of_commRing (K : DerivationLieLane R A)
    (ω : DerivationOperatorForm K 1) :
    ceWedge K ω ω = 0 := by
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i; fin_cases i <;> rfl
  rw [hv, ceWedge_one_one_apply, mul_comm, sub_self]
  rfl

theorem ceCurvature_eq_exteriorDerivative_of_commRing (K : DerivationLieLane R A)
    (Γ : DerivationOperatorForm K 1) :
    ceCurvature K Γ = ceExteriorDerivative K 1 Γ := by
  rw [ceCurvature, ceWedge_self_one_eq_zero_of_commRing, add_zero]

theorem covariantExteriorDerivativeN_eq_ceExteriorDerivative_of_commRing
    (K : DerivationLieLane R A) (Γ : DerivationOperatorForm K 1)
    (n : ℕ) (ω : DerivationOperatorForm K n) :
    covariantExteriorDerivativeN K Γ n ω = ceExteriorDerivative K n ω := by
  dsimp [covariantExteriorDerivativeN]
  have hcomm := ceWedge_comm_of_commRing K Γ ω
  rw [one_mul] at hcomm
  have h1 : reindexForm (Nat.add_comm 1 n) (ceWedge K Γ ω) =
      ((-1 : R) ^ n) • ceWedge K ω Γ := by
    rw [hcomm, reindexForm_smul, reindexForm_trans, reindexForm_rfl]
  rw [h1, add_sub_cancel_right]

end CommutativeSpecialization

section DeRhamInstantiation

open InfoGeometry.Spectral.Cohomology.deRham

universe u

/-- `BUCKET 1`: Any `DerivationLieLane ℝ A` (with `K.L : Type u` and `A : Type u`)
natively instantiates `Spectral.Cohomology.deRham.DifferentialForms M A`. -/
@[instance_reducible]
def derivationDifferentialForms
    (M : Type*) [TopologicalSpace M] [SmoothManifold M]
    {A : Type u} [Ring A] [Algebra ℝ A]
    (K : DerivationLieLane.{0, u, u} ℝ A) :
    DifferentialForms M A where
  forms k := DerivationOperatorForm K k
  formsAddCommGroup _ := inferInstance
  formsModule _ := inferInstance
  d k := ceExteriorDerivative K k
  d_sq_zero k ω := ceExteriorDerivative_succ_comp K k ω

/-- `BUCKET 1` DGA + `BUCKET 2` metric/HK parameters:
When `[CommRing A]`, `DerivationOperatorForm K` instantiates `deRhamComplex M A`
given explicit `hodge`, `hkOperator`, and `hk_sq_zero` parameters. -/
def derivationDeRhamComplex
    (M : Type*) [TopologicalSpace M] [SmoothManifold M]
    {A : Type u} [CommRing A] [Algebra ℝ A]
    (K : DerivationLieLane.{0, u, u} ℝ A)
    (hodge : ∀ k, DerivationOperatorForm K k →ₗ[ℝ]
      DerivationOperatorForm K ((inferInstance : SmoothManifold M).manifoldDim - k))
    (hkOperator : ∀ k, Module.End ℝ (DerivationOperatorForm K k))
    (hk_sq_zero : ∀ k, (hkOperator k).comp (hkOperator k) = 0) :
    @deRhamComplex M _ _ A _ _ (derivationDifferentialForms M K) :=
  letI : DifferentialForms M A := derivationDifferentialForms M K
  { wedge := fun _ _ ω η => ceWedge K ω η
    wedge_assoc := fun p q r ω η θ => by
      rw [← reindexForm_eq_cast (Nat.add_assoc p q r)]
      exact ceWedge_assoc K ω η θ
    wedge_graded_comm := fun p q ω η => ceWedge_comm_cast_of_commRing K ω η
    d_wedge := fun p q ω η => by
      rw [← reindexForm_eq_cast (by omega : p + q + 1 = (p + 1) + q)]
      change reindexForm (by omega : p + q + 1 = (p + 1) + q)
          (ceExteriorDerivative K (p + q) (ceWedge K ω η)) =
        ceWedge K (ceExteriorDerivative K p ω) η +
          cast (congrArg (DerivationOperatorForm K) (by omega : p + (q + 1) = (p + 1) + q))
            ((-1 : ℝ) ^ p • ceWedge K ω (ceExteriorDerivative K q η))
      rw [ceExteriorDerivative_ceWedge, reindexForm_add, reindexForm_trans, reindexForm_rfl,
        reindexForm_smul, reindexForm_trans, ← reindexForm_smul, reindexForm_eq_cast]
    hodge := hodge
    hkOperator := hkOperator
    hk_sq_zero := hk_sq_zero }

end DeRhamInstantiation

section ContinuousChartAlignment

open InfoGeometry.Continuous.DeRhamBridge

/-- Scalar functions on `Chart α` that are Fréchet differentiable at `x`. -/
def DifferentiableAtSubalgebra (α : Type*) [Fintype α] (x : Chart α) :
    Subalgebra ℝ (Chart α → ℝ) where
  carrier := { f | DifferentiableAt ℝ f x }
  mul_mem' hf hg := hf.mul hg
  one_mem' := differentiableAt_const 1
  add_mem' hf hg := hf.add hg
  zero_mem' := differentiableAt_const 0
  algebraMap_mem' r := differentiableAt_const r

/-- Pointwise directional-derivative `LieActionLane` on `DifferentiableAtSubalgebra α x`
(abelian tangent vectors `Chart α` acting by directional Fréchet derivative at `x`
as constant functions). -/
def chartDirectionalLieAction (α : Type*) [Fintype α] (x : Chart α) :
    LieActionLane ℝ (DifferentiableAtSubalgebra α x) :=
  letI : LieRing (Chart α) :=
    { bracket := fun _ _ => 0
      add_lie := fun _ _ _ => (add_zero 0).symm
      lie_add := fun _ _ _ => (add_zero 0).symm
      lie_self := fun _ => rfl
      leibniz_lie := fun _ _ _ => (add_zero 0).symm }
  letI : LieAlgebra ℝ (Chart α) :=
    { lie_smul := fun _ _ _ => (smul_zero _).symm }
  { L := Chart α
    lieRing := ‹_›
    lieAlgebra := ‹_›
    act :=
      { toFun := fun v =>
          { toFun := fun f =>
              ⟨fun _ => fderiv ℝ f.1 x v, differentiableAt_const _⟩
            map_add' := fun f g => Subtype.ext (funext fun _ => by
              simp [fderiv_add f.2 g.2])
            map_smul' := fun r f => Subtype.ext (funext fun _ => by
              simp [fderiv_const_smul f.2]) }
        map_add' := fun v w => by
          ext f y
          simp
        map_smul' := fun r v => by
          ext f y
          simp
        map_lie' := fun {v w} => by
          ext f y
          change (fderiv ℝ f.1 x) (0 : Chart α) =
            (fderiv ℝ (fun _ => (fderiv ℝ f.1 x) w) x) v -
              (fderiv ℝ (fun _ => (fderiv ℝ f.1 x) v) x) w
          simp } }

theorem chartDirectionalLieAction_leibniz_at (α : Type*) [Fintype α] (x : Chart α)
    (v : Chart α) (f g : DifferentiableAtSubalgebra α x) :
    ((chartDirectionalLieAction α x).operatorAction v (f * g)).1 x =
      ((chartDirectionalLieAction α x).operatorAction v f * g +
        f * (chartDirectionalLieAction α x).operatorAction v g).1 x := by
  change fderiv ℝ (f.1 * g.1) x v =
    fderiv ℝ f.1 x v * g.1 x + f.1 x * fderiv ℝ g.1 x v
  rw [fderiv_mul f.2 g.2]
  simp only [add_apply, smul_apply, smul_eq_mul, mul_comm (g.1 x)]
  ring

/-- Alignment between `actionExteriorDerivative` on `chartDirectionalLieAction α x`
and `Continuous.DeRhamBridge.exactOneForm_eq_mathlib_extDeriv` for the logarithmic
coordinate potential `zeroForm i`. -/
theorem actionExteriorDerivative_zero_chart_eq_extDeriv
    {α : Type*} [Fintype α] (i : α) {x : Chart α} (hx : x i ≠ 0) (v : Chart α) :
    ((actionExteriorDerivative (chartDirectionalLieAction α x) 0
        (AlternatingMap.constLinearEquivOfIsEmpty
          ⟨zeroForm i, (zeroForm_hasFDerivAt i hx).differentiableAt⟩) ![v]).1 x) =
      extDeriv
        (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ (Chart α) (Fin 0) (zeroForm i y))
        x ![v] := by
  rw [actionExteriorDerivative_zero_apply]
  rw [exactOneForm_eq_mathlib_extDeriv i hx]
  dsimp [chartDirectionalLieAction]
  change fderiv ℝ (zeroForm i) x v = exactOneForm i x v
  rw [exactOneForm_is_derivative i hx]

end ContinuousChartAlignment

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

