/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Category.ModuleCat.Limits
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# Holographic Tower: Successor Maps and an Algebraic Module Colimit

This module formalizes successor towers of modules, compatible stage families,
and the canonical algebraic direct limit in `ModuleCat`. It also proves causal
cone monotonicity and finite-stage projector intertwining:
1. `HolographicTower`: Direct inductive tower of module spaces with linear bonding maps
   `iota : ∀ n, T n →ₗ[R] T (n + 1)`.
2. `iotaSeq`: Multi-step sequential bonding map along the tower.
3. `iotaSeq_eq_tensorTowerColimit_iota_seq`: Proved isomorphism with canonical `TensorTowerColimit.iota_seq`.
4. `HolographicColimitCocone`: Compatible family into an arbitrary target; this alone is not a colimit witness.
5. `psi_comp_iotaSeq`: Multi-step cocone sequence compatibility `(psi (n + m)).comp (iotaSeq n m) = psi n`.
6. `compatible_family_evaluation_invariant`: Evaluation invariance from supplied stage compatibility equations.
7. `CausalConeFamily` & `causal_cone_seq_stable`: Preservation of causal cone membership across sequential stages.
8. `ProjectorFamily` & `projector_comm_iotaSeq`: Sequential intertwining of idempotent stage projectors with bonding maps.
9. `complement_idempotent`, `projector_annihilation`, & `complement_intertwines_iotaSeq`:
   Complementary idempotent $Q = \text{id} - P$, orthogonal annihilation $PQ = 0$, and sequential intertwining of $Q$.
-/

namespace InfoGeometry.Canonical.HolographicColimitContinuum

open InfoGeometry.Canonical
open CategoryTheory
open CategoryTheory.Limits

/-! ### 1. Discrete Holographic Tower and Sequential Bonding -/

/-- Direct inductive tower of modules with linear successor maps. -/
structure HolographicTower {R : Type*} [CommRing R]
    (T : ℕ → Type*) [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)] where
  iota : ∀ n, T n →ₗ[R] T (n + 1)

/-- Constructive model witness: constant module tower with zero bonding maps. -/
def zeroHolographicTower {R : Type*} [CommRing R] :
    HolographicTower (R := R) (fun _ : ℕ => R) :=
  ⟨fun _ => 0⟩

instance {R : Type*} [CommRing R] {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)] :
    Inhabited (HolographicTower (R := R) T) :=
  ⟨⟨fun _ => 0⟩⟩

/-- Sequential composition of bonding maps across `m` steps. -/
def iotaSeq {R : Type*} [CommRing R] {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (n : ℕ) : ∀ m, T n →ₗ[R] T (n + m)
  | 0 => LinearMap.id
  | m + 1 => (tower.iota (n + m)).comp (iotaSeq tower n m)

@[simp]
theorem iotaSeq_zero {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (n : ℕ) :
    iotaSeq tower n 0 = LinearMap.id := rfl

@[simp]
theorem iotaSeq_succ {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (n m : ℕ) :
    iotaSeq tower n (m + 1) = (tower.iota (n + m)).comp (iotaSeq tower n m) := rfl

/-- Connection theorem: Exact identity with canonical TensorTowerColimit `iota_seq`. -/
theorem iotaSeq_eq_tensorTowerColimit_iota_seq {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (n m : ℕ) :
    iotaSeq tower n m = iota_seq T tower.iota n m := by
  induction' m with m ih
  · rfl
  · dsimp [iotaSeq, iota_seq]
    rw [ih]

/-! ### 2. Native Mathlib Module Colimit -/

/-- The transition map from stage `m` to stage `n`, for `m ≤ n`. -/
def holographicStageMap {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (m n : ℕ) (h : m ≤ n) :
    T m →ₗ[R] T n :=
  Nat.leRecOn h
    (C := fun k => T m →ₗ[R] T k)
    (fun {k} f => (tower.iota k).comp f)
    (LinearMap.id : T m →ₗ[R] T m)

@[simp]
theorem holographicStageMap_refl {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (m : ℕ) :
    holographicStageMap tower m m le_rfl = LinearMap.id := by
  simpa [holographicStageMap] using
    (Nat.leRecOn_self
      (C := fun k => T m →ₗ[R] T k)
      (next := fun {k} f => (tower.iota k).comp f)
      (x := (LinearMap.id : T m →ₗ[R] T m)))

theorem holographicStageMap_succ {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (m n : ℕ) (h : m ≤ n) :
    holographicStageMap tower m (n + 1) (Nat.le_trans h (Nat.le_succ n)) =
      (tower.iota n).comp (holographicStageMap tower m n h) := by
  unfold holographicStageMap
  rw [Nat.leRecOn_trans h (Nat.le_succ n)]
  rw [Nat.leRecOn_succ']

theorem holographicStageMap_apply_trans {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (m n k : ℕ)
    (hmn : m ≤ n) (hnk : n ≤ k) (x : T m) :
    holographicStageMap tower m k (hmn.trans hnk) x =
      holographicStageMap tower n k hnk (holographicStageMap tower m n hmn x) := by
  induction k, hnk using Nat.le_induction with
  | base =>
      simp [holographicStageMap_refl]
  | succ k hk ih =>
      rw [holographicStageMap_succ tower m k (hmn.trans hk),
        holographicStageMap_succ tower n k hk]
      exact congrArg (fun y => tower.iota k y) ih

/-- The successor maps of a `HolographicTower` form a Mathlib directed system. -/
instance holographicDirectedSystem {R : Type*} [CommRing R]
    (T : ℕ → Type) [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) :
    DirectedSystem T (fun m n h => holographicStageMap tower m n h) where
  map_self := by
    intro m x
    exact congrArg (fun f : T m →ₗ[R] T m => f x)
      (holographicStageMap_refl tower m)
  map_map := by
    intro k j i hij hjk x
    simpa using (holographicStageMap_apply_trans tower i j k hij hjk x).symm

/-- The canonical Mathlib cocone on the algebraic module direct limit of this
successor tower. -/
noncomputable abbrev holographicModuleCocone {R : Type*} [CommRing R]
    (T : ℕ → Type) [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) :
    Cocone (ModuleCat.directLimitDiagram T
      (fun m n h => holographicStageMap tower m n h)) :=
  ModuleCat.directLimitCocone T (fun m n h => holographicStageMap tower m n h)

/-- The canonical module direct limit of a `HolographicTower` has the genuine
universal property of a colimit in `ModuleCat R`. This is an algebraic
filtered colimit; it asserts no topology, completion, or analytic limit. -/
noncomputable def holographicModuleCoconeIsColimit {R : Type*} [CommRing R]
    (T : ℕ → Type) [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) :
    IsColimit (holographicModuleCocone T tower) :=
  ModuleCat.directLimitIsColimit T
    (fun m n h => holographicStageMap tower m n h)

/-! ### 3. Compatible Stage Families -/

/-- A compatible family of linear maps from the stages into a chosen target.
This structure alone does not assert that the target is a colimit. -/
structure HolographicColimitCocone {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (T_inf : Type*) [AddCommGroup T_inf] [Module R T_inf] where
  psi : ∀ n, T n →ₗ[R] T_inf
  psi_comm : ∀ n, (psi (n + 1)).comp (tower.iota n) = psi n

/-- Constructive model witness: the zero cocone over `zeroHolographicTower`. -/
def zeroHolographicColimitCocone {R : Type*} [CommRing R] :
    HolographicColimitCocone (zeroHolographicTower (R := R)) R :=
  ⟨fun _ => 0, fun _ => LinearMap.zero_comp 0⟩

instance {R : Type*} [CommRing R] {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    {T_inf : Type*} [AddCommGroup T_inf] [Module R T_inf]
    (tower : HolographicTower (R := R) T) :
    Inhabited (HolographicColimitCocone tower T_inf) :=
  ⟨⟨fun _ => 0, fun n => LinearMap.zero_comp (tower.iota n)⟩⟩

/--
Theorem: Sequential cocone compatibility.
Evaluating the colimit morphism at depth `n + m` on `iotaSeq n m v` recovers `psi n v`.
-/
theorem psi_comp_iotaSeq {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    {T_inf : Type*} [AddCommGroup T_inf] [Module R T_inf]
    (tower : HolographicTower (R := R) T)
    (cocone : HolographicColimitCocone tower T_inf)
    (n m : ℕ) :
    (cocone.psi (n + m)).comp (iotaSeq tower n m) = cocone.psi n := by
  induction' m with m ih
  · rfl
  · dsimp [iotaSeq]
    rw [← LinearMap.comp_assoc]
    have hcomm : (cocone.psi (n + (m + 1))).comp (tower.iota (n + m)) = cocone.psi (n + m) := by
      simpa only [Nat.add_succ] using cocone.psi_comm (n + m)
    rw [hcomm]
    exact ih

/-- Functional evaluation invariance: Any boundary linear functional evaluates identically along the tower. -/
theorem compatible_family_evaluation_invariant {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    {T_inf : Type*} [AddCommGroup T_inf] [Module R T_inf]
    (tower : HolographicTower (R := R) T)
    (cocone : HolographicColimitCocone tower T_inf)
    (f : T_inf →ₗ[R] R) (n m : ℕ) (v : T n) :
    f (cocone.psi (n + m) (iotaSeq tower n m v)) = f (cocone.psi n v) := by
  have h_comp := psi_comp_iotaSeq tower cocone n m
  have h_eval := congr_arg (fun (g : T n →ₗ[R] T_inf) => f (g v)) h_comp
  exact h_eval

/-- Connection theorem: Colimit trace commutativity derived from canonical TensorTowerColimit. -/
theorem compatible_family_trace_invariant {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    {T_inf : Type*} [AddCommGroup T_inf] [Module R T_inf]
    (tower : HolographicTower (R := R) T)
    (cocone : HolographicColimitCocone tower T_inf)
    (f : T_inf →ₗ[R] R) (n m : ℕ) (v : T n) :
    f (cocone.psi (n + m) (iota_seq T tower.iota n m v)) = f (cocone.psi n v) := by
  rw [← iotaSeq_eq_tensorTowerColimit_iota_seq]
  exact compatible_family_evaluation_invariant tower cocone f n m v

/-! ### 4. Causal Cone Preservation & Preorder Stabilization -/

/-- Causal cone family across the discrete network stages. -/
structure CausalConeFamily (T : ℕ → Type*) where
  cone : ∀ n, T n → Prop

/-- Constructive model witness: the full-stage causal cone family. -/
def trivialCausalConeFamily : CausalConeFamily (fun _ : ℕ => PUnit) :=
  ⟨fun _ _ => True⟩

instance {T : ℕ → Type*} : Inhabited (CausalConeFamily T) :=
  ⟨⟨fun _ _ => True⟩⟩

/-- Preservation of causal cones under the bonding intertwiners. -/
def PreservesCausalCone {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (cones : CausalConeFamily T) : Prop :=
  ∀ (n : ℕ) (v : T n), cones.cone n v → cones.cone (n + 1) (tower.iota n v)

/-- Theorem: Causal cone membership is stably preserved across arbitrary depth $m$. -/
theorem causal_cone_seq_stable {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (cones : CausalConeFamily T)
    (h_pres : PreservesCausalCone tower cones)
    (n : ℕ) (m : ℕ) (v : T n) (hv : cones.cone n v) :
    cones.cone (n + m) (iotaSeq tower n m v) := by
  induction' m with m ih
  · exact hv
  · dsimp [iotaSeq]
    exact h_pres (n + m) (iotaSeq tower n m v) ih

/-! ### 5. Coherent Idempotent Projectors & Stage Invariance -/

/-- Family of idempotent projectors `P_n : T n →ₗ[R] T n` on each discrete stage. -/
structure ProjectorFamily {R : Type*} [CommRing R]
    (T : ℕ → Type*) [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)] where
  P : ∀ n, T n →ₗ[R] T n
  idempotent : ∀ n (v : T n), P n (P n v) = P n v

/-- Constructive model witness: the identity stage projector family. -/
def idProjectorFamily {R : Type*} [CommRing R] :
    ProjectorFamily (R := R) (fun _ : ℕ => R) :=
  ⟨fun _ => LinearMap.id, fun _ _ => rfl⟩

instance {R : Type*} [CommRing R] {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)] :
    Inhabited (ProjectorFamily (R := R) T) :=
  ⟨⟨fun _ => LinearMap.id, fun _ _ => rfl⟩⟩

/-- Intertwining condition: The projectors commute with the bonding maps. -/
def IntertwinesProjector {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (projs : ProjectorFamily (R := R) T) : Prop :=
  ∀ n, (tower.iota n).comp (projs.P n) = (projs.P (n + 1)).comp (tower.iota n)

/--
Theorem: Sequential intertwining.
Projectors commute with `iotaSeq` across arbitrary depth $m$.
-/
theorem projector_comm_iotaSeq {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (projs : ProjectorFamily (R := R) T)
    (h_inter : IntertwinesProjector tower projs)
    (n m : ℕ) :
    (iotaSeq tower n m).comp (projs.P n) = (projs.P (n + m)).comp (iotaSeq tower n m) := by
  induction' m with m ih
  · rfl
  · dsimp [iotaSeq]
    have h_step : (tower.iota (n + m)).comp (projs.P (n + m)) = (projs.P (n + m + 1)).comp (tower.iota (n + m)) :=
      h_inter (n + m)
    rw [LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc, h_step, LinearMap.comp_assoc]
    rfl

/-- Complementary projector $Q_n = \text{id} - P_n$ is also idempotent. -/
def complementProjector {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (projs : ProjectorFamily (R := R) T) (n : ℕ) : T n →ₗ[R] T n :=
  LinearMap.id - projs.P n

@[simp]
theorem complement_idempotent {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (projs : ProjectorFamily (R := R) T) (n : ℕ) (v : T n) :
    complementProjector projs n (complementProjector projs n v) = complementProjector projs n v := by
  dsimp [complementProjector]
  rw [map_sub, projs.idempotent, sub_self, sub_zero]

/-- Orthogonal annihilation: $P_n Q_n = 0$. -/
@[simp]
theorem projector_annihilation {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (projs : ProjectorFamily (R := R) T) (n : ℕ) (v : T n) :
    projs.P n (complementProjector projs n v) = 0 := by
  dsimp [complementProjector]
  rw [map_sub, projs.idempotent, sub_self]

/--
Theorem: Sequential intertwining of the complementary projector $Q_n = \text{id} - P_n$.
If `projs` intertwines the tower bonding maps, then `complementProjector projs` also commutes with `iotaSeq`.
-/
theorem complement_intertwines_iotaSeq {R : Type*} [CommRing R]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (projs : ProjectorFamily (R := R) T)
    (h_inter : IntertwinesProjector tower projs)
    (n m : ℕ) :
    (iotaSeq tower n m).comp (complementProjector projs n) =
      (complementProjector projs (n + m)).comp (iotaSeq tower n m) := by
  dsimp [complementProjector]
  rw [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id, LinearMap.id_comp,
    projector_comm_iotaSeq tower projs h_inter n m]

end InfoGeometry.Canonical.HolographicColimitContinuum
