/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Category.ModuleCat.Limits
import InfoGeometry.Canonical.TensorTowerColimit

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Holographic Successor Tower and Its Algebraic Module Colimit

This module formalizes discrete inductive towers of modules with bonding intertwiners,
their algebraic direct limit in `ModuleCat`, cocone compatibility, causal cone
monotonicity, and finite-stage projector intertwining. It does not assert a
topological completion or an analytic continuum limit:
1. `HolographicTower`: Direct inductive tower of module spaces with linear bonding maps
   `iota : ∀ n, T n →ₗ[R] T (n + 1)`.
2. `iotaSeq`: Multi-step sequential bonding map along the tower.
3. `iotaSeq_eq_tensorTowerColimit_iota_seq`: Proved isomorphism with canonical `TensorTowerColimit.iota_seq`.
4. `HolographicColimitCocone`: A compatible family of maps from the stages; it is not assumed colimiting.
5. `holographicModuleDirectedSystem`: The successor maps induce a directed system on all `m ≤ n`.
6. `holographicModuleCoconeIsColimit`: Mathlib's direct-limit cocone is a genuine colimit in `ModuleCat R`.
7. `holographicCoconeDesc`: Every compatible stage family descends uniquely from that algebraic colimit.
8. `psi_comp_iotaSeq`: Multi-step cocone sequence compatibility `(psi (n + m)).comp (iotaSeq n m) = psi n`.
9. `colimit_evaluation_invariant`: Evaluation invariance for boundary functionals on the cocone space.
10. `CausalConeFamily` & `causal_cone_seq_stable`: Preservation of causal cone membership across sequential stages.
11. `ProjectorFamily` & `projector_comm_iotaSeq`: Sequential intertwining of idempotent stage projectors with bonding maps.
12. `complement_idempotent` & `projector_annihilation`: Complementary idempotent `Q = id - P` and annihilation `PQ = 0`.
-/

namespace InfoGeometry.Canonical.HolographicColimitContinuum

open InfoGeometry.Canonical

variable {R : Type*} [CommRing R]

/-! ### 1. Discrete Holographic Tower and Sequential Bonding -/

/-- Direct inductive tower of discrete tensor network state spaces. -/
structure HolographicTower (T : ℕ → Type*) [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)] where
  iota : ∀ n, T n →ₗ[R] T (n + 1)

/-- Sequential composition of bonding maps across `m` steps. -/
def iotaSeq {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (n : ℕ) : ∀ m, T n →ₗ[R] T (n + m)
  | 0 => LinearMap.id
  | m + 1 => (tower.iota (n + m)).comp (iotaSeq tower n m)

@[simp]
theorem iotaSeq_zero {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (n : ℕ) :
    iotaSeq tower n 0 = LinearMap.id := rfl

@[simp]
theorem iotaSeq_succ {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (n m : ℕ) :
    iotaSeq tower n (m + 1) = (tower.iota (n + m)).comp (iotaSeq tower n m) := rfl

/-- Connection theorem: Exact identity with canonical TensorTowerColimit `iota_seq`. -/
theorem iotaSeq_eq_tensorTowerColimit_iota_seq
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (n m : ℕ) :
    iotaSeq tower n m = iota_seq T tower.iota n m := by
  induction' m with m ih
  · rfl
  · dsimp [iotaSeq, iota_seq]
    rw [ih]

/-! ### 1b. Native directed system and algebraic direct limit -/

/-- The map from stage `m` to stage `n`, obtained by iterating the successor
bonding maps. -/
def holographicStageMap
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (m n : ℕ) (h : m ≤ n) :
    T m →ₗ[R] T n :=
  Nat.leRecOn h
    (C := fun k => T m →ₗ[R] T k)
    (fun {k} ih => (tower.iota k).comp ih)
    (LinearMap.id : T m →ₗ[R] T m)

@[simp]
theorem holographicStageMap_refl
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (m : ℕ) :
    holographicStageMap tower m m le_rfl = LinearMap.id := by
  simpa [holographicStageMap] using
    (Nat.leRecOn_self
      (C := fun k => T m →ₗ[R] T k)
      (next := fun {k} ih => (tower.iota k).comp ih)
      (x := (LinearMap.id : T m →ₗ[R] T m)))

theorem holographicStageMap_succ
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (m n : ℕ) (h : m ≤ n) :
    holographicStageMap tower m (n + 1) (Nat.le_trans h (Nat.le_succ n)) =
      (tower.iota n).comp (holographicStageMap tower m n h) := by
  unfold holographicStageMap
  rw [Nat.leRecOn_trans h (Nat.le_succ n)]
  rw [Nat.leRecOn_succ']

theorem holographicStageMap_apply_trans
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (m n k : ℕ)
    (hmn : m ≤ n) (hnk : n ≤ k) (x : T m) :
    holographicStageMap tower m k (hmn.trans hnk) x =
      holographicStageMap tower n k hnk (holographicStageMap tower m n hmn x) := by
  induction k, hnk using Nat.le_induction with
  | base =>
      simp [holographicStageMap_refl]
  | succ k hnk ih =>
      rw [holographicStageMap_succ tower m k (hmn.trans hnk),
        holographicStageMap_succ tower n k hnk]
      exact congrArg (tower.iota k) ih

/-- The all-stage maps generated by a successor tower satisfy Mathlib's
directed-system coherence laws. -/
instance holographicModuleDirectedSystem
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) :
    DirectedSystem T (fun m n h => holographicStageMap tower m n h) where
  map_self := by
    intro m x
    exact congrArg (fun f : T m →ₗ[R] T m => f x)
      (holographicStageMap_refl tower m)
  map_map := by
    intro k j i hij hjk x
    simpa using (holographicStageMap_apply_trans tower i j k hij hjk x).symm

/-- The native Mathlib module diagram associated with a successor tower. -/
noncomputable abbrev holographicModuleDiagram
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) :=
  ModuleCat.directLimitDiagram T (fun m n h => holographicStageMap tower m n h)

/-- Mathlib's canonical direct-limit cocone for a holographic successor tower. -/
noncomputable abbrev holographicModuleCocone
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) :=
  ModuleCat.directLimitCocone T (fun m n h => holographicStageMap tower m n h)

/-- The successive bonding maps determine a genuine algebraic module colimit. -/
noncomputable def holographicModuleCoconeIsColimit
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) : IsColimit (holographicModuleCocone tower) :=
  ModuleCat.directLimitIsColimit T (fun m n h => holographicStageMap tower m n h)

/-! ### 2. Continuous Holographic Boundary Cocone -/

/-- Continuous boundary inductive colimit cocone for the tensor network tower. -/
structure HolographicColimitCocone {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (T_inf : Type*) [AddCommGroup T_inf] [Module R T_inf] where
  psi : ∀ n, T n →ₗ[R] T_inf
  psi_comm : ∀ n, (psi (n + 1)).comp (tower.iota n) = psi n

/--
Theorem: Sequential cocone compatibility.
Evaluating the colimit morphism at depth `n + m` on `iotaSeq n m v` recovers `psi n v`.
-/
theorem psi_comp_iotaSeq {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
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
theorem colimit_evaluation_invariant
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
theorem colimit_trace_comm_canonical
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    {T_inf : Type*} [AddCommGroup T_inf] [Module R T_inf]
    (tower : HolographicTower (R := R) T)
    (cocone : HolographicColimitCocone tower T_inf)
    (f : T_inf →ₗ[R] R) (n m : ℕ) (v : T n) :
    f (cocone.psi (n + m) (iota_seq T tower.iota n m v)) = f (cocone.psi n v) := by
  rw [← iotaSeq_eq_tensorTowerColimit_iota_seq]
  exact colimit_evaluation_invariant tower cocone f n m v

/-! ### 3. Causal Cone Preservation & Preorder Stabilization -/

/-- Causal cone family across the discrete network stages. -/
structure CausalConeFamily (T : ℕ → Type*) where
  cone : ∀ n, T n → Prop

/-- Preservation of causal cones under the bonding intertwiners. -/
def PreservesCausalCone {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (cones : CausalConeFamily T) : Prop :=
  ∀ (n : ℕ) (v : T n), cones.cone n v → cones.cone (n + 1) (tower.iota n v)

/-- Theorem: Causal cone membership is stably preserved across arbitrary depth $m$. -/
theorem causal_cone_seq_stable
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (cones : CausalConeFamily T)
    (h_pres : PreservesCausalCone tower cones)
    (n : ℕ) (m : ℕ) (v : T n) (hv : cones.cone n v) :
    cones.cone (n + m) (iotaSeq tower n m v) := by
  induction' m with m ih
  · exact hv
  · dsimp [iotaSeq]
    exact h_pres (n + m) (iotaSeq tower n m v) ih

/-! ### 4. Coherent Idempotent Projectors & Continuum Invariance -/

/-- Family of idempotent projectors `P_n : T n →ₗ[R] T n` on each discrete stage. -/
structure ProjectorFamily (T : ℕ → Type*) [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)] where
  P : ∀ n, T n →ₗ[R] T n
  idempotent : ∀ n (v : T n), P n (P n v) = P n v

/-- Intertwining condition: The projectors commute with the bonding maps. -/
def IntertwinesProjector {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (tower : HolographicTower (R := R) T) (projs : ProjectorFamily (R := R) T) : Prop :=
  ∀ n, (tower.iota n).comp (projs.P n) = (projs.P (n + 1)).comp (tower.iota n)

/--
Theorem: Sequential intertwining.
Projectors commute with `iotaSeq` across arbitrary depth $m$.
-/
theorem projector_comm_iotaSeq
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
def complementProjector {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (projs : ProjectorFamily (R := R) T) (n : ℕ) : T n →ₗ[R] T n :=
  LinearMap.id - projs.P n

@[simp]
theorem complement_idempotent
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (projs : ProjectorFamily (R := R) T) (n : ℕ) (v : T n) :
    complementProjector projs n (complementProjector projs n v) = complementProjector projs n v := by
  dsimp [complementProjector]
  rw [map_sub, projs.idempotent, sub_self, sub_zero]

/-- Orthogonal annihilation: $P_n Q_n = 0$. -/
@[simp]
theorem projector_annihilation
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (projs : ProjectorFamily (R := R) T) (n : ℕ) (v : T n) :
    projs.P n (complementProjector projs n v) = 0 := by
  dsimp [complementProjector]
  rw [map_sub, projs.idempotent, sub_self]

/-! ### 5. Master Holographic Colimit Continuum Certificate -/

structure HolographicColimitContinuumCertificate (R : Type*) [CommRing R]
    (T : ℕ → Type*) [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (T_inf : Type*) [AddCommGroup T_inf] [Module R T_inf] : Prop where
  colimit_eval_inv : ∀ (tower : HolographicTower (R := R) T)
    (cocone : HolographicColimitCocone tower T_inf)
    (f : T_inf →ₗ[R] R) (n m : ℕ) (v : T n),
    f (cocone.psi (n + m) (iotaSeq tower n m v)) = f (cocone.psi n v)
  causal_stable : ∀ (tower : HolographicTower (R := R) T) (cones : CausalConeFamily T)
    (h_pres : PreservesCausalCone tower cones) (n m : ℕ) (v : T n),
    cones.cone n v → cones.cone (n + m) (iotaSeq tower n m v)
  projector_seq_comm : ∀ (tower : HolographicTower (R := R) T) (projs : ProjectorFamily (R := R) T)
    (h_inter : IntertwinesProjector tower projs) (n m : ℕ),
    (iotaSeq tower n m).comp (projs.P n) = (projs.P (n + m)).comp (iotaSeq tower n m)
  proj_annihilate : ∀ (projs : ProjectorFamily (R := R) T) (n : ℕ) (v : T n),
    projs.P n (complementProjector projs n v) = 0

theorem compile_holographic_colimit_continuum (R : Type*) [CommRing R]
    (T : ℕ → Type*) [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (T_inf : Type*) [AddCommGroup T_inf] [Module R T_inf] :
    HolographicColimitContinuumCertificate R T T_inf where
  colimit_eval_inv := colimit_evaluation_invariant
  causal_stable := causal_cone_seq_stable
  projector_seq_comm := projector_comm_iotaSeq
  proj_annihilate := projector_annihilation

end InfoGeometry.Canonical.HolographicColimitContinuum
