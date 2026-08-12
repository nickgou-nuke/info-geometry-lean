import InfoGeometry.Canonical.RefinementGaloisConnection
import InfoGeometry.Canonical.CompletionPathway
import Mathlib.Order.FixedPoints

/-!
# Self-Similar Vacuum and Knaster-Tarski

This file formalizes the self-similar Cantor vacuum using the Knaster-Tarski
fixed-point theorem.

A state is defined as an infinite sequence of sectors $(s_n)_{n \in \mathbb N}$
where $s_n \in \text{Sector } n$. The product of complete lattices is a complete lattice.

The renormalization/refinement operator $R$ acts on states by:
  $(R s)_0 = s_0$
  $(R s)_{n+1} = \text{refine}(s_n)$

$R$ is a monotone map on the complete lattice of states. By the Knaster-Tarski
theorem, the set of fixed points $\text{Fix}(R)$ forms a complete lattice.

A fixed point of $R$ satisfies $s_{n+1} = \text{refine}(s_n)$ for all $n$,
which is the exact formal definition of a self-similar fractal vacuum state.
-/

namespace InfoGeometry.Canonical.SelfSimilarVacuum

open InfoGeometry.Canonical.RefinementGaloisConnection

/-! ## 1. State Space -/

/-- The state space is the product lattice of all sector layers. -/
def StateSpace := ∀ n : ℕ, Sector n

/-- The state space is a complete lattice (product of complete lattices). -/
noncomputable instance completeLatticeStateSpace : CompleteLattice StateSpace :=
  Pi.instCompleteLattice

/-! ## 2. Renormalization Operator -/

/-- The renormalization/refinement operator. -/
def R (s : StateSpace) : StateSpace
  | 0     => s 0
  | n + 1 => refineSector (s n)

/-- The operator $R$ is monotone. -/
theorem R_monotone : Monotone R := by
  intro s t hst
  change ∀ n, R s n ≤ R t n
  intro n
  cases n with
  | zero => exact hst 0
  | succ m =>
    have h_mono : Monotone (@refineSector m) :=
      (sector_galois_connection m).monotone_l
    exact h_mono (hst m)

/-- The monotone operator $R$ as an `OrderHom`. -/
def R_hom : StateSpace →o StateSpace :=
  ⟨R, R_monotone⟩

/-! ## 3. Knaster-Tarski Vacuum Lattice -/

/-- A self-similar vacuum is a fixed point of the renormalization operator. -/
def IsSelfSimilarVacuum (s : StateSpace) : Prop :=
  R s = s

/-- The set of all self-similar vacua. -/
abbrev VacuumLattice : Type :=
  Function.fixedPoints R_hom

/-! ## 3a. Classification of the exact-refinement fixed points -/

def stateFromSeed (x : Sector 0) : StateSpace
  | 0 => x
  | n + 1 => refineSector (stateFromSeed x n)

theorem stateFromSeed_fixed (x : Sector 0) :
    R (stateFromSeed x) = stateFromSeed x := by
  funext n
  cases n <;> rfl

def vacuumSeed (v : VacuumLattice) : Sector 0 :=
  v.1 0

theorem vacuum_eq_stateFromSeed (v : VacuumLattice) :
    v.1 = stateFromSeed (vacuumSeed v) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [stateFromSeed]
      have h := congrFun v.2 (n + 1)
      change refineSector (v.1 n) = v.1 (n + 1) at h
      rw [← h, ih]

def exactVacuumOrderIso : VacuumLattice ≃o Sector 0 where
  toFun := vacuumSeed
  invFun x := ⟨stateFromSeed x, stateFromSeed_fixed x⟩
  left_inv v := by
    apply Subtype.ext
    exact (vacuum_eq_stateFromSeed v).symm
  right_inv x := rfl
  map_rel_iff' := by
    intro v w
    change vacuumSeed v ≤ vacuumSeed w ↔ v ≤ w
    constructor
    · intro h
      change v.1 ≤ w.1
      rw [vacuum_eq_stateFromSeed v, vacuum_eq_stateFromSeed w]
      intro n
      induction n with
      | zero => exact h
      | succ n ih =>
          exact (sector_galois_connection n).monotone_l ih
    · intro h
      change v.1 0 ≤ w.1 0
      exact h 0

/-- By Knaster-Tarski, the set of self-similar vacua forms a complete lattice. -/
noncomputable instance completeLatticeVacuum : CompleteLattice VacuumLattice :=
  inferInstance

/-- The least fixed point is a valid self-similar vacuum. -/
noncomputable def leastVacuum : VacuumLattice :=
  ⟨R_hom.lfp, R_hom.map_lfp⟩

/-- The greatest fixed point is a valid self-similar vacuum. -/
noncomputable def greatestVacuum : VacuumLattice :=
  ⟨R_hom.gfp, R_hom.map_gfp⟩

/-! ## 4. Pointwise projector vacuum lattice -/

/--
The stronger projector state space records a complete finite projection assignment at
every Cantor level.
-/
def ProjectionStateSpace :=
  ∀ n : ℕ,
    (Fin n → Bool) →
      InfoGeometry.Canonical.KreinProjectorLattice.KreinSector

/-- The pointwise projector state space is a complete lattice. -/
noncomputable instance completeLatticeProjectionStateSpace :
    CompleteLattice ProjectionStateSpace :=
  Pi.instCompleteLattice

/-- The pointwise projector renormalization/refinement operator. -/
def projectionR (s : ProjectionStateSpace) : ProjectionStateSpace
  | 0 => s 0
  | n + 1 => InfoGeometry.Canonical.CompletionPathway.refineProjectionAssignment (s n)

/-- The pointwise projector renormalization operator is monotone. -/
theorem projectionR_monotone : Monotone projectionR := by
  intro s t hst
  change ∀ n, projectionR s n ≤ projectionR t n
  intro n
  cases n with
  | zero => exact hst 0
  | succ m =>
    have h_mono : Monotone
        (@InfoGeometry.Canonical.CompletionPathway.refineProjectionAssignment m) :=
      (InfoGeometry.Canonical.CompletionPathway.projectionAssignment_galoisConnection m).monotone_l
    exact h_mono (hst m)

/-- The pointwise projector renormalization operator as an `OrderHom`. -/
def projectionR_hom : ProjectionStateSpace →o ProjectionStateSpace :=
  ⟨projectionR, projectionR_monotone⟩

/-- A pointwise projector vacuum is a fixed point of the projector renormalization operator. -/
def IsProjectionSelfSimilarVacuum (s : ProjectionStateSpace) : Prop :=
  projectionR s = s

/-- The complete lattice of pointwise self-similar projector vacua. -/
abbrev ProjectionVacuumLattice : Type :=
  Function.fixedPoints projectionR_hom

/--
Knaster-Tarski, imported from mathlib, supplies the complete lattice of fixed
pointwise projector vacua.
-/
noncomputable instance completeLatticeProjectionVacuum :
    CompleteLattice ProjectionVacuumLattice :=
  inferInstance

/-- The least fixed point is a valid pointwise projector vacuum. -/
noncomputable def leastProjectionVacuum : ProjectionVacuumLattice :=
  ⟨projectionR_hom.lfp, projectionR_hom.map_lfp⟩

/-- The greatest fixed point is a valid pointwise projector vacuum. -/
noncomputable def greatestProjectionVacuum : ProjectionVacuumLattice :=
  ⟨projectionR_hom.gfp, projectionR_hom.map_gfp⟩

/-- The least pointwise projector vacuum satisfies the renormalization fixed-point law. -/
theorem leastProjectionVacuum_isFixed :
    projectionR projectionR_hom.lfp = projectionR_hom.lfp :=
  projectionR_hom.map_lfp

/-- The greatest pointwise projector vacuum satisfies the renormalization fixed-point law. -/
theorem greatestProjectionVacuum_isFixed :
    projectionR projectionR_hom.gfp = projectionR_hom.gfp :=
  projectionR_hom.map_gfp

end InfoGeometry.Canonical.SelfSimilarVacuum
