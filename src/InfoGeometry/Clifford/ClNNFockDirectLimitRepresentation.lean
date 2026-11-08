import Mathlib.Algebra.Colimit.DirectLimit
import InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Canonical.SplitCliffordSuperGradeColimit

/-!
# The algebraic Fock colimit for the symmetric split Clifford tower

The finite-stage Chevalley representations on `Λ (Fin n → ℝ)` are compatible
with both the recursive `Cl(n,n)` maps and the zero-head exterior-Fock maps.
This file forms the algebraic direct limit of the Fock stages and descends the
stagewise Clifford action to the canonical split-Clifford direct limit.

The Fock carrier here is an algebraic colimit of exterior-algebra carriers. It
is not identified with a doubled Krein space or with a Hilbert completion.
-/

noncomputable section

namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Algebra.SuperGrassmannianClifford

abbrev FockStage (n : ℕ) :=
  InfoGeometry.Clifford.SpinorSpace (Vector n)

/-- Left contraction reverses exterior parity.  This is stated directly for
Mathlib's Clifford grade involution, so it applies to the native Fock carrier
`CliffordAlgebra 0` used by the symmetric split tower. -/
theorem involute_contractLeft
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (φ : Module.Dual ℝ V)
    (x : CliffordAlgebra Q) :
    CliffordAlgebra.involute (CliffordAlgebra.contractLeft φ x) =
      -CliffordAlgebra.contractLeft φ (CliffordAlgebra.involute x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | ι_mul v x hx =>
      simp only [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul,
        map_mul, CliffordAlgebra.involute_ι, hx]
      simp only [map_neg, mul_neg, neg_mul, neg_neg]
      rw [CliffordAlgebra.contractLeft_ι_mul]

/-- The iterated zero-head inclusion between finite Fock stages. -/
def fockStageMap (m n : ℕ) (h : m ≤ n) : FockStage m →ₗ[ℝ] FockStage n :=
  Nat.leRecOn h
    (C := fun n => FockStage m →ₗ[ℝ] FockStage n)
    (fun {k} ih => (fockTailMap k).toLinearMap.comp ih)
    (LinearMap.id : FockStage m →ₗ[ℝ] FockStage m)

@[simp] theorem fockStageMap_refl (m : ℕ) :
    fockStageMap m m le_rfl = (LinearMap.id : FockStage m →ₗ[ℝ] FockStage m) := by
  simpa [fockStageMap] using
    (Nat.leRecOn_self
      (C := fun n => FockStage m →ₗ[ℝ] FockStage n)
      (next := fun {k} ih => (fockTailMap k).toLinearMap.comp ih)
      (x := (LinearMap.id : FockStage m →ₗ[ℝ] FockStage m)))

theorem fockStageMap_succ (m n : ℕ) (h : m ≤ n) :
    fockStageMap m (n + 1) (Nat.le_trans h (Nat.le_succ n)) =
      (fockTailMap n).toLinearMap.comp (fockStageMap m n h) := by
  unfold fockStageMap
  rw [Nat.leRecOn_trans h (Nat.le_succ n)]
  rw [Nat.leRecOn_succ']

/-- The native zero-head Fock transition commutes with Mathlib's Clifford
grade involution. This is the compatibility needed to define spinor parity on
the algebraic direct limit. -/
theorem fockTailMap_involute (n : ℕ) (ψ : FockStage n) :
    CliffordAlgebra.involute (fockTailMap n ψ) =
      fockTailMap n (CliffordAlgebra.involute ψ) := by
  have hhom :
      (CliffordAlgebra.involute
        (Q := (0 : QuadraticForm ℝ (Vector (n + 1))))).comp (fockTailMap n) =
      (fockTailMap n).comp
        (CliffordAlgebra.involute
          (Q := (0 : QuadraticForm ℝ (Vector n)))) := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change CliffordAlgebra.involute
        (fockTailMap n
          (CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n)) v)) =
      fockTailMap n
        (CliffordAlgebra.involute
          (CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n)) v))
    simp only [fockTailMap_generator, CliffordAlgebra.involute_ι, map_neg]
  exact congrArg (fun f => f ψ) hhom

/-- Every iterated zero-head Fock transition preserves the native spinor
grade involution. -/
theorem fockStageMap_involute (m n : ℕ) (h : m ≤ n)
    (ψ : FockStage m) :
    CliffordAlgebra.involute (fockStageMap m n h ψ) =
      fockStageMap m n h (CliffordAlgebra.involute ψ) := by
  induction n, h using Nat.le_induction with
  | base =>
      simp [fockStageMap_refl]
  | succ n hmn ih =>
      rw [fockStageMap_succ (m := m) (n := n) hmn]
      change CliffordAlgebra.involute
          (fockTailMap n (fockStageMap m n hmn ψ)) =
        fockTailMap n
          (fockStageMap m n hmn (CliffordAlgebra.involute ψ))
      rw [fockTailMap_involute, ih]

theorem fockStageMap_apply_trans (m n k : ℕ) (hmn : m ≤ n) (hnk : n ≤ k)
    (x : FockStage m) :
    fockStageMap m k (hmn.trans hnk) x =
      fockStageMap n k hnk (fockStageMap m n hmn x) := by
  induction k, hnk using Nat.le_induction with
  | base =>
      simp [fockStageMap_refl]
  | succ k hk ih =>
      rw [fockStageMap_succ (m := m) (n := k) (h := hmn.trans hk),
        fockStageMap_succ (m := n) (n := k) (h := hk)]
      exact congrArg (fun y => fockTailMap k y) ih

/-- The Fock stages and zero-head inclusions form a directed system. -/
instance fockDirectedSystem :
    DirectedSystem FockStage (fun m n h => fockStageMap m n h) where
  map_self := by
    intro m x
    exact congrArg (fun f : FockStage m →ₗ[ℝ] FockStage m => f x)
      (fockStageMap_refl m)
  map_map := by
    intro k j i hij hjk x
    simpa using (fockStageMap_apply_trans i j k hij hjk x).symm

/-- Algebraic direct limit of the finite-dimensional exterior-Fock carriers. -/
abbrev FockInfinity :=
  _root_.DirectLimit FockStage (fun m n h => fockStageMap m n h)

/-- Canonical inclusion of a finite Fock stage into its algebraic direct limit. -/
def fockToInfinity (n : ℕ) : FockStage n → FockInfinity :=
  DirectLimit.Module.of ℝ ℕ FockStage
    (fun m k h => fockStageMap m k h) n

/-- The finite-stage Clifford grade involutions induce an involution on the
algebraic Fock direct limit. Its construction uses the verified compatibility
of `fockStageMap` with grade involution. -/
noncomputable def fockInfinityInvolute : FockInfinity →ₗ[ℝ] FockInfinity :=
  DirectLimit.Module.lift ℝ ℕ FockStage
    (fun m n h => fockStageMap m n h)
    (fun n => (DirectLimit.Module.of ℝ ℕ FockStage
      (fun m k h => fockStageMap m k h) n).comp
      (CliffordAlgebra.involute
        (Q := (0 : QuadraticForm ℝ (Vector n))).toLinearMap))
    (by
      intro m n h ψ
      change fockToInfinity n
          (CliffordAlgebra.involute (fockStageMap m n h ψ)) =
        fockToInfinity m (CliffordAlgebra.involute ψ)
      rw [fockStageMap_involute]
      exact DirectLimit.Module.of_f
        (f := fun i j hij => fockStageMap i j hij)
        (i := m) (j := n) (hij := h) (x := CliffordAlgebra.involute ψ))

@[simp] theorem fockInfinityInvolute_ofStage (n : ℕ) (ψ : FockStage n) :
    fockInfinityInvolute (fockToInfinity n ψ) =
      fockToInfinity n (CliffordAlgebra.involute ψ) := by
  change DirectLimit.Module.lift ℝ ℕ FockStage
      (fun m k h => fockStageMap m k h)
      (fun k => (DirectLimit.Module.of ℝ ℕ FockStage
        (fun i j hij => fockStageMap i j hij) k).comp
        (CliffordAlgebra.involute
          (Q := (0 : QuadraticForm ℝ (Vector k))).toLinearMap)) _
      (DirectLimit.Module.of ℝ ℕ FockStage
        (fun i j hij => fockStageMap i j hij) n ψ) = _
  rw [DirectLimit.Module.lift_of]
  rfl

/-- The induced Fock-colimit parity map is involutive. -/
theorem fockInfinityInvolute_involutive (ψ : FockInfinity) :
    fockInfinityInvolute (fockInfinityInvolute ψ) = ψ := by
  have hcomp :
      fockInfinityInvolute.comp fockInfinityInvolute =
        (LinearMap.id : FockInfinity →ₗ[ℝ] FockInfinity) := by
    apply DirectLimit.Module.hom_ext
    intro n
    ext ξ
    change fockInfinityInvolute
        (fockInfinityInvolute (DirectLimit.Module.of ℝ ℕ FockStage
          (fun m k h => fockStageMap m k h) n ξ)) =
      DirectLimit.Module.of ℝ ℕ FockStage
        (fun m k h => fockStageMap m k h) n ξ
    unfold fockInfinityInvolute
    rw [DirectLimit.Module.lift_of]
    simp only [LinearMap.comp_apply]
    rw [DirectLimit.Module.lift_of]
    change DirectLimit.Module.of ℝ ℕ FockStage
        (fun m k h => fockStageMap m k h) n
        (CliffordAlgebra.involute (CliffordAlgebra.involute ξ)) =
      DirectLimit.Module.of ℝ ℕ FockStage
        (fun m k h => fockStageMap m k h) n ξ
    rw [CliffordAlgebra.involute_involutive]
  change (fockInfinityInvolute.comp fockInfinityInvolute) ψ = ψ
  rw [hcomp]
  rfl

/-- The canonical Fock-stage injection preserves additive inverses. -/
@[simp] theorem fockToInfinity_neg (n : ℕ) (ψ : FockStage n) :
    fockToInfinity n (-ψ) = -fockToInfinity n ψ := by
  change (DirectLimit.Module.of ℝ ℕ FockStage
    (fun m k h => fockStageMap m k h) n) (-ψ) =
      -(DirectLimit.Module.of ℝ ℕ FockStage
        (fun m k h => fockStageMap m k h) n) ψ
  exact map_neg _ _

/-- The categorical tensor-factor transition and the super-Grassmannian
stage inclusion are the same algebra map: both send each old Clifford
generator to its tail generator. -/
theorem splitCliffordStep_eq_splitStageCliffordMap (n : ℕ) :
    splitCliffordStep n =
      InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageCliffordMap n := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  change splitCliffordStep n (CliffordAlgebra.ι (Quad n) x) =
    InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageCliffordMap n
      (CliffordAlgebra.ι (Quad n) x)
  rw [InfoGeometry.Clifford.ClNNSuperGrassmannianBridge.splitStageCliffordMap_generator_eq_gammaTail]
  apply (splitCliffordTensorStepEquiv n).injective
  simp only [splitCliffordStep, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    AlgEquiv.apply_symm_apply, gammaTail]
  exact (splitCliffordTensorStep_tailFactor n x).symm

/-- The finite-stage Chevalley representation intertwines with every iterated
Fock and split-Clifford transition. -/
theorem towerSpinorRep_stageMap (m n : ℕ) (h : m ≤ n)
    (a : SplitClNNAlg m) (ψ : FockStage m) :
    fockStageMap m n h (towerSpinorRep m a ψ) =
      towerSpinorRep n (splitCliffordMap m n h a) (fockStageMap m n h ψ) := by
  induction n, h using Nat.le_induction with
  | base =>
      simp [fockStageMap_refl, splitCliffordMap_refl]
  | succ n hn ih =>
      rw [fockStageMap_succ m n hn, splitCliffordMap_succ m n hn]
      simp only [LinearMap.comp_apply, AlgHom.comp_apply]
      rw [splitCliffordStep_eq_splitStageCliffordMap]
      rw [ih]
      simpa using
        (towerSpinorRep_tail n (splitCliffordMap m n hn a)
          (fockStageMap m n hn ψ))

/-- The stage action induces an action of the canonical `Cl(N,N)` algebraic
direct limit on the algebraic Fock direct limit. -/
def splitCliffordFockAction : SplitCliffordInfinity → FockInfinity → FockInfinity :=
  DirectLimit.map₂
    (f₁ := fun m n h => splitCliffordMap m n h)
    (f₂ := fun m n h => fockStageMap m n h)
    (f := fun m n h => fockStageMap m n h)
    (fun n a ψ => towerSpinorRep n a ψ)
    (by
      intro m n h a ψ
      exact towerSpinorRep_stageMap m n h a ψ)

/-- On finite-stage representatives the descended action is exactly the
existing finite-stage Chevalley representation. -/
@[simp] theorem splitCliffordFockAction_of (n : ℕ)
    (a : SplitClNNAlg n) (ψ : FockStage n) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n a)
        (fockToInfinity n ψ) =
      fockToInfinity n (towerSpinorRep n a ψ) := by
  change DirectLimit.map₂
      (f₁ := fun m k h => splitCliffordMap m k h)
      (f₂ := fun m k h => fockStageMap m k h)
      (f := fun m k h => fockStageMap m k h)
      (fun k x y => towerSpinorRep k x y)
      (by intro i j hij x y; exact towerSpinorRep_stageMap i j hij x y)
      (⟦⟨n, a⟩⟧ : SplitCliffordInfinity)
      (⟦⟨n, ψ⟩⟧ : FockInfinity) =
    (⟦⟨n, towerSpinorRep n a ψ⟩⟧ : FockInfinity)
  rw [DirectLimit.map₂_def]

/-- On a finite-stage Clifford generator, the colimit action is the native
Chevalley creation/contraction action on the corresponding Fock representative. -/
@[simp] theorem splitCliffordFockAction_generator_of (n : ℕ)
    (x : TowerSpace n) (ψ : FockStage n) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n
          (CliffordAlgebra.ι (TowerForm n) x))
        (fockToInfinity n ψ) =
      fockToInfinity n
        (InfoGeometry.Clifford.spinorAction ((neutralToSplit n).symm x) ψ) := by
  rw [splitCliffordFockAction_of, towerSpinorRep_generator]

/-- The square of a finite-stage split vector acts on the Fock colimit by
its symmetric split quadratic value. The scalar is transported through the
existing neutral-to-split isometry; the Fock carrier remains the algebraic
exterior-spinor colimit. -/
theorem splitCliffordFockAction_generator_sq (n : ℕ)
    (x : TowerSpace n) (ψ : FockStage n) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n
          (CliffordAlgebra.ι (TowerForm n) x))
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n
            (CliffordAlgebra.ι (TowerForm n) x))
          (fockToInfinity n ψ)) =
      fockToInfinity n ((TowerForm n x) • ψ) := by
  rw [splitCliffordFockAction_generator_of,
    splitCliffordFockAction_generator_of,
    InfoGeometry.Clifford.spinorAction_sq]
  apply congrArg (fockToInfinity n)
  rw [← Algebra.smul_def]
  congr 1
  have hform := Qsplit_neutralToSplit_chevalley n
    ((neutralToSplit n).symm x)
  simpa using hform.symm

/-- Every neutral Chevalley vector acts oddly on the native exterior-spinor
carrier: applying Mathlib's spinor grade involution before or after the
creation-plus-contraction action changes the sign. -/
theorem spinorAction_anticommutes_with_involute (n : ℕ)
    (x : InfoGeometry.Clifford.SplitSpace (Vector n))
    (ψ : FockStage n) :
    CliffordAlgebra.involute
        (InfoGeometry.Clifford.spinorAction x ψ) =
      -InfoGeometry.Clifford.spinorAction x
        (CliffordAlgebra.involute ψ) := by
  rcases x with ⟨u, φ⟩
  change CliffordAlgebra.involute
      (CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n)) u * ψ +
        CliffordAlgebra.contractLeft φ ψ) =
    -(CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n)) u *
        CliffordAlgebra.involute ψ +
      CliffordAlgebra.contractLeft φ (CliffordAlgebra.involute ψ))
  rw [map_add, map_mul, CliffordAlgebra.involute_ι,
    involute_contractLeft]
  rw [neg_mul, neg_add]

/-- The recursive `Cl(n,n)` vector generator acts oddly on its Chevalley Fock
module.  This is the action-level compatibility between Mathlib's native
`evenOdd` super-grade-one generator and the exterior-spinor parity involution. -/
theorem towerSpinorRep_generator_anticommutes_with_involute (n : ℕ)
    (x : TowerSpace n) (ψ : FockStage n) :
    CliffordAlgebra.involute
        (towerSpinorRep n (CliffordAlgebra.ι (TowerForm n) x) ψ) =
      -towerSpinorRep n (CliffordAlgebra.ι (TowerForm n) x)
        (CliffordAlgebra.involute ψ) := by
  rw [towerSpinorRep_generator]
  exact spinorAction_anticommutes_with_involute n ((neutralToSplit n).symm x) ψ

/-- The finite-stage Chevalley action is equivariant for the Clifford grade
involution on the algebra and the exterior parity involution on spinors.
The statement is for every Clifford element, obtained from the generator
identity by Mathlib's Clifford algebra induction principle. -/
theorem towerSpinorRep_grade_equivariant (n : ℕ)
    (a : SplitClNNAlg n) (ψ : FockStage n) :
    CliffordAlgebra.involute (towerSpinorRep n a ψ) =
      towerSpinorRep n (CliffordAlgebra.involute a)
        (CliffordAlgebra.involute ψ) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [towerSpinorRep, InfoGeometry.Clifford.abstractSpinorRep]
  | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply, ha, hb]
  | ι_mul a v ha =>
      have hmul : towerSpinorRep n
          (CliffordAlgebra.ι (TowerForm n) v * a) =
          towerSpinorRep n (CliffordAlgebra.ι (TowerForm n) v) *
            towerSpinorRep n a := map_mul _ _ _
      rw [hmul]
      change CliffordAlgebra.involute
          (towerSpinorRep n (CliffordAlgebra.ι (TowerForm n) v)
            (towerSpinorRep n a ψ)) =
        towerSpinorRep n
          (CliffordAlgebra.involute
            (CliffordAlgebra.ι (TowerForm n) v * a))
          (CliffordAlgebra.involute ψ)
      rw [towerSpinorRep_generator_anticommutes_with_involute n v
        (towerSpinorRep n a ψ), ha]
      simp only [map_mul, Module.End.mul_apply,
        CliffordAlgebra.involute_ι, map_neg]
      rfl

/-- The native Clifford grade involution acts by a sign on the Fock-colimit
action of every split vector generator. This connects the even/odd grading
used by the SuperGrassmannian Clifford tower to its Chevalley action. -/
theorem splitCliffordFockAction_involute_generator_of (n : ℕ)
    (x : TowerSpace n) (ψ : FockStage n) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n
          (CliffordAlgebra.involute
            (CliffordAlgebra.ι (TowerForm n) x)))
        (fockToInfinity n ψ) =
      -splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n
          (CliffordAlgebra.ι (TowerForm n) x))
        (fockToInfinity n ψ) := by
  rw [splitCliffordFockAction_of, splitCliffordFockAction_of,
    CliffordAlgebra.involute_ι, map_neg]
  exact fockToInfinity_neg n _

/-- The induced Fock-colimit parity anticommutes with the action of each
finite-stage split vector generator. -/
theorem fockInfinityInvolute_action_generator_anticommutes (n : ℕ)
    (x : TowerSpace n) (ψ : FockStage n) :
    fockInfinityInvolute
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n
            (CliffordAlgebra.ι (TowerForm n) x))
          (fockToInfinity n ψ)) =
      -splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n
          (CliffordAlgebra.ι (TowerForm n) x))
        (fockInfinityInvolute (fockToInfinity n ψ)) := by
  rw [splitCliffordFockAction_generator_of, fockInfinityInvolute_ofStage,
    spinorAction_anticommutes_with_involute, fockToInfinity_neg,
    fockInfinityInvolute_ofStage, splitCliffordFockAction_generator_of]

/-- The stagewise Clifford grade involution is represented by the Fock-colimit
parity involution: the Chevalley representation is an equivariant map of
`ℤ₂`-graded carriers on every split vector generator. -/
theorem splitCliffordFockAction_grade_equivariant_generator (n : ℕ)
    (x : TowerSpace n) (ψ : FockStage n) :
    fockInfinityInvolute
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n
            (CliffordAlgebra.ι (TowerForm n) x))
          (fockToInfinity n ψ)) =
      splitCliffordFockAction
        (splitCliffordInfinityInvolute
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n
            (CliffordAlgebra.ι (TowerForm n) x)))
        (fockInfinityInvolute (fockToInfinity n ψ)) := by
  calc
    fockInfinityInvolute
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n
            (CliffordAlgebra.ι (TowerForm n) x))
          (fockToInfinity n ψ)) =
      -splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n
          (CliffordAlgebra.ι (TowerForm n) x))
        (fockInfinityInvolute (fockToInfinity n ψ)) :=
          fockInfinityInvolute_action_generator_anticommutes n x ψ
    _ = splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n
          (-CliffordAlgebra.ι (TowerForm n) x))
        (fockInfinityInvolute (fockToInfinity n ψ)) := by
          rw [fockInfinityInvolute_ofStage, splitCliffordFockAction_of]
          rw [← map_neg, splitCliffordFockAction_of]
          simp only [map_neg, LinearMap.neg_apply, fockToInfinity_neg]
    _ = splitCliffordFockAction
        (splitCliffordInfinityInvolute
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n
            (CliffordAlgebra.ι (TowerForm n) x)))
        (fockInfinityInvolute (fockToInfinity n ψ)) := by
          rw [splitCliffordInfinityInvolute_ofStage,
            CliffordAlgebra.involute_ι]

/-- The grade/action intertwining holds on every pair of finite-stage
representatives after both the split Clifford algebra and Fock carrier have
been mapped into their canonical algebraic direct limits. -/
theorem splitCliffordFockAction_grade_equivariant_of (n : ℕ)
    (a : SplitClNNAlg n) (ψ : FockStage n) :
    fockInfinityInvolute
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n a)
          (fockToInfinity n ψ)) =
      splitCliffordFockAction
        (splitCliffordInfinityInvolute
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n a))
        (fockInfinityInvolute (fockToInfinity n ψ)) := by
  calc
    fockInfinityInvolute
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n a)
          (fockToInfinity n ψ)) =
      fockToInfinity n (CliffordAlgebra.involute
        (towerSpinorRep n a ψ)) := by
          rw [splitCliffordFockAction_of, fockInfinityInvolute_ofStage]
    _ = fockToInfinity n
        (towerSpinorRep n (CliffordAlgebra.involute a)
          (CliffordAlgebra.involute ψ)) :=
          congrArg (fockToInfinity n) (towerSpinorRep_grade_equivariant n a ψ)
    _ = splitCliffordFockAction
        (splitCliffordInfinityInvolute
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n a))
        (fockInfinityInvolute (fockToInfinity n ψ)) := by
          rw [splitCliffordInfinityInvolute_ofStage,
            fockInfinityInvolute_ofStage, splitCliffordFockAction_of]

/-- The grade/action intertwining holds for arbitrary elements of the two
algebraic direct limits. A representative for each input is moved to a common
finite stage using the directed-system maps, where finite-stage equivariance
applies. -/
theorem splitCliffordFockAction_grade_equivariant
    (aInf : SplitCliffordInfinity) (ψInf : FockInfinity) :
    fockInfinityInvolute (splitCliffordFockAction aInf ψInf) =
      splitCliffordFockAction
        (splitCliffordInfinityInvolute aInf) (fockInfinityInvolute ψInf) := by
  obtain ⟨n, a, ha⟩ := splitCliffordInfinity_exists_of aInf
  obtain ⟨m, ψ, hψ⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) ψInf
  have hψ' : fockToInfinity m ψ = ψInf := by
    simpa [fockToInfinity] using hψ.symm
  let k := max n m
  have hnk : n ≤ k := le_max_left n m
  have hmk : m ≤ k := le_max_right n m
  let aK := splitCliffordMap n k hnk a
  let ψK := fockStageMap m k hmk ψ
  have ha' : DirectLimit.Algebra.of SplitClNNAlg
      (fun i j h => splitCliffordMap i j h) k aK = aInf := by
    calc
      DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k aK =
        DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) n a := by
            exact DirectLimit.Algebra.of_f
              (f := fun i j h => splitCliffordMap i j h) hnk a
      _ = aInf := ha
  have hψK : fockToInfinity k ψK = ψInf := by
    calc
      fockToInfinity k ψK = fockToInfinity m ψ := by
        exact DirectLimit.Module.of_f
          (f := fun i j h => fockStageMap i j h)
          (i := m) (j := k) (hij := hmk) (x := ψ)
      _ = ψInf := hψ'
  rw [← ha', ← hψK]
  simpa only [splitCliffordFockAction_of, fockInfinityInvolute_ofStage,
    splitCliffordInfinityInvolute_ofStage] using
      congrArg (fockToInfinity k) (towerSpinorRep_grade_equivariant k aK ψK)

/-- A finite-stage element in the SuperGrassmannian even super-grade acts
commutatively with the induced Fock parity on every Fock-colimit vector. -/
theorem splitCliffordFockAction_superGrade_zero_commutes
    (n : ℕ) (x : SplitExteriorStage n)
    (hx : x ∈ superGrade (InfoGeometry.CliffordTower.Qsplit n) (0 : ZMod 2))
    (ψ : FockInfinity) :
    fockInfinityInvolute
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun i j h => splitCliffordMap i j h) n
            ((cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit n)).symm x)) ψ) =
      splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) n
          ((cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit n)).symm x))
        (fockInfinityInvolute ψ) := by
  have hfixed := directLimit_of_superGrade_zero_fixed n x hx
  rw [splitCliffordFockAction_grade_equivariant, hfixed]

/-- The Chevalley vacuum-sheet vector acts as an odd operator on the algebraic
Fock colimit: its grade-involuted Clifford class is the negative class, and
the Fock parity intertwiner represents that grade involution on the action. -/
theorem neutralVacuumSheet_fockAction_grade_odd
    (n : ℕ) (φ : Module.Dual ℝ (Vector n)) (ψ : FockInfinity) :
    fockInfinityInvolute
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun i j h => splitCliffordMap i j h) n
            (CliffordAlgebra.ι (TowerForm n)
              (neutralVacuumSheetMap n φ))) ψ) =
      splitCliffordFockAction
        (-DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) n
          (CliffordAlgebra.ι (TowerForm n)
            (neutralVacuumSheetMap n φ)))
        (fockInfinityInvolute ψ) := by
  rw [splitCliffordFockAction_grade_equivariant,
    neutralVacuumSheet_colimit_odd]

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
