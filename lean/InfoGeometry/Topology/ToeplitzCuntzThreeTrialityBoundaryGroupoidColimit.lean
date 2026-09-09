import Mathlib.Topology.Category.TopCat.Limits.Basic
import InfoGeometry.Canonical.PauliJungTrialityD4Synthesis
import InfoGeometry.Topology.PauliJungTrialityD4Topological
import InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

/-!
# Ternary Toeplitz--Cuntz triality boundary

This owner records the theorem-safe topological shadow of the ternary sector
symmetry.  The boundary is the inverse-limit sequence space supplied by
`NaryTreeBoundaryInverseLimit`; finite cylinder observables are represented by
their stage functions.  The algebraic direct-limit carrier and any
`G_{2(2)}` identification remain separate proof obligations.
-/

noncomputable section

namespace InfoGeometry.Topology.ToeplitzCuntzThreeTriality

open InfoGeometry.Canonical
open NaryTreeBoundaryInverseLimit

abbrev TernaryBoundary : Type := Boundary (A := ColorChannel)

abbrev TernaryWord (n : ℕ) : Type := Word (A := ColorChannel) n

def prefixBoundary : ColorChannel → TernaryBoundary → TernaryBoundary :=
  boundaryCons

def boundaryPermutation (σ : Equiv.Perm ColorChannel) :
    TernaryBoundary → TernaryBoundary :=
  fun x n => σ (x n)

def boundaryPermutationHomeomorph (σ : Equiv.Perm ColorChannel) :
    TernaryBoundary ≃ₜ TernaryBoundary where
  toFun := boundaryPermutation σ
  invFun := boundaryPermutation σ.symm
  left_inv := by
    intro x
    funext n
    simp [boundaryPermutation]
  right_inv := by
    intro x
    funext n
    simp [boundaryPermutation]
  continuous_toFun := by
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology : Continuous σ).comp
      (continuous_apply n)
  continuous_invFun := by
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology : Continuous σ.symm).comp
      (continuous_apply n)

@[simp] theorem boundaryPermutation_apply
    (σ : Equiv.Perm ColorChannel) (x : TernaryBoundary) (n : ℕ) :
    boundaryPermutation σ x n = σ (x n) := rfl

@[simp] theorem boundaryPermutation_prefix
    (σ : Equiv.Perm ColorChannel)
    (c : ColorChannel)
    (x : TernaryBoundary) :
    boundaryPermutation σ (prefixBoundary c x) =
      prefixBoundary (σ c) (boundaryPermutation σ x) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

def stagePermutation (σ : Equiv.Perm ColorChannel) (w : TernaryWord n) :
    TernaryWord n :=
  fun i => σ (w i)

def stageTrialityAction (σ : Equiv.Perm ColorChannel)
    (f : TernaryWord n → A) : TernaryWord n → A :=
  fun w => f (stagePermutation σ w)

def stageTransition (f : TernaryWord n → A) : TernaryWord (n + 1) → A :=
  fun w => f (fun i => w i.castSucc)

@[simp] theorem stageTransition_triality
    (σ : Equiv.Perm ColorChannel) (f : TernaryWord n → A) :
    stageTransition (stageTrialityAction σ f) =
      stageTrialityAction σ (stageTransition f) := by
  funext w
  rfl

def cylinderObservable (f : TernaryWord n → A) : TernaryBoundary → A :=
  fun x => f (fun i => x i)

@[simp] theorem cylinderObservable_transition
    (f : TernaryWord n → A) (x : TernaryBoundary) :
    cylinderObservable (stageTransition f) x = cylinderObservable f x := by
  rfl

@[simp] theorem cylinderObservable_triality
    (σ : Equiv.Perm ColorChannel) (f : TernaryWord n → A)
    (x : TernaryBoundary) :
    cylinderObservable (stageTrialityAction σ f)
        (boundaryPermutation σ.symm x) = cylinderObservable f x := by
  apply congrArg f
  funext i
  simp [stagePermutation, boundaryPermutation]

/-- An arrow of the action groupoid `S₃ ⋉ Σ₃`. -/
abbrev TrialityArrow : Type := Equiv.Perm ColorChannel × TernaryBoundary

def arrowSource : TrialityArrow → TernaryBoundary := Prod.snd

def arrowTarget : TrialityArrow → TernaryBoundary :=
  fun a => boundaryPermutation a.1 a.2

def arrowInverse : TrialityArrow → TrialityArrow :=
  fun a => (a.1.symm, arrowTarget a)

def arrowCompose (a b : TrialityArrow) : TrialityArrow :=
  (a.1 * b.1, b.2)

def arrowIdentity (x : TernaryBoundary) : TrialityArrow := (1, x)

@[simp] theorem arrowIdentity_source (x : TernaryBoundary) :
    arrowSource (arrowIdentity x) = x := rfl

@[simp] theorem arrowIdentity_target (x : TernaryBoundary) :
    arrowTarget (arrowIdentity x) = x := by
  funext n
  simp [arrowIdentity, arrowTarget, boundaryPermutation]

theorem arrowCompose_source_target (a b : TrialityArrow)
    (h : arrowTarget b = arrowSource a) :
    arrowSource (arrowCompose a b) = arrowSource b ∧
      arrowTarget (arrowCompose a b) = arrowTarget a := by
  constructor
  · rfl
  · change boundaryPermutation (a.1 * b.1) b.2 =
      boundaryPermutation a.1 a.2
    change boundaryPermutation b.1 b.2 = a.2 at h
    rw [← h]
    funext n
    simp [boundaryPermutation]

theorem arrowInverse_source (a : TrialityArrow) :
    arrowSource (arrowInverse a) = arrowTarget a := rfl

theorem arrowInverse_target (a : TrialityArrow) :
    arrowTarget (arrowInverse a) = arrowSource a := by
  funext n
  simp [arrowInverse, arrowTarget, arrowSource, boundaryPermutation]

theorem arrowCompose_assoc (a b c : TrialityArrow) :
    arrowCompose (arrowCompose a b) c =
      arrowCompose a (arrowCompose b c) := by
  simp [arrowCompose, mul_assoc]

theorem arrowCompose_left_identity (a : TrialityArrow) :
    arrowCompose (arrowIdentity (arrowTarget a)) a = a := by
  simp [arrowCompose, arrowIdentity]

theorem arrowCompose_right_identity (a : TrialityArrow) :
    arrowCompose a (arrowIdentity (arrowSource a)) = a := by
  change (a.1, a.2) = a
  rfl

theorem arrowCompose_inverse_left (a : TrialityArrow) :
    arrowCompose (arrowInverse a) a = arrowIdentity (arrowSource a) := by
  change (a.1.symm * a.1, a.2) = (1, a.2)
  simp

theorem arrowCompose_inverse_right (a : TrialityArrow) :
    arrowCompose a (arrowInverse a) = arrowIdentity (arrowTarget a) := by
  simp [arrowCompose, arrowInverse, arrowIdentity, arrowTarget]


end InfoGeometry.Topology.ToeplitzCuntzThreeTriality
