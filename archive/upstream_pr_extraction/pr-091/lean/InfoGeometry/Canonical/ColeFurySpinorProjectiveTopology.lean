import Mathlib.Topology.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import InfoGeometry.Canonical.ColeFurySpinorTopology

namespace InfoGeometry.Canonical.ColeFurySpinorProjectiveTopology

open InfoGeometry.Algebra.ColeFurySpinorBridge
open InfoGeometry.Canonical.ColeFurySpinorTopology

/-- The nonzero part of the real finite Cole--Fury spinor carrier. -/
def NonzeroSpinor := {ψ : ColeFurySpinor ℝ // ψ ≠ ColeFurySpinor.zero}

instance : SMul ℝ (ColeFurySpinor ℝ) where
  smul c ψ := fun i => c * ψ i

instance : TopologicalSpace NonzeroSpinor := by
  change TopologicalSpace {ψ : ColeFurySpinor ℝ // ψ ≠ ColeFurySpinor.zero}
  infer_instance

instance : MulAction ℝˣ (NonzeroSpinor) where
  smul u ψ :=
    ⟨(u : ℝ) • ψ.1, by
      intro h
      apply ψ.2
      funext i
      have hi := congrFun h i
      change (u : ℝ) * ψ.1 i = 0 at hi
      exact (mul_eq_zero.mp hi).resolve_left (Units.ne_zero u)⟩
  one_smul ψ := by
    apply Subtype.ext
    funext i
    change (1 : ℝ) * ψ.1 i = ψ.1 i
    simp
  mul_smul u v ψ := by
    apply Subtype.ext
    funext i
    change (↑(u * v) : ℝ) * ψ.1 i = (u : ℝ) * ((v : ℝ) * ψ.1 i)
    rw [Units.val_mul]
    ring

/-- Nonzero spinors modulo nonzero real rescaling. -/
def projectiveSpinorSetoid : Setoid NonzeroSpinor :=
  MulAction.orbitRel ℝˣ NonzeroSpinor

/-- The projective spinor quotient with its quotient topology. -/
def ProjectiveSpinor := Quotient projectiveSpinorSetoid

instance : TopologicalSpace ProjectiveSpinor :=
  instTopologicalSpaceQuotient

/-- The canonical projection from nonzero spinors to projective spinors. -/
def projectiveSpinorMap : NonzeroSpinor → ProjectiveSpinor :=
  Quotient.mk projectiveSpinorSetoid

theorem continuous_projectiveSpinorMap :
    Continuous projectiveSpinorMap :=
  continuous_quotient_mk'

theorem projectiveSpinorMap_surjective :
    Function.Surjective projectiveSpinorMap := by
  intro q
  exact Quotient.inductionOn q (fun ψ => ⟨ψ, rfl⟩)

/-- A rescaling-invariant continuous readout descends to projective spinors. -/
def projectiveSpinorLift {Y : Type*} [TopologicalSpace Y]
    (f : NonzeroSpinor → Y)
    (hinv : ∀ (u : ℝˣ) (ψ : NonzeroSpinor), f (u • ψ) = f ψ) :
    ProjectiveSpinor → Y :=
  Quotient.lift f (by
    intro a b h
    rcases h with ⟨u, hu⟩
    rw [← hu, hinv u b])

@[simp]
theorem projectiveSpinorLift_map {Y : Type*} [TopologicalSpace Y]
    (f : NonzeroSpinor → Y)
    (hinv : ∀ (u : ℝˣ) (ψ : NonzeroSpinor), f (u • ψ) = f ψ)
    (ψ : NonzeroSpinor) :
    projectiveSpinorLift f hinv (projectiveSpinorMap ψ) = f ψ :=
  rfl

theorem continuous_projectiveSpinorLift {Y : Type*} [TopologicalSpace Y]
    (f : NonzeroSpinor → Y)
    (hcont : Continuous f)
    (hinv : ∀ (u : ℝˣ) (ψ : NonzeroSpinor), f (u • ψ) = f ψ) :
    Continuous (projectiveSpinorLift f hinv) := by
  exact Continuous.quotient_lift hcont _

end InfoGeometry.Canonical.ColeFurySpinorProjectiveTopology
