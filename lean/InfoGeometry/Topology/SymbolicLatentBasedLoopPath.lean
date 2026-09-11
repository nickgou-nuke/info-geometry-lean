import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentLoop
import InfoGeometry.Topology.SymbolicLatentPathConcatenationConstruction

namespace InfoGeometry.Topology

/-!
# Based-loop paths before homotopy quotienting

This is the concrete composable loop layer.  It keeps the basepoint in the
type and deliberately stops short of asserting associativity or quotient
well-definedness.
-/

abbrev SymbolicLatentBasedLoopPath
    {X : Type*} [TopologicalSpace X] (x : X) :=
  {γ : SymbolicLatentPath X // γ.start = x ∧ γ.finish = x}

noncomputable def canonicalSymbolicLatentBasedLoopConcatenation
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ : SymbolicLatentBasedLoopPath x) :
    SymbolicLatentBasedLoopPath x :=
  let hend : (γ₀.1).finish = (γ₁.1).start :=
    γ₀.2.2.trans γ₁.2.1.symm
  ⟨canonicalSymbolicConcatenation hend, by
    constructor
    · change (canonicalSymbolicConcatenation hend).start = x
      change (canonicalSymbolicLatentPathConcatenation hend).path.start = x
      rw [(canonicalSymbolicLatentPathConcatenation hend).start_eq_first_start]
      exact γ₀.2.1
    · change (canonicalSymbolicConcatenation hend).finish = x
      change (canonicalSymbolicLatentPathConcatenation hend).path.finish = x
      rw [(canonicalSymbolicLatentPathConcatenation hend).finish_eq_second_finish]
      exact γ₁.2.2⟩

theorem canonicalSymbolicLatentBasedLoopConcatenation_start
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ : SymbolicLatentBasedLoopPath x) :
    (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1.start = x :=
  (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).2.1

theorem canonicalSymbolicLatentBasedLoopConcatenation_finish
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ : SymbolicLatentBasedLoopPath x) :
    (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1.finish = x :=
  (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).2.2

theorem canonicalSymbolicLatentBasedLoopConcatenation_endpoints
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ : SymbolicLatentBasedLoopPath x) :
    (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1.endpoints =
      (x, x) := by
  ext <;>
    simp [SymbolicLatentPath.endpoints,
      canonicalSymbolicLatentBasedLoopConcatenation_start,
      canonicalSymbolicLatentBasedLoopConcatenation_finish]

theorem constantSymbolicLatentBasedLoopPath_endpoints
    {X : Type*} [TopologicalSpace X] (x : X) :
    ((⟨constantSymbolicLatentPath x, by constructor <;> rfl⟩ :
      SymbolicLatentBasedLoopPath x)).1.endpoints = (x, x) := by
  ext <;> simp [SymbolicLatentPath.endpoints]

def reverseSymbolicLatentBasedLoopPath
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    SymbolicLatentBasedLoopPath x :=
  ⟨reverseSymbolicLatentPath γ.1, by
    constructor
    · rw [reverseSymbolicLatentPath_start]
      exact γ.2.2
    · rw [reverseSymbolicLatentPath_finish]
      exact γ.2.1⟩

theorem reverse_reverseSymbolicLatentBasedLoopPath
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    reverseSymbolicLatentBasedLoopPath
        (reverseSymbolicLatentBasedLoopPath γ) = γ := by
  apply Subtype.ext
  exact reverse_reverseSymbolicLatentPath γ.1

theorem reverseSymbolicLatentBasedLoopPath_endpoints
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    (reverseSymbolicLatentBasedLoopPath γ).1.endpoints = (x, x) := by
  exact Prod.ext (reverseSymbolicLatentBasedLoopPath γ).2.1
    (reverseSymbolicLatentBasedLoopPath γ).2.2

end InfoGeometry.Topology
