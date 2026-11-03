/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.GrandUnification.CanonicalSpectralGap
open LinearMap
open Module

/-!
# Canonical Mathematical Extraction: Spectral Gaps and Kernels
-/

section ArchetypePoset

inductive MathArchetype
  | endomorphism
  | kernelSubspace
  | trivialKernel
  | spectralGap
  | automorphism
  deriving DecidableEq, Repr

def rank : MathArchetype → Nat
  | .endomorphism => 1
  | .kernelSubspace => 2
  | .trivialKernel => 3
  | .spectralGap => 4
  | .automorphism => 5

def causallyPrecedes (a b : MathArchetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : MathArchetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : MathArchetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := Nat.le_trans

theorem causal_antisymm {a b : MathArchetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢

end ArchetypePoset

section SpectralTheory

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
variable [FiniteDimensional R M]

/-- The "Defect Block" mathematically maps to the Kernel of the Endomorphism. -/
def kernelSubspace (K : Module.End R M) : Subspace R M := LinearMap.ker K

/-- The algebraic dimension of the kernel subspace. -/
noncomputable def kernelDimension (K : Module.End R M) : ℕ := Module.finrank R (LinearMap.ker K)

/-- 
The condition of "Confinement" mathematically translates to the 
triviality of the kernel (i.e., its dimension is zero).
-/
def TrivialKernelProp (K : Module.End R M) : Prop := kernelDimension K = 0

/-- 
If the kernel dimension is 0, the linear map is injective.
-/
theorem injective_of_trivial_kernel (K : Module.End R M) (h : TrivialKernelProp K) : 
    Function.Injective K := by
  dsimp [TrivialKernelProp, kernelDimension] at h
  rw [Submodule.finrank_eq_zero] at h
  exact LinearMap.ker_eq_bot.mp h

end SpectralTheory

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype 1 (`endomorphism`):**
Inner derivation endomorphism `ad_P(X) = comm P X` satisfies the tripotent operator law
`comm P (comm P (comm P X)) = comm P X`. -/
theorem archetype_endomorphism_inner_derivation_tripotence
    {P : B} (hP : P * P = P) (X : B) :
    comm P (comm P (comm P X)) = comm P X ∧
    comm P (comm P X) = oddGrade P X := by
  refine ⟨?_, ?_⟩
  · peirce_nf hP
  · simp only [oddGrade]; peirce_nf hP

/-- **Archetype 2 (`kernelSubspace`):**
The kernel subspace of `ad_P` contains the entire even-grade Peirce subalgebra
`evenGrade P X = P X P + (1 - P) X (1 - P)`:
`comm P (evenGrade P X) = 0`, `comm P (genV P A C) = 0`, and `comm P (genSig P A C) = 0`. -/
theorem archetype_kernelSubspace_even_grade_centralizer
    {P : B} (hP : P * P = P) (A C X : B) :
    comm P (evenGrade P X) = 0 ∧
    comm P (genV P A C) = 0 ∧
    comm P (genSig P A C) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [evenGrade]; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- **Archetype 3 (`trivialKernel`):**
On the off-diagonal odd-grade subspace `oddGrade P X`, `ad_P²` acts as the identity
(`comm P (comm P (oddGrade P X)) = oddGrade P X`), so `comm P (oddGrade P X) = 0` implies
`oddGrade P X = 0`. -/
theorem archetype_trivialKernel_on_odd_grade
    {P : B} (hP : P * P = P) (X : B) :
    comm P (comm P (oddGrade P X)) = oddGrade P X ∧
    (comm P (oddGrade P X) = 0 → oddGrade P X = 0) := by
  have h1 : comm P (comm P (oddGrade P X)) = oddGrade P X := by
    simp only [oddGrade]; peirce_nf hP
  refine ⟨h1, fun h0 => ?_⟩
  rw [← h1, h0]
  dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  noncomm_ring

/-- **Archetype 4 (`spectralGap`):**
Operator-valued Casimir spectral gap on the odd-grade generators `(Φ, J)`:
`derivSqSig P A C (genPhi P A C) = -4 • ((V * V) * Φ)` and
`derivSqSig P A C (genJ P A C) = -4 • ((V * V) * J)`. -/
theorem archetype_spectralGap_casimir_eigenvalue
    {P : B} (hP : P * P = P) (A C : B) :
    derivSqSig P A C (genPhi P A C) = -((4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) ∧
    derivSqSig P A C (genJ P A C) = -((4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)) := by
  refine ⟨?_, ?_⟩ <;>
    (simp only [derivSqSig]; peirce_nf hP)

/-- **Archetype 5 (`automorphism`):**
Grading reflection `X ↦ invS P * X * invS P` is an involutive ring automorphism of `B`
(`invS P * (invS P * X * invS P) * invS P = X` and
`(invS P * X * invS P) * (invS P * Y * invS P) = invS P * (X * Y) * invS P`). -/
theorem archetype_automorphism_grading_conjugation
    {P : B} (hP : P * P = P) (X Y : B) :
    invS P * (invS P * X * invS P) * invS P = X ∧
    (invS P * X * invS P) * (invS P * Y * invS P) = invS P * (X * Y) * invS P := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Master Synthesis (`canonical_spectral_gap_operator_master_synthesis`):**
Combines the 5-stage causal order with all five non-commutative `[Ring B]` spectral-gap
and kernel theorems. -/
theorem canonical_spectral_gap_operator_master_synthesis
    {P : B} (hP : P * P = P) (A C X Y : B) :
    (causallyPrecedes .endomorphism .kernelSubspace ∧
      causallyPrecedes .kernelSubspace .trivialKernel ∧
      causallyPrecedes .trivialKernel .spectralGap ∧
      causallyPrecedes .spectralGap .automorphism) ∧
    (comm P (comm P (comm P X)) = comm P X) ∧
    (comm P (evenGrade P X) = 0) ∧
    (comm P (comm P (oddGrade P X)) = oddGrade P X) ∧
    (derivSqSig P A C (genPhi P A C) = -((4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C))) ∧
    ((invS P * X * invS P) * (invS P * Y * invS P) = invS P * (X * Y) * invS P) := by
  have h1 := archetype_endomorphism_inner_derivation_tripotence hP X
  have h2 := archetype_kernelSubspace_even_grade_centralizer hP A C X
  have h3 := archetype_trivialKernel_on_odd_grade hP X
  have h4 := archetype_spectralGap_casimir_eigenvalue hP A C
  have h5 := archetype_automorphism_grading_conjugation hP X Y
  exact ⟨by simp [causallyPrecedes, rank], h1.1, h2.1, h3.1, h4.1, h5.2⟩

end NonCommutativeOperatorRealization

end InfoGeometry.GrandUnification.CanonicalSpectralGap
