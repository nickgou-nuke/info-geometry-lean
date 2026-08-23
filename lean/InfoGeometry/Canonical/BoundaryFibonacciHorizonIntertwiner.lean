import InfoGeometry.Canonical.BoundaryBraidRepresentation
import InfoGeometry.Physics.Algebra.FibonacciHorizonBraidBridge

/-!
# The finite intertwiner problem for the two braid carriers

The repository has two honest `B₃` actions: the eight-dimensional Jones--
Temperley--Lieb boundary action and the two-dimensional Fibonacci action on the
tripotent horizon carrier.  This file records their actual intertwiner space.

No nonzero intertwiner is assumed here.  The kernel below is the finite linear
system whose nontriviality is the remaining representation-theoretic question.
In particular, this owner does not identify the two carriers merely because
both satisfy the Artin relation.
-/

noncomputable section

namespace InfoGeometry.Canonical.BoundaryFibonacciHorizonIntertwiner

open InfoGeometry.Canonical.BoundaryBraidRepresentation
open InfoGeometry.Physics.Algebra.FibonacciHorizonBraidBridge
open InfoGeometry.Physics.B3PresentedGroup

def boundarySig0 : Module.End ℂ BoundaryBraidState :=
  (boundaryBraidLinearRepresentation
    (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) :
      BoundaryBraidState →ₗ[ℂ] BoundaryBraidState)

def boundarySig1 : Module.End ℂ BoundaryBraidState :=
  (boundaryBraidLinearRepresentation
    (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) :
      BoundaryBraidState →ₗ[ℂ] BoundaryBraidState)

/-- The pair of generator defects of a candidate boundary-to-horizon map. -/
def intertwinerDefect (Φ : BoundaryBraidState →ₗ[ℂ] HorizonSpace) :
    (BoundaryBraidState →ₗ[ℂ] HorizonSpace) ×
      (BoundaryBraidState →ₗ[ℂ] HorizonSpace) :=
  (Φ.comp boundarySig0 - horizonLinR.comp Φ,
    Φ.comp boundarySig1 - horizonLinB.comp Φ)

/-- The simultaneous linear system defining `B₃`-intertwiners. -/
def boundaryFibonacciIntertwinerOperator :
    (BoundaryBraidState →ₗ[ℂ] HorizonSpace) →ₗ[ℂ]
      ((BoundaryBraidState →ₗ[ℂ] HorizonSpace) ×
        (BoundaryBraidState →ₗ[ℂ] HorizonSpace)) where
  toFun := intertwinerDefect
  map_add' Φ Ψ := by
    apply Prod.ext
    · apply LinearMap.ext
      intro x
      simp [intertwinerDefect, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    · apply LinearMap.ext
      intro x
      simp [intertwinerDefect, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' c Φ := by
    change intertwinerDefect (c • Φ) = c • intertwinerDefect Φ
    apply Prod.ext
    · apply LinearMap.ext
      intro v
      change ((c • Φ).comp boundarySig0 - horizonLinR.comp (c • Φ)) v =
        c • ((Φ.comp boundarySig0 - horizonLinR.comp Φ) v)
      simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, smul_sub]
      module
    · apply LinearMap.ext
      intro v
      change ((c • Φ).comp boundarySig1 - horizonLinB.comp (c • Φ)) v =
        c • ((Φ.comp boundarySig1 - horizonLinB.comp Φ) v)
      simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, smul_sub]
      module

/-- The exact finite-dimensional intertwiner space for the two generator actions. -/
def boundaryFibonacciIntertwinerSpace :
    Submodule ℂ (BoundaryBraidState →ₗ[ℂ] HorizonSpace) :=
  LinearMap.ker boundaryFibonacciIntertwinerOperator

theorem mem_boundaryFibonacciIntertwinerSpace_iff
    (Φ : BoundaryBraidState →ₗ[ℂ] HorizonSpace) :
    Φ ∈ boundaryFibonacciIntertwinerSpace ↔
      Φ.comp boundarySig0 = horizonLinR.comp Φ ∧
      Φ.comp boundarySig1 = horizonLinB.comp Φ := by
  constructor
  · intro h
    have hzero := h
    change boundaryFibonacciIntertwinerOperator Φ = 0 at hzero
    have h0 := congrArg Prod.fst hzero
    have h1 := congrArg Prod.snd hzero
    exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩
  · rintro ⟨h0, h1⟩
    change boundaryFibonacciIntertwinerOperator Φ = 0
    apply Prod.ext
    · exact sub_eq_zero.mpr h0
    · exact sub_eq_zero.mpr h1

theorem boundaryFibonacciIntertwinerSpace_eq_bot_iff :
    boundaryFibonacciIntertwinerSpace = ⊥ ↔
      ∀ Φ : BoundaryBraidState →ₗ[ℂ] HorizonSpace,
        Φ.comp boundarySig0 = horizonLinR.comp Φ ∧
        Φ.comp boundarySig1 = horizonLinB.comp Φ →
        Φ = 0 := by
  constructor
  · intro h Φ hΦ
    have hmem : Φ ∈ boundaryFibonacciIntertwinerSpace :=
      (mem_boundaryFibonacciIntertwinerSpace_iff Φ).mpr hΦ
    have hzero : Φ ∈ (⊥ : Submodule ℂ
        (BoundaryBraidState →ₗ[ℂ] HorizonSpace)) := h ▸ hmem
    simpa using hzero
  · intro h
    apply le_antisymm
    · intro Φ hΦ
      have hzero := h Φ ((mem_boundaryFibonacciIntertwinerSpace_iff Φ).mp hΦ)
      simpa [hzero]
    · exact bot_le

end InfoGeometry.Canonical.BoundaryFibonacciHorizonIntertwiner
