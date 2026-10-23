/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BoundaryRepresentationKernel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BoundaryFibonacciHorizonIntertwiner

/-!
# Quotient factorization for boundary-to-target intertwiners

The direct boundary/Fibonacci intertwiner is known to vanish.  This file
records conditional descent through an invariant source submodule.
Quotienting alone does not evade the zero-Hom obstruction: an intertwiner
from such a quotient pulls back along its surjective quotient map.
No particular invariant submodule or nonzero intertwiner is constructed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.BoundaryFibonacciQuotientFactorization

open InfoGeometry.Canonical.BoundaryFibonacciHorizonIntertwiner
open InfoGeometry.Canonical.BoundaryBraidRepresentation
open InfoGeometry.Physics.Algebra.FibonacciHorizonBraidBridge

variable {R V W : Type*}
  [CommRing R]
  [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module R W]

/-- The quotient map induced by a linear map which kills the chosen submodule. -/
def quotientFactor
    (S : Submodule R V)
    (Φ : V →ₗ[R] W)
    (hΦ : S ≤ LinearMap.ker Φ) : V ⧸ S →ₗ[R] W :=
  S.liftQ Φ hΦ

@[simp] theorem quotientFactor_mk
    (S : Submodule R V)
    (Φ : V →ₗ[R] W)
    (hΦ : S ≤ LinearMap.ker Φ)
    (v : V) :
    quotientFactor S Φ hΦ (S.mkQ v) = Φ v := by
  exact Submodule.liftQ_apply S Φ v

theorem quotientFactor_comp_mkQ
    (S : Submodule R V)
    (Φ : V →ₗ[R] W)
    (hΦ : S ≤ LinearMap.ker Φ) :
    (quotientFactor S Φ hΦ).comp S.mkQ = Φ := by
  exact Submodule.liftQ_mkQ S Φ hΦ

theorem quotientFactor_unique
    (S : Submodule R V)
    (Φ : V →ₗ[R] W)
    (hΦ : S ≤ LinearMap.ker Φ)
    (g : V ⧸ S →ₗ[R] W)
    (hg : g.comp S.mkQ = Φ) :
    g = quotientFactor S Φ hΦ := by
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := S.mkQ_surjective q
  have hgv := congrArg (fun f => f v) hg
  simpa [LinearMap.comp_apply, quotientFactor] using hgv

/-- The source action descends to the quotient when the submodule is invariant. -/
def quotientAction
    (S : Submodule R V)
    (T : V →ₗ[R] V)
    (hT : ∀ v, v ∈ S → T v ∈ S) :
    V ⧸ S →ₗ[R] V ⧸ S := by
  apply S.liftQ (S.mkQ.comp T)
  intro v hv
  simp only [LinearMap.mem_ker]
  exact (Submodule.Quotient.mk_eq_zero S).2 (hT v hv)

@[simp] theorem quotientAction_mk
    (S : Submodule R V)
    (T : V →ₗ[R] V)
    (hT : ∀ v, v ∈ S → T v ∈ S)
    (v : V) :
    quotientAction S T hT (S.mkQ v) = S.mkQ (T v) := by
  exact Submodule.liftQ_apply S (S.mkQ.comp T) v

theorem quotientAction_comp_mkQ
    (S : Submodule R V)
    (T : V →ₗ[R] V)
    (hT : ∀ v, v ∈ S → T v ∈ S) :
    (quotientAction S T hT).comp S.mkQ = S.mkQ.comp T := by
  exact Submodule.liftQ_mkQ S (S.mkQ.comp T) _

/-- An intertwiner that kills an invariant source submodule factors through its
quotient, and the factor still intertwines the descended source action. -/
theorem quotientFactor_intertwines
    (S : Submodule R V)
    (source : V →ₗ[R] V)
    (target : W →ₗ[R] W)
    (Φ : V →ₗ[R] W)
    (hS : ∀ v, v ∈ S → source v ∈ S)
    (hΦ : S ≤ LinearMap.ker Φ)
    (hintertwine : Φ.comp source = target.comp Φ) :
    (quotientFactor S Φ hΦ).comp (quotientAction S source hS) =
      target.comp (quotientFactor S Φ hΦ) := by
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := S.mkQ_surjective q
  simp only [LinearMap.comp_apply, quotientAction_mk, quotientFactor_mk]
  exact congrArg (fun f => f v) hintertwine

/-- Conditional two-generator factorization for the boundary/Fibonacci actions.
The intertwining hypotheses already force the original map, and hence its
quotient factor, to vanish. This is not a nonzero indirect realization. -/
theorem boundaryFibonacci_quotient_factor_intertwines
    (S : Submodule ℂ BoundaryBraidState)
    (Φ : BoundaryBraidState →ₗ[ℂ] HorizonSpace)
    (hS0 : ∀ v, v ∈ S → boundarySig0 v ∈ S)
    (hS1 : ∀ v, v ∈ S → boundarySig1 v ∈ S)
    (hΦ : S ≤ LinearMap.ker Φ)
    (h0 : Φ.comp boundarySig0 =
      (horizonLinR : Module.End ℂ HorizonSpace).comp Φ)
    (h1 : Φ.comp boundarySig1 =
      (horizonLinB : Module.End ℂ HorizonSpace).comp Φ) :
    (quotientFactor S Φ hΦ).comp
        (quotientAction S boundarySig0 hS0) =
        (horizonLinR : Module.End ℂ HorizonSpace).comp
          (quotientFactor S Φ hΦ) ∧
      (quotientFactor S Φ hΦ).comp
        (quotientAction S boundarySig1 hS1) =
        (horizonLinB : Module.End ℂ HorizonSpace).comp
          (quotientFactor S Φ hΦ) := by
  exact ⟨quotientFactor_intertwines S boundarySig0 horizonLinR Φ
      hS0 hΦ h0,
    quotientFactor_intertwines S boundarySig1 horizonLinB Φ
      hS1 hΦ h1⟩

end InfoGeometry.Canonical.BoundaryFibonacciQuotientFactorization
