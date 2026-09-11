import InfoGeometry.Canonical.RealIncidenceChains
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section

namespace InfoGeometry.Canonical.RealStokesGaussHomology

/-!
# Real Stokes/Gauss homology

This file proves the finite-support incidence Stokes identity for typed triple
systems:

`<∂₁ c, φ>₀ = <c, δ⁰ φ>₁`.

The theorem is purely real.  It does not introduce complex contours, de Rham
forms, analytic continuation, residues, or a Hodge theorem.
-/

open InfoGeometry.Canonical.RealIncidenceHomology
open InfoGeometry.Canonical.RealIncidenceChains

namespace Incidence

/-- Pair a degree-0 incidence chain with a real object potential. -/
@[rep_depth transport]
def pairingZeroLinear {A : DAG.TripleSystem}
    (φ : RealIncidenceHomology.Incidence.ZeroCochain A) :
    RealIncidenceChains.Incidence.ZeroChains A →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ φ

/-- Pair a degree-1 incidence chain with a real edge observable. -/
@[rep_depth transport]
def pairingOneLinear {A : DAG.TripleSystem}
    (ψ : RealIncidenceHomology.Incidence.OneCochain A) :
    RealIncidenceChains.Incidence.OneChains A →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ ψ

/-- Degree-0 chain/cochain pairing readback. -/
@[rep_depth transport]
def pairZero {A : DAG.TripleSystem}
    (c : RealIncidenceChains.Incidence.ZeroChains A)
    (φ : RealIncidenceHomology.Incidence.ZeroCochain A) : ℝ :=
  pairingZeroLinear (A := A) φ c

/-- Degree-1 chain/cochain pairing readback. -/
@[rep_depth transport]
def pairOne {A : DAG.TripleSystem}
    (c : RealIncidenceChains.Incidence.OneChains A)
    (ψ : RealIncidenceHomology.Incidence.OneCochain A) : ℝ :=
  pairingOneLinear (A := A) ψ c

/-- Pairing a basis edge boundary with a potential gives target-minus-source. -/
@[rep_depth transport]
theorem pairingZero_edgeBoundary
    {A : DAG.TripleSystem}
    [DecidableEq A.Obj]
    (φ : RealIncidenceHomology.Incidence.ZeroCochain A)
    (e : RealIncidenceHomology.Incidence.Edge A) :
    pairingZeroLinear (A := A) φ
        (RealIncidenceChains.Incidence.edgeBoundary (A := A) e)
      = φ e.tgt - φ e.src := by
  simp [pairingZeroLinear, RealIncidenceChains.Incidence.edgeBoundary]

/-- Linear-map form of real incidence Stokes/Gauss duality. -/
@[rep_depth transport]
theorem stokes_linear
    {A : DAG.TripleSystem}
    [DecidableEq A.Obj]
    (φ : RealIncidenceHomology.Incidence.ZeroCochain A) :
    (pairingZeroLinear (A := A) φ).comp
        (RealIncidenceChains.Incidence.boundaryOne A)
      = pairingOneLinear (A := A)
          (RealIncidenceHomology.Incidence.zeroCoboundary φ) := by
  apply Finsupp.lhom_ext
  intro e a
  calc
    ((pairingZeroLinear (A := A) φ).comp
        (RealIncidenceChains.Incidence.boundaryOne A))
        (Finsupp.single e a)
        = pairingZeroLinear (A := A) φ
            (a • RealIncidenceChains.Incidence.edgeBoundary (A := A) e) := by
            simp [LinearMap.comp_apply, RealIncidenceChains.Incidence.boundaryOne,
              Finsupp.linearCombination_single]
    _ = a * (φ e.tgt - φ e.src) := by
            simp [pairingZero_edgeBoundary]
    _ = pairingOneLinear (A := A)
          (RealIncidenceHomology.Incidence.zeroCoboundary φ)
          (Finsupp.single e a) := by
            simp [pairingOneLinear,
              RealIncidenceHomology.Incidence.zeroCoboundary,
              Finsupp.linearCombination_single]

/-- Real incidence Stokes/Gauss theorem: `<∂₁ c, φ>₀ = <c, δ⁰φ>₁`. -/
@[rep_depth transport]
theorem pairing_boundaryOne_eq_pairing_zeroCoboundary
    {A : DAG.TripleSystem}
    [DecidableEq A.Obj]
    (c : RealIncidenceChains.Incidence.OneChains A)
    (φ : RealIncidenceHomology.Incidence.ZeroCochain A) :
    pairZero (A := A) (RealIncidenceChains.Incidence.boundaryOne A c) φ
      = pairOne (A := A) c
          (RealIncidenceHomology.Incidence.zeroCoboundary φ) := by
  have h := congrArg
    (fun L : RealIncidenceChains.Incidence.OneChains A →ₗ[ℝ] ℝ => L c)
    (stokes_linear (A := A) φ)
  simpa [pairZero, pairOne, LinearMap.comp_apply] using h

end Incidence

end InfoGeometry.Canonical.RealStokesGaussHomology
