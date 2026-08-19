import DAG.TripleSystem
import InfoGeometry.Canonical.HestenesPhaseSemilinear
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.RealIncidenceHomology

Linear real incidence homology/cohomology primitives.

This file is the concrete linear companion to `RealIncidenceHomologyBridge`.
It provides:

* real chain complexes with `∂ ∘ ∂ = 0`;
* cycle spaces as kernels and boundary spaces as ranges;
* the theorem `boundaries_le_cycles` needed before quotient homology is valid;
* degree-0/1 incidence edges for `DAG.TripleSystem`;
* real object-potential coboundaries `δ⁰ φ(edge) = φ(target) - φ(source)`;
* a Hestenes phase-semilinear chain-complex interface.

It does not construct singular homology, de Rham cohomology, quotient-space
homology groups, higher incidence faces, or scalar-complex coefficient lanes.
-/

namespace InfoGeometry.Canonical.RealIncidenceHomology

open InfoGeometry.Krein
open InfoGeometry.Canonical.HestenesPhaseSemilinear

/--
A real chain complex with successor-indexed boundary maps
`boundary n : C (n+1) -> C n`.
-/
@[rep_depth transport]
structure RealChainComplex where
  C : ℕ → Type u
  instAdd : ∀ n, AddCommGroup (C n)
  instModule : ∀ n, Module ℝ (C n)
  boundary : ∀ n, C (n + 1) →ₗ[ℝ] C n
  boundary_boundary :
    ∀ n, (boundary n).comp (boundary (n + 1)) = 0

namespace RealChainComplex

variable (K : RealChainComplex)

attribute [local instance] RealChainComplex.instAdd RealChainComplex.instModule

/-- Degree `n+1` cycles are `ker(∂ₙ)`. -/
@[rep_depth transport]
def CyclesAtSucc (n : ℕ) : Submodule ℝ (K.C (n + 1)) :=
  LinearMap.ker (K.boundary n)

/-- Degree `n+1` boundaries are `range(∂ₙ₊₁)`. -/
@[rep_depth transport]
def BoundariesAtSucc (n : ℕ) : Submodule ℝ (K.C (n + 1)) :=
  LinearMap.range (K.boundary (n + 1))

/-- Readback of chain-complex nilpotence. -/
@[rep_depth transport]
theorem boundary_boundary_readback
    (n : ℕ) :
    (K.boundary n).comp (K.boundary (n + 1)) = 0 :=
  K.boundary_boundary n

/-- Boundaries are cycles: `range(∂ₙ₊₁) ≤ ker(∂ₙ)`. -/
@[rep_depth transport]
theorem boundariesAtSucc_le_cyclesAtSucc
    (n : ℕ) :
    K.BoundariesAtSucc n ≤ K.CyclesAtSucc n := by
  intro x hx
  rcases hx with ⟨y, hy⟩
  change K.boundary n x = 0
  rw [← hy]
  have h := congrArg (fun F : K.C (n + 2) →ₗ[ℝ] K.C n => F y)
    (K.boundary_boundary n)
  simpa [LinearMap.comp_apply] using h

end RealChainComplex

/--
A real cochain complex with successor-indexed coboundary maps
`coboundary n : C^n -> C^(n+1)`.
-/
@[rep_depth transport]
structure RealCochainComplex where
  C : ℕ → Type u
  instAdd : ∀ n, AddCommGroup (C n)
  instModule : ∀ n, Module ℝ (C n)
  coboundary : ∀ n, C n →ₗ[ℝ] C (n + 1)
  coboundary_coboundary :
    ∀ n, (coboundary (n + 1)).comp (coboundary n) = 0

namespace RealCochainComplex

variable (K : RealCochainComplex)

attribute [local instance] RealCochainComplex.instAdd RealCochainComplex.instModule

/-- Degree `n` cocycles are `ker(δⁿ)`. -/
@[rep_depth transport]
def Cocycles (n : ℕ) : Submodule ℝ (K.C n) :=
  LinearMap.ker (K.coboundary n)

/-- Degree `n+1` coboundaries are `range(δⁿ)`. -/
@[rep_depth transport]
def CoboundariesAtSucc (n : ℕ) : Submodule ℝ (K.C (n + 1)) :=
  LinearMap.range (K.coboundary n)

/-- Readback of cochain-complex nilpotence. -/
@[rep_depth transport]
theorem coboundary_coboundary_readback
    (n : ℕ) :
    (K.coboundary (n + 1)).comp (K.coboundary n) = 0 :=
  K.coboundary_coboundary n

/-- Coboundaries are cocycles: `range(δⁿ) ≤ ker(δⁿ⁺¹)`. -/
@[rep_depth transport]
theorem coboundariesAtSucc_le_cocycles
    (n : ℕ) :
    K.CoboundariesAtSucc n ≤ K.Cocycles (n + 1) := by
  intro x hx
  rcases hx with ⟨y, hy⟩
  change K.coboundary (n + 1) x = 0
  rw [← hy]
  have h := congrArg (fun F : K.C n →ₗ[ℝ] K.C (n + 2) => F y)
    (K.coboundary_coboundary n)
  simpa [LinearMap.comp_apply] using h

end RealCochainComplex

namespace Incidence

/-- A valid degree-1 incidence edge of a `DAG.TripleSystem`. -/
@[rep_depth transport]
structure Edge (A : DAG.TripleSystem) where
  src : A.Obj
  rel : A.Rel
  tgt : A.Obj
  valid : A.triple src rel tgt

namespace Edge

variable {A : DAG.TripleSystem}

/-- Map incidence edges along a triple homomorphism. -/
@[rep_depth transport]
def map {B : DAG.TripleSystem} (F : DAG.TripleSystem.Hom A B) (e : Edge A) : Edge B where
  src := F.mapObj e.src
  rel := F.mapRel e.rel
  tgt := F.mapObj e.tgt
  valid := F.preserves e.valid

@[simp] theorem map_src {B : DAG.TripleSystem}
    (F : DAG.TripleSystem.Hom A B) (e : Edge A) :
    (map F e).src = F.mapObj e.src := rfl

@[simp] theorem map_rel {B : DAG.TripleSystem}
    (F : DAG.TripleSystem.Hom A B) (e : Edge A) :
    (map F e).rel = F.mapRel e.rel := rfl

@[simp] theorem map_tgt {B : DAG.TripleSystem}
    (F : DAG.TripleSystem.Hom A B) (e : Edge A) :
    (map F e).tgt = F.mapObj e.tgt := rfl

end Edge

/-- Real degree-0 cochains are object potentials. -/
@[rep_depth transport]
abbrev ZeroCochain (A : DAG.TripleSystem) := A.Obj → ℝ

/-- Real degree-1 cochains are edge observables. -/
@[rep_depth transport]
abbrev OneCochain (A : DAG.TripleSystem) := Edge A → ℝ

/-- The degree-0 incidence coboundary `δ⁰ φ(s,p,o) = φ(o) - φ(s)`. -/
@[rep_depth transport]
def zeroCoboundary {A : DAG.TripleSystem} (φ : ZeroCochain A) : OneCochain A :=
  fun e => φ e.tgt - φ e.src

/-- Pointwise readback of the incidence coboundary formula. -/
@[rep_depth transport]
theorem zeroCoboundary_apply {A : DAG.TripleSystem}
    (φ : ZeroCochain A) (e : Edge A) :
    zeroCoboundary φ e = φ e.tgt - φ e.src :=
  rfl

/-- A degree-0 cocycle/potential is constant along every incidence edge. -/
@[rep_depth transport]
def IsZeroCocycle {A : DAG.TripleSystem} (φ : ZeroCochain A) : Prop :=
  ∀ e : Edge A, φ e.tgt = φ e.src

/-- Zero coboundary is equivalent to constancy along incidence edges. -/
@[rep_depth transport]
theorem isZeroCocycle_iff_zeroCoboundary_eq_zero {A : DAG.TripleSystem}
    (φ : ZeroCochain A) :
    IsZeroCocycle φ ↔ zeroCoboundary φ = 0 := by
  constructor
  · intro h
    funext e
    simp [zeroCoboundary, h e]
  · intro h e
    have hp := congrArg (fun ψ : OneCochain A => ψ e) h
    simpa [zeroCoboundary, sub_eq_zero] using hp

end Incidence

/--
A Hestenes phase-semilinear real chain complex.

`phase n` is the internal `K`-axis on degree `n`, and `boundary_phase` says the
boundary transports `K` by the supplied `PhaseTwist` sign.
-/
@[rep_depth krein]
structure HestenesChainComplex where
  C : ℕ → Type u
  instAdd : ∀ n, AddCommGroup (C n)
  instModule : ∀ n, Module ℝ (C n)
  boundary : ∀ n, C (n + 1) →ₗ[ℝ] C n
  boundary_boundary :
    ∀ n, (boundary n).comp (boundary (n + 1)) = 0
  phase : ∀ n, C n →ₗ[ℝ] C n
  phase_sq_neg : ∀ n, (phase n).comp (phase n) = -(LinearMap.id : C n →ₗ[ℝ] C n)
  twist : ∀ n, PhaseTwist
  boundary_phase :
    ∀ n,
      (boundary n).comp (phase (n + 1)) =
        (twist n).sign • ((phase n).comp (boundary n))

namespace HestenesChainComplex

variable (K : HestenesChainComplex)

attribute [local instance] HestenesChainComplex.instAdd HestenesChainComplex.instModule

/-- Forget the Hestenes phase structure and retain the underlying real chain complex. -/
@[rep_depth transport]
def toRealChainComplex : RealChainComplex where
  C := K.C
  instAdd := K.instAdd
  instModule := K.instModule
  boundary := K.boundary
  boundary_boundary := K.boundary_boundary

end HestenesChainComplex

end InfoGeometry.Canonical.RealIncidenceHomology
