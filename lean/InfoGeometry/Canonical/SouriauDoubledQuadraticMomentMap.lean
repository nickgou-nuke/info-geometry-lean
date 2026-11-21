/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.ChiralBoundarySymplecticBridge
import InfoGeometry.Geometry.QuadraticPotentialCalculus
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# A real quadratic moment map on the canonical doubled space

This owner isolates the first genuine bridge from a linear symplectic generator
on `DoubledSpace E` to a real Hamiltonian.  The carrier is the existing
`WithLp 2 (E × E)` doubled space, and the symplectic form is the existing
coordinate form transported through its `WithLp` projections.

For a continuous linear generator `G` satisfying the infinitesimal symplectic
identity, the quadratic function
`z ↦ Ω (G z) z / 2` has derivative `v ↦ Ω (G z) v`.  No manifold,
probability, or Lipschitz--Killing curvature claim is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap

open InfoGeometry.Krein
open InfoGeometry.Geometry.QuadraticPotentialCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance : LieRing (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  LieAlgebra.ofAssociativeAlgebra

abbrev Doubled (E : Type*) := DoubledSpace E

/-- The canonical real symplectic form on the doubled `WithLp` carrier. -/
noncomputable def symplecticForm : Doubled E →L[ℝ] Doubled E →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (fst_L (E := E)) (snd_L (E := E)) -
    (innerSL ℝ).bilinearComp (snd_L (E := E)) (fst_L (E := E))

@[simp] lemma symplecticForm_apply (u v : Doubled E) :
    symplecticForm u v =
      inner ℝ (WithLp.fst u) (WithLp.snd v) -
        inner ℝ (WithLp.snd u) (WithLp.fst v) :=
  rfl

/-- This is the existing chiral boundary form after `WithLp` readback. -/
lemma symplecticForm_eq_chiral (u v : Doubled E) :
    symplecticForm u v =
      InfoGeometry.Canonical.ChiralBoundarySymplectic.ChiralDoubled.symplecticForm
        (WithLp.ofLp u) (WithLp.ofLp v) := by
  simp [symplecticForm,
    InfoGeometry.Canonical.ChiralBoundarySymplectic.ChiralDoubled.symplecticForm,
    real_inner_comm]

lemma symplecticForm_skew (u v : Doubled E) :
    symplecticForm u v = -symplecticForm v u := by
  rw [symplecticForm_apply, symplecticForm_apply]
  rw [real_inner_comm (WithLp.fst v) (WithLp.snd u),
    real_inner_comm (WithLp.fst u) (WithLp.snd v)]
  ring

/-- The symplectic form is represented by the canonical real clock axis and
the positive doubled Hilbert product. -/
lemma symplecticForm_eq_inner_clockAxis (u v : Doubled E) :
    symplecticForm u v = inner ℝ (clockAxis u) v := by
  rw [symplecticForm_apply, clockAxis_apply]
  simp only [WithLp.prod_inner_apply]
  rw [inner_neg_left]
  simp only [WithLp.fst, WithLp.snd]
  ring

/-- Infinitesimal preservation of the canonical doubled symplectic form. -/
def IsSymplecticGenerator (G : Doubled E →L[ℝ] Doubled E) : Prop :=
  ∀ u v, symplecticForm (G u) v + symplecticForm u (G v) = 0

lemma symplecticForm_comp_generator_symmetric
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G)
    (u v : Doubled E) :
    symplecticForm (G u) v = symplecticForm (G v) u := by
  have hskew := symplecticForm_skew u (G v)
  linarith [hG u v]

/-- The quadratic Souriau Hamiltonian attached to a linear symplectic generator. -/
noncomputable def quadraticMoment
    (G : Doubled E →L[ℝ] Doubled E) (z : Doubled E) : ℝ :=
  potential (symplecticForm.comp G) z

@[simp] lemma quadraticMoment_apply
    (G : Doubled E →L[ℝ] Doubled E) (z : Doubled E) :
    quadraticMoment G z = symplecticForm (G z) z / 2 :=
  rfl

/-- The genuine real Fréchet derivative of the quadratic moment map. -/
theorem hasFDerivAt_quadraticMoment
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G)
    (z : Doubled E) :
    HasFDerivAt (quadraticMoment G) (symplecticForm (G z)) z := by
  exact hasFDerivAt_potential (symplecticForm.comp G)
    (fun u v => symplecticForm_comp_generator_symmetric G hG u v) z

/-- Pointwise form of the Hamiltonian identity `dH = ι_(Gz) Ω`. -/
theorem fderiv_quadraticMoment
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G)
    (z v : Doubled E) :
    fderiv ℝ (quadraticMoment G) z v = symplecticForm (G z) v := by
  rw [(hasFDerivAt_quadraticMoment G hG z).fderiv]

/-- The infinitesimal symplectic identity is the operator equation
`K G + G† K = 0`, where `K` is the canonical real clock axis and `†` is the
positive doubled Hilbert adjoint. -/
theorem symplecticGenerator_adjoint_identity
    [CompleteSpace E] (G : Doubled E →L[ℝ] Doubled E)
    (hG : IsSymplecticGenerator G) :
    clockAxis.comp G + (ContinuousLinearMap.adjoint G).comp clockAxis = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  let w : Doubled E := (clockAxis.comp G + (ContinuousLinearMap.adjoint G).comp clockAxis) u
  change w = 0
  apply (inner_self_eq_zero (𝕜 := ℝ) (x := w)).mp
  have h := hG u w
  rw [symplecticForm_eq_inner_clockAxis, symplecticForm_eq_inner_clockAxis] at h
  rw [← ContinuousLinearMap.adjoint_inner_left G w (clockAxis u)] at h
  rw [← inner_add_left] at h
  simpa [w, add_apply, ContinuousLinearMap.comp_apply] using h

/-- Solving the infinitesimal identity for the Hilbert adjoint uses the
real clock-axis square `K² = -1`: `G† = K G K`. -/
theorem adjoint_eq_clockAxis_comp_generator_comp_clockAxis
    [CompleteSpace E] (G : Doubled E →L[ℝ] Doubled E)
    (hG : IsSymplecticGenerator G) :
    ContinuousLinearMap.adjoint G =
      clockAxis.comp (G.comp clockAxis) := by
  apply ContinuousLinearMap.ext
  intro u
  have hsq : clockAxis (clockAxis u) = -u := by
    have h := congrArg (fun T : Doubled E →L[ℝ] Doubled E => T u) (clockAxis_sq E)
    simpa [ContinuousLinearMap.comp_apply] using h
  have h := congrArg (fun T : Doubled E →L[ℝ] Doubled E => T (clockAxis u))
    (symplecticGenerator_adjoint_identity G hG)
  simp only [add_apply, ContinuousLinearMap.comp_apply] at h
  rw [hsq, map_neg] at h
  have h' : clockAxis (G (clockAxis u)) - ContinuousLinearMap.adjoint G u = 0 := by
    simpa [sub_eq_add_neg] using h
  exact (sub_eq_zero.mp h').symm

/-- The real clock axis is a unit in the bounded-operator algebra, with
inverse `-K`; this is the algebraic datum needed for conjugating exponentials. -/
noncomputable def clockAxisUnit [CompleteSpace E] :
    (Doubled E →L[ℝ] Doubled E)ˣ where
  val := clockAxis
  inv := -clockAxis
  val_inv := by
    apply ContinuousLinearMap.ext
    intro u
    change clockAxis (-clockAxis u) = u
    rw [map_neg]
    have hsq := congrArg (fun T : Doubled E →L[ℝ] Doubled E => T u) (clockAxis_sq E)
    simpa [ContinuousLinearMap.comp_apply] using congrArg Neg.neg hsq
  inv_val := by
    apply ContinuousLinearMap.ext
    intro u
    change -clockAxis (clockAxis u) = u
    have hsq := congrArg (fun T : Doubled E →L[ℝ] Doubled E => T u) (clockAxis_sq E)
    simpa [ContinuousLinearMap.comp_apply] using congrArg Neg.neg hsq

/-- The canonical doubled symplectic form is nondegenerate, transported from
the existing chiral product-space proof through `WithLp.ofLp`. -/
theorem symplecticForm_nondegenerate (u : Doubled E)
    (h : ∀ v, symplecticForm u v = 0) :
    u = 0 := by
  apply WithLp.ofLp_injective (p := (2 : ENNReal))
  apply InfoGeometry.Canonical.ChiralBoundarySymplectic.ChiralDoubled.symplectic_nondegenerate
    (WithLp.ofLp u)
  intro v
  have hv := h (WithLp.toLp (2 : ENNReal) v)
  simpa [symplecticForm_eq_chiral,
    InfoGeometry.Canonical.ChiralBoundarySymplectic.ChiralDoubled.symplecticForm,
    real_inner_comm] using hv

/-- The quadratic moment separates infinitesimal symplectic generators: if
their Hamiltonians agree at every doubled state, then the generators agree. -/
theorem quadraticMoment_injective_on_symplecticGenerators
    {A B : Doubled E →L[ℝ] Doubled E}
    (hA : IsSymplecticGenerator A) (hB : IsSymplecticGenerator B)
    (h : quadraticMoment A = quadraticMoment B) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro z
  apply sub_eq_zero.mp
  apply symplecticForm_nondegenerate
  intro v
  have hd := congrArg (fun f : Doubled E → ℝ => fderiv ℝ f z v) h
  rw [fderiv_quadraticMoment A hA, fderiv_quadraticMoment B hB] at hd
  rw [map_sub, sub_apply]
  linarith

/-- The commutator of two infinitesimal symplectic generators is again
infinitesimally symplectic. This makes the generator carrier a Lie subalgebra. -/
theorem lie_isSymplecticGenerator
    {A B : Doubled E →L[ℝ] Doubled E}
    (hA : IsSymplecticGenerator A) (hB : IsSymplecticGenerator B) :
    IsSymplecticGenerator ⁅A, B⁆ := by
  intro u v
  change symplecticForm (A (B u) - B (A u)) v +
      symplecticForm u (A (B v) - B (A v)) = 0
  simp only [map_sub, sub_apply]
  have hA₁ := hA (B u) v
  have hA₂ := hA u (B v)
  have hB₁ := hB (A u) v
  have hB₂ := hB u (A v)
  linear_combination hA₁ - hB₁ + hA₂ - hB₂

/-- The real Lie algebra of continuous infinitesimal symplectic operators on
the canonical doubled carrier. -/
def symplecticGeneratorLieSubalgebra :
    LieSubalgebra ℝ (Doubled E →L[ℝ] Doubled E) where
  carrier := {G | IsSymplecticGenerator G}
  zero_mem' := by
    intro u v
    simp
  add_mem' := by
    intro A B hA hB u v
    change IsSymplecticGenerator A at hA
    change IsSymplecticGenerator B at hB
    simp only [add_apply, map_add]
    linear_combination hA u v + hB u v
  smul_mem' := by
    intro c A hA u v
    change IsSymplecticGenerator A at hA
    simp only [smul_apply, map_smul, smul_eq_mul]
    linear_combination c * hA u v
  lie_mem' := by
    intro A B hA hB
    exact lie_isSymplecticGenerator hA hB

/-- The Hamiltonian bracket of two linear moment-map components, in the
convention `{H_A,H_B}(z) = Ω(Az,Bz)`, is the component for the commutator
generator. Thus the quadratic map respects the generator Lie bracket. -/
def quadraticMomentBracket
    (A B : Doubled E →L[ℝ] Doubled E) (z : Doubled E) : ℝ :=
  symplecticForm (A z) (B z)

theorem quadraticMomentBracket_eq_commutatorMoment
    (A B : Doubled E →L[ℝ] Doubled E)
    (hA : IsSymplecticGenerator A) (hB : IsSymplecticGenerator B)
    (z : Doubled E) :
    quadraticMomentBracket A B z = quadraticMoment ⁅A, B⁆ z := by
  rw [quadraticMoment_apply]
  change symplecticForm (A z) (B z) =
    symplecticForm (A (B z) - B (A z)) z / 2
  rw [map_sub]
  have hA' := hA (B z) z
  have hB' := hB (A z) z
  have hskew := symplecticForm_skew (B z) (A z)
  have hAB : symplecticForm (A (B z)) z = symplecticForm (A z) (B z) := by
    linarith
  have hBA : symplecticForm (B (A z)) z = -symplecticForm (A z) (B z) := by
    linarith
  rw [sub_apply, hAB, hBA]
  ring

/-- A continuous linear equivalence preserving the doubled symplectic form. -/
def IsSymplecticEquiv (S : Doubled E ≃L[ℝ] Doubled E) : Prop :=
  ∀ u v, symplecticForm (S u) (S v) = symplecticForm u v

/-- Conjugation of a generator by a continuous linear equivalence. -/
noncomputable def conjugateGenerator
    (S : Doubled E ≃L[ℝ] Doubled E) (G : Doubled E →L[ℝ] Doubled E) :
    Doubled E →L[ℝ] Doubled E :=
  S.symm.toContinuousLinearMap.comp (G.comp S.toContinuousLinearMap)

/-- Symplectic conjugation preserves the infinitesimal generator identity. -/
theorem conjugateGenerator_isSymplecticGenerator
    (S : Doubled E ≃L[ℝ] Doubled E) (hS : IsSymplecticEquiv S)
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G) :
    IsSymplecticGenerator (conjugateGenerator S G) := by
  intro u v
  calc
    symplecticForm (conjugateGenerator S G u) v +
        symplecticForm u (conjugateGenerator S G v) =
        symplecticForm (S (conjugateGenerator S G u)) (S v) +
          symplecticForm (S u) (S (conjugateGenerator S G v)) := by
            rw [hS, hS]
    _ = symplecticForm (G (S u)) (S v) +
          symplecticForm (S u) (G (S v)) := by
            simp [conjugateGenerator]
    _ = 0 := hG (S u) (S v)

/-- The quadratic moment is equivariant under symplectic conjugation. -/
theorem quadraticMoment_equivariant
    (S : Doubled E ≃L[ℝ] Doubled E) (hS : IsSymplecticEquiv S)
    (G : Doubled E →L[ℝ] Doubled E) (z : Doubled E) :
    quadraticMoment G (S z) =
      quadraticMoment (conjugateGenerator S G) z := by
  rw [quadraticMoment_apply, quadraticMoment_apply]
  have hconj : S (conjugateGenerator S G z) = G (S z) := by
    simp [conjugateGenerator]
  rw [← hconj, hS]

end InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap
