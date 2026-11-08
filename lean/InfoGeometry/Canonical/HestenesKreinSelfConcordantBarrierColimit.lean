import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport
import InfoGeometry.Canonical.SelfConcordantZetaBarrier
import InfoGeometry.Geometry.LegendreDifferential

/-!
# Itakura--Saito barrier transport on the Hestenes--Krein colimit

This owner translates the finite real self-concordant barrier kernel into the
Hestenes--Krein colimit language.  The positive scalar readout and its
compatibility are explicit premises.  No infinite prime sum, zeta barrier,
or RH variational theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinSelfConcordantBarrierColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Canonical.SelfConcordantZetaBarrier
open InfoGeometry.Krein
open InfoGeometry.Geometry.LegendreDifferential

/-- The Hessian quadratic form of a real potential.  This is the positive
    local form used for Dikin geometry; it is distinct from the indefinite
    Hestenes--Krein pairing. -/
noncomputable def hessianQuadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (potential : E → ℝ) (x v : E) : ℝ :=
  hessianMap potential x v v

/-- The Hessian seminorm used to define a Dikin ellipsoid.  Positive
    definiteness is a separate property of the chosen barrier. -/
noncomputable def dikinHessianNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (potential : E → ℝ) (x v : E) : ℝ :=
  Real.sqrt (hessianQuadratic potential x v)

/-- Open unit Dikin ellipsoid at `x`, defined by the barrier Hessian. -/
def dikinEllipsoid
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (potential : E → ℝ) (x : E) : Set E :=
  {y | hessianQuadratic potential x (y - x) < 1}

/-- A linear map preserving the Hessian bilinear form preserves its diagonal
    quadratic form, hence its Dikin Hessian seminorm. -/
theorem hessianCompatible_dikinNorm_eq
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (potentialE : E → ℝ) (potentialF : F → ℝ)
    (T : E →L[ℝ] F) (x v : E)
    (hHessian : ∀ u w : E,
      hessianMap potentialF (T x) (T u) (T w) =
        hessianMap potentialE x u w) :
    dikinHessianNorm potentialF (T x) (T v) =
      dikinHessianNorm potentialE x v := by
  unfold dikinHessianNorm hessianQuadratic
  rw [hHessian v v]

/-- Hessian-compatible linear maps send the source Dikin ellipsoid into the
    target Dikin ellipsoid.  No assertion about boundary traces is involved. -/
theorem hessianCompatible_maps_dikinEllipsoid
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (potentialE : E → ℝ) (potentialF : F → ℝ)
    (T : E →L[ℝ] F) (x : E)
    (hHessian : ∀ u w : E,
      hessianMap potentialF (T x) (T u) (T w) =
        hessianMap potentialE x u w) :
    T '' dikinEllipsoid potentialE x ⊆ dikinEllipsoid potentialF (T x) := by
  rintro y ⟨z, hz, rfl⟩
  change hessianQuadratic potentialF (T x) (T z - T x) < 1
  rw [show T z - T x = T (z - x) by exact (map_sub T z x).symm]
  unfold hessianQuadratic
  rw [hHessian (z - x) (z - x)]
  exact hz

/-- The Drazin--Dikin quadratic form: forcing is first sent through the
    generalized Green operator, then measured by the barrier Hessian. -/
noncomputable def drazinDikinQuadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (potential : E → ℝ) (x : E) (green : E →L[ℝ] E) (v : E) : ℝ :=
  hessianQuadratic potential x (green v)

/-- The transport-admissible forcing ellipsoid, defined by the Drazin--Dikin
    quadratic form.  This is a sublevel set of forcing vectors; the barrier
    containment applies to their Green responses. -/
def drazinDikinEllipsoid
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (potential : E → ℝ) (x : E) (green : E →L[ℝ] E) : Set E :=
  {v | drazinDikinQuadratic potential x green v < 1}

/-- Intertwining Laplacians and their chosen Drazin Green operators intertwines
    the dynamic projectors `L G`.  The inverse intertwining is a separate
    premise: it is not inferred from Laplacian intertwining alone. -/
theorem drazinDynamicProjector_intertwines
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (Lₙ Gₙ : E →ₗ[ℝ] E) (Lₘ Gₘ : F →ₗ[ℝ] F)
    (T : E →ₗ[ℝ] F)
    (hL : T.comp Lₙ = Lₘ.comp T)
    (hG : T.comp Gₙ = Gₘ.comp T) :
    T.comp (Lₙ.comp Gₙ) = (Lₘ.comp Gₘ).comp T := by
  calc
    T.comp (Lₙ.comp Gₙ) = (T.comp Lₙ).comp Gₙ := by
      rw [LinearMap.comp_assoc]
    _ = (Lₘ.comp T).comp Gₙ := by rw [hL]
    _ = Lₘ.comp (T.comp Gₙ) := by rw [LinearMap.comp_assoc]
    _ = Lₘ.comp (Gₘ.comp T) := by rw [hG]
    _ = (Lₘ.comp Gₘ).comp T := by rw [LinearMap.comp_assoc]

/-- Hessian compatibility and Green-operator intertwining preserve the
    Drazin--Dikin quadratic form under a linear transition map. -/
theorem drazinDikinQuadratic_intertwines
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (potentialE : E → ℝ) (potentialF : F → ℝ)
    (T : E →L[ℝ] F) (x v : E)
    (greenE : E →L[ℝ] E) (greenF : F →L[ℝ] F)
    (hGreen : ∀ w : E, T (greenE w) = greenF (T w))
    (hHessian : ∀ u w : E,
      hessianMap potentialF (T x) (T u) (T w) =
        hessianMap potentialE x u w) :
    drazinDikinQuadratic potentialF (T x) greenF (T v) =
      drazinDikinQuadratic potentialE x greenE v := by
  unfold drazinDikinQuadratic hessianQuadratic
  rw [← hGreen v, hHessian (greenE v) (greenE v)]

/-- The corresponding filtered transport carries every source admissible
    forcing to a target admissible forcing. -/
theorem drazinDikinEllipsoid_maps
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (potentialE : E → ℝ) (potentialF : F → ℝ)
    (T : E →L[ℝ] F) (x : E)
    (greenE : E →L[ℝ] E) (greenF : F →L[ℝ] F)
    (hGreen : ∀ w : E, T (greenE w) = greenF (T w))
    (hHessian : ∀ u w : E,
      hessianMap potentialF (T x) (T u) (T w) =
        hessianMap potentialE x u w) :
    T '' drazinDikinEllipsoid potentialE x greenE ⊆
      drazinDikinEllipsoid potentialF (T x) greenF := by
  rintro y ⟨v, hv, rfl⟩
  change drazinDikinQuadratic potentialF (T x) greenF (T v) < 1
  rw [drazinDikinQuadratic_intertwines potentialE potentialF T x v
    greenE greenF hGreen hHessian]
  exact hv

def stageBarrier
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  isBarrierKernel (readout n x)

def limitBarrier
    {C : HestenesKreinCone}
    (readout : DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  isBarrierKernel (readout x)

theorem stageBarrier_eq_limitBarrier
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, readout n x = limitReadout (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageBarrier readout n x = limitBarrier limitReadout (C.ι n x) := by
  unfold stageBarrier limitBarrier
  rw [hreadout n x]

theorem stageBarrier_bondIterate_eq
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n m x,
      readout (n + m)
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
        readout n x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageBarrier readout (n + m)
        (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
      stageBarrier readout n x := by
  unfold stageBarrier
  rw [hreadout n m x]

theorem stageBarrier_nonneg
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hpositive : ∀ n x, 0 < readout n x)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 ≤ stageBarrier readout n x := by
  exact isBarrierKernel_nonneg (readout n x) (hpositive n x)

theorem stageBarrier_pos_of_ne_one
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hpositive : ∀ n x, 0 < readout n x)
    (hne : ∀ n x, readout n x ≠ 1)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 < stageBarrier readout n x := by
  exact isBarrierKernel_pos (readout n x) (hpositive n x) (hne n x)

theorem limitBarrier_pos_of_stage_ne_one
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, readout n x = limitReadout (C.ι n x))
    (hpositive : ∀ n x, 0 < readout n x)
    (hne : ∀ n x, readout n x ≠ 1)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 < limitBarrier limitReadout (C.ι n x) := by
  rw [← stageBarrier_eq_limitBarrier readout limitReadout hreadout n x]
  exact stageBarrier_pos_of_ne_one readout hpositive hne n x

end InfoGeometry.Canonical.HestenesKreinSelfConcordantBarrierColimit

end noncomputable section
