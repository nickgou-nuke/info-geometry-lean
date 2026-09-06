import InfoGeometry.Canonical.FilteredGNSTomitaRealColimit

/-!
# Filtered closed Tomita modular forms

For a generally unbounded closed Tomita operator, Mathlib's bounded
`ContinuousLinearMap.adjoint` is not an applicable owner.  The native
operator-theoretic precursor of the modular operator `S⋆S` is instead its
positive sesquilinear form on the actual closed domain:

`q(x, y) = ⟪S y, S x⟫`.

The reversed arguments compensate for the conjugate-linearity of `S`, making
`q` conjugate-linear in its first argument and linear in its second argument.
This file bundles that form, proves positivity, and proves exact preservation
by every filtered GNS isometric transition.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaModularForm

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaClosedTransport

universe u

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)
variable
  (hclos :
    ∀ i, IsClosableTomitaCore (ω.state i))

/-- Every filtered completed-GNS transition, already known to be complex
linear and norm-preserving, bundled as a native complex linear isometry. -/
def filteredGNSLinearIsometry
    {i j : I} (hij : i ≤ j) :
    (ω.state i).functional.GNS →ₗᵢ[ℂ]
      (ω.state j).functional.GNS :=
  LinearIsometry.mk
    (filteredGNSMapCLM Stage sys ω hij).toLinearMap
    (fun x => by
      have h :=
        (filteredGNSMap_isometry
          Stage sys ω hij).dist_eq x 0
      have hzero :
          filteredGNSMap Stage sys ω hij 0 = 0 := by
        simpa only [filteredGNSMapCLM_apply] using
          (filteredGNSMapCLM
            Stage sys ω hij).map_zero
      calc
        ‖((filteredGNSMapCLM
            Stage sys ω hij).toLinearMap) x‖ =
            ‖filteredGNSMap Stage sys ω hij x‖ :=
          congrArg norm
            (filteredGNSMapCLM_apply
              Stage sys ω hij x)
        _ = dist
              (filteredGNSMap Stage sys ω hij x)
              (filteredGNSMap Stage sys ω hij 0) := by
            rw [hzero, dist_zero_right]
        _ = dist x 0 := h
        _ = ‖x‖ := dist_zero_right x)

@[simp] theorem filteredGNSLinearIsometry_apply
    {i j : I} (hij : i ≤ j)
    (x : (ω.state i).functional.GNS) :
    filteredGNSLinearIsometry Stage sys ω hij x =
      filteredGNSMap Stage sys ω hij x :=
  filteredGNSMapCLM_apply Stage sys ω hij x

/-- The positive closed-domain form associated to the closed Tomita operator.
It is the form-theoretic precursor of the generally unbounded modular operator
`S⋆S`. -/
def closedTomitaModularForm
    (i : I) :
    closedTomitaDomain (ω.state i) →ₛₗ[starRingEnd ℂ]
      closedTomitaDomain (ω.state i) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ
    (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y =>
      inner ℂ
        (closedTomitaOperator
          (ω.state i) (hclos i) y)
        (closedTomitaOperator
          (ω.state i) (hclos i) x))
    (by
      intro x₁ x₂ y
      simp only [map_add, inner_add_right])
    (by
      intro c x y
      change
        inner ℂ
            (closedTomitaOperator
              (ω.state i) (hclos i) y)
            (closedTomitaOperator
              (ω.state i) (hclos i) (c • x)) =
          (starRingEnd ℂ) c •
            inner ℂ
              (closedTomitaOperator
                (ω.state i) (hclos i) y)
              (closedTomitaOperator
                (ω.state i) (hclos i) x)
      rw [map_smulₛₗ, inner_smul_right]
      simp)
    (by
      intro x y₁ y₂
      simp only [map_add, inner_add_left])
    (by
      intro c x y
      change
        inner ℂ
            (closedTomitaOperator
              (ω.state i) (hclos i) (c • y))
            (closedTomitaOperator
              (ω.state i) (hclos i) x) =
          (RingHom.id ℂ) c •
            inner ℂ
              (closedTomitaOperator
                (ω.state i) (hclos i) y)
              (closedTomitaOperator
                (ω.state i) (hclos i) x)
      rw [map_smulₛₗ, inner_smul_left]
      simp)

@[simp] theorem closedTomitaModularForm_apply
    (i : I)
    (x y : closedTomitaDomain (ω.state i)) :
    closedTomitaModularForm Stage sys ω hclos i x y =
      inner ℂ
        (closedTomitaOperator
          (ω.state i) (hclos i) y)
        (closedTomitaOperator
          (ω.state i) (hclos i) x) :=
  rfl

/-- The diagonal of the modular form is real and nonnegative. -/
theorem closedTomitaModularForm_nonneg
    (i : I)
    (x : closedTomitaDomain (ω.state i)) :
    0 ≤
      Complex.re
        (closedTomitaModularForm
          Stage sys ω hclos i x x) := by
  rw [closedTomitaModularForm_apply]
  exact inner_self_nonneg (𝕜 := ℂ)

/-- Filtered transition maps preserve the closed Tomita modular form exactly.
This is the stagewise compatibility needed before descending the form through
the filtered categorical system. -/
theorem filteredClosedTomitaDomainMap_preserves_modularForm
    {i j : I} (hij : i ≤ j)
    (x y : closedTomitaDomain (ω.state i)) :
    closedTomitaModularForm Stage sys ω hclos j
        (filteredClosedTomitaDomainMap
          Stage sys ω hij x)
        (filteredClosedTomitaDomainMap
          Stage sys ω hij y) =
      closedTomitaModularForm Stage sys ω hclos i x y := by
  simp only [closedTomitaModularForm_apply]
  rw [← filteredGNSMap_intertwines_closedTomitaOperator
      Stage sys ω hij (hclos i) (hclos j) y]
  rw [← filteredGNSMap_intertwines_closedTomitaOperator
      Stage sys ω hij (hclos i) (hclos j) x]
  exact
    (by
      simpa only [filteredGNSLinearIsometry_apply] using
        (filteredGNSLinearIsometry
          Stage sys ω hij).inner_map_map
          (closedTomitaOperator (ω.state i) (hclos i) y)
          (closedTomitaOperator (ω.state i) (hclos i) x))

end CStarStateColimit.Native.FilteredGNSTomitaModularForm
