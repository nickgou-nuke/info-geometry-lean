import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathHomotopy

namespace InfoGeometry.Topology

/-!
# Endpoint-preserving reparametrizations of symbolic-latent paths

This owner isolates the reusable homotopy property for a continuous change of
the path parameter.  The parameter map is required to fix the two endpoints;
the straight-line interpolation in the interval then gives an explicit
endpoint-preserving homotopy.
-/

abbrev SymbolicLatentPathReparametrization :=
  {parameter : C(SymbolicPathDomain, SymbolicPathDomain) //
    parameter 0 = (0 : SymbolicPathDomain) ∧
    parameter 1 = (1 : SymbolicPathDomain)}

namespace SymbolicLatentPathReparametrization

abbrev parameter (R : SymbolicLatentPathReparametrization) := R.1
abbrev at_zero (R : SymbolicLatentPathReparametrization) :
    R.parameter 0 = (0 : SymbolicPathDomain) := R.2.1
abbrev at_one (R : SymbolicLatentPathReparametrization) :
    R.parameter 1 = (1 : SymbolicPathDomain) := R.2.2

end SymbolicLatentPathReparametrization

def reparametrizeSymbolicLatentPath
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) : SymbolicLatentPath X :=
  γ.comp R.parameter

theorem reparametrizeSymbolicLatentPath_start
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    (reparametrizeSymbolicLatentPath R γ).start = γ.start := by
  change γ (R.parameter 0) = γ 0
  rw [R.at_zero]

theorem reparametrizeSymbolicLatentPath_finish
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    (reparametrizeSymbolicLatentPath R γ).finish = γ.finish := by
  change γ (R.parameter 1) = γ 1
  rw [R.at_one]

theorem reparametrizeSymbolicLatentPath_endpoints
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    (reparametrizeSymbolicLatentPath R γ).endpoints = γ.endpoints := by
  ext <;>
    simp [SymbolicLatentPath.endpoints,
      reparametrizeSymbolicLatentPath_start,
      reparametrizeSymbolicLatentPath_finish]

noncomputable def linearReparametrizationParameter
    (R : SymbolicLatentPathReparametrization) :
    C(SymbolicPathSquare, SymbolicPathDomain) :=
  { toFun := fun p =>
      ⟨(1 - (p.1 : ℝ)) * (p.2 : ℝ) +
          (p.1 : ℝ) * (R.parameter p.2 : ℝ), by
        have hs0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.property.1
        have hs1 : (p.1 : ℝ) ≤ 1 := p.1.property.2
        have ht0 : (0 : ℝ) ≤ (p.2 : ℝ) := p.2.property.1
        have ht1 : (p.2 : ℝ) ≤ 1 := p.2.property.2
        have hr0 : (0 : ℝ) ≤ (R.parameter p.2 : ℝ) :=
          (R.parameter p.2).property.1
        have hr1 : (R.parameter p.2 : ℝ) ≤ 1 :=
          (R.parameter p.2).property.2
        have h₁ : 0 ≤ (1 - (p.1 : ℝ)) * (p.2 : ℝ) :=
          mul_nonneg (sub_nonneg.mpr hs1) ht0
        have h₂ : 0 ≤ (p.1 : ℝ) * (R.parameter p.2 : ℝ) :=
          mul_nonneg hs0 hr0
        have h₃ : (1 - (p.1 : ℝ)) * (p.2 : ℝ) ≤
            1 - (p.1 : ℝ) := by
          simpa using mul_le_mul_of_nonneg_left ht1 (sub_nonneg.mpr hs1)
        have h₄ : (p.1 : ℝ) * (R.parameter p.2 : ℝ) ≤
            (p.1 : ℝ) := by
          simpa using mul_le_mul_of_nonneg_left hr1 hs0
        constructor
        · exact h₁.trans (le_add_of_nonneg_right h₂)
        · nlinarith⟩
    continuous_toFun := by
      continuity }

theorem linearReparametrizationParameter_at_zero
    (R : SymbolicLatentPathReparametrization) (t : SymbolicPathDomain) :
    linearReparametrizationParameter R (0, t) = t := by
  apply Subtype.ext
  norm_num [linearReparametrizationParameter]

theorem linearReparametrizationParameter_at_one
    (R : SymbolicLatentPathReparametrization) (t : SymbolicPathDomain) :
    linearReparametrizationParameter R (1, t) = R.parameter t := by
  apply Subtype.ext
  norm_num [linearReparametrizationParameter]

theorem linearReparametrizationParameter_fixed_zero
    (R : SymbolicLatentPathReparametrization) (s : SymbolicPathDomain) :
    linearReparametrizationParameter R (s, 0) = (0 : SymbolicPathDomain) := by
  apply Subtype.ext
  change (1 - (s : ℝ)) * 0 + (s : ℝ) *
      (R.parameter 0 : ℝ) = 0
  rw [R.at_zero]
  norm_num

theorem linearReparametrizationParameter_fixed_one
    (R : SymbolicLatentPathReparametrization) (s : SymbolicPathDomain) :
    linearReparametrizationParameter R (s, 1) = (1 : SymbolicPathDomain) := by
  apply Subtype.ext
  change (1 - (s : ℝ)) * 1 + (s : ℝ) * (R.parameter 1 : ℝ) = 1
  rw [R.at_one]
  norm_num

noncomputable def reparametrizationHomotopy
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    SymbolicLatentPathHomotopy γ (reparametrizeSymbolicLatentPath R γ) where
  map := {
    toFun := fun p => γ (linearReparametrizationParameter R p)
    continuous_toFun := γ.continuous.comp
      (linearReparametrizationParameter R).continuous }
  at_start := by
    intro t
    change γ (linearReparametrizationParameter R (0, t)) = γ t
    rw [linearReparametrizationParameter_at_zero]
  at_finish := by
    intro t
    change γ (linearReparametrizationParameter R (1, t)) =
      γ (R.parameter t)
    rw [linearReparametrizationParameter_at_one]
  fixed_start := by
    intro s
    change γ (linearReparametrizationParameter R (s, 0)) = γ.start
    rw [linearReparametrizationParameter_fixed_zero]
    rfl
  fixed_finish := by
    intro s
    change γ (linearReparametrizationParameter R (s, 1)) = γ.finish
    rw [linearReparametrizationParameter_fixed_one]
    rfl

theorem reparametrizeSymbolicLatentPath_homotopic
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    SymbolicLatentPathHomotopic γ (reparametrizeSymbolicLatentPath R γ) :=
  ⟨reparametrizationHomotopy R γ⟩

end InfoGeometry.Topology
