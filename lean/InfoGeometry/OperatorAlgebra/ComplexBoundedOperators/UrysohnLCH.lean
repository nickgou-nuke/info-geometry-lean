import Mathlib.Topology.UrysohnsLemma

/-!
# AFP Urysohn locally compact Hausdorff adapter

This file exposes Lean-native names for the locally compact Urysohn lemma used
in AFP's `Riesz_Representation/Urysohn_Locally_Compact_Hausdorff`.

The proof authority is mathlib's `Topology.UrysohnsLemma`, especially
`exists_continuousMap_one_of_isCompact_subset_isOpen`.
-/

noncomputable section

open Set

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace UrysohnLCH

variable {X : Type*} [TopologicalSpace X]

/--
Locally compact Urysohn bump function.

If `K` is compact and `K ⊆ U` with `U` open, there is a continuous real-valued
function equal to `1` on `K`, with compact topological support contained in
`U`, and with values in `[0, 1]`.
-/
theorem exists_bump_one_on_compact_support_subset_open
    [R1Space X] [LocallyCompactSpace X]
    {K U : Set X}
    (hK : IsCompact K)
    (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ f : C(X, ℝ),
      EqOn f 1 K ∧
      HasCompactSupport f ∧
      tsupport f ⊆ U ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  rcases exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU with
    ⟨f, hfK, hfc, hfU, hfrange⟩
  exact ⟨f, hfK, hfc, hfU, hfrange⟩

/--
Same bump function, also stated in the AFP style as vanishing off the open set.
-/
theorem exists_bump_one_on_compact_zero_off_open
    [R1Space X] [LocallyCompactSpace X]
    {K U : Set X}
    (hK : IsCompact K)
    (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ f : C(X, ℝ),
      EqOn f 1 K ∧
      EqOn f 0 Uᶜ ∧
      HasCompactSupport f ∧
      tsupport f ⊆ U ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  rcases exists_bump_one_on_compact_support_subset_open hK hU hKU with
    ⟨f, hfK, hfc, hfU, hfrange⟩
  refine ⟨f, hfK, ?_, hfc, hfU, hfrange⟩
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun hx' => hx (hfU hx'))

/--
Two-compact-set separation form.

If `K₀` and `K₁` are disjoint compact sets, there is a continuous compactly
supported function with values in `[0, 1]`, equal to `0` on `K₀` and `1` on
`K₁`.
-/
theorem exists_bump_zero_one_of_disjoint_compacts
    [R1Space X] [LocallyCompactSpace X]
    {K₀ K₁ : Set X}
    (hK₀ : IsCompact K₀)
    (hK₁ : IsCompact K₁)
    (hdisj : Disjoint K₀ K₁) :
    ∃ f : C(X, ℝ),
      EqOn f 0 K₀ ∧
      EqOn f 1 K₁ ∧
      HasCompactSupport f ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  have hK₀_closed : IsClosed K₀ := hK₀.isClosed
  have hK₁U : K₁ ⊆ K₀ᶜ := by
    intro x hx₁ hx₀
    exact Set.disjoint_left.mp hdisj hx₀ hx₁
  rcases exists_bump_one_on_compact_zero_off_open
      hK₁ hK₀_closed.isOpen_compl hK₁U with
    ⟨f, hfK₁, hfzero, hfc, _hfU, hfrange⟩
  exact ⟨f, hfzero, hfK₁, hfc, hfrange⟩

/--
Mathlib's closed-set Urysohn form for a compact set and a closed disjoint set.
-/
theorem exists_continuous_one_zero_of_compact_closed
    [RegularSpace X] [LocallyCompactSpace X]
    {K F : Set X}
    (hK : IsCompact K)
    (hF : IsClosed F)
    (hdisj : Disjoint K F) :
    ∃ f : C(X, ℝ),
      EqOn f 1 K ∧
      EqOn f 0 F ∧
      HasCompactSupport f ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  exists_continuous_one_zero_of_isCompact hK hF hdisj

end UrysohnLCH
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
