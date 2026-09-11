import InfoGeometry.Canonical.Cl55WittFullLieClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Classical

/-!
# The orthogonal hierarchy inside the five-mode Witt--CAR representation

The five-mode spinor matrices contain two related but distinct Lie algebras.

* The quadratic lanes `g_{-2} ⊕ g_0 ⊕ g_{+2}` have dimension fingerprint
  `10 + 25 + 10 = 45`, matching the split type-`D₅` model `so(5,5)`.
* Adjoining the linear lanes `g_{-1} ⊕ g_{+1}` gives the full five-grade
  closure with fingerprint `10 + 5 + 25 + 5 + 10 = 55`, matching the split
  type-`B₅` model `so(6,5)`.

This file proves the internal quadratic Lie closure and the exact dimension
fingerprints.  It exposes Mathlib's canonical `typeD` and `typeB` targets, but
it deliberately does not claim a Lie equivalence before an explicit
intertwiner is constructed.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55WittOrthogonalHierarchy

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Canonical.Cl55WittFullLieClosure

/-- Mathlib's canonical split `D₅` matrix Lie algebra. -/
abbrev SplitD5Model := LieAlgebra.Orthogonal.typeD (Fin 5) ℝ

/-- Mathlib's canonical split `B₅` matrix Lie algebra. -/
abbrev SplitB5Model := LieAlgebra.Orthogonal.typeB (Fin 5) ℝ

/-- The three even/quadratic lanes. -/
inductive QuadraticLane
  | negTwo
  | zero
  | posTwo
  deriving DecidableEq, Fintype

/-- Existing concrete submodule for a quadratic lane. -/
def quadraticLaneSpace : QuadraticLane → Submodule ℝ (MatStage 5)
  | .negTwo => wittNegTwo
  | .zero => wittZero
  | .posTwo => wittPosTwo

/-- Union of the three quadratic homogeneous lanes. -/
def quadraticLaneSet : Set (MatStage 5) :=
  {X | ∃ lane, X ∈ quadraticLaneSpace lane}

/-- Internal linear carrier of the quadratic orthogonal core. -/
def quadraticCoreSpan : Submodule ℝ (MatStage 5) :=
  Submodule.span ℝ quadraticLaneSet

/-- Every quadratic lane lies in the quadratic core. -/
theorem quadraticLaneSpace_le_core (lane : QuadraticLane) :
    quadraticLaneSpace lane ≤ quadraticCoreSpan := by
  intro X hX
  exact Submodule.subset_span ⟨lane, hX⟩

/-- The quadratic core is contained in the full five-grade span. -/
theorem quadraticCoreSpan_le_full :
    quadraticCoreSpan ≤ wittFiveGradeSpan := by
  apply Submodule.span_le.mpr
  intro X hX
  rcases hX with ⟨lane, hLane⟩
  cases lane with
  | negTwo => exact laneSpace_le_span .negTwo hLane
  | zero => exact laneSpace_le_span .zero hLane
  | posTwo => exact laneSpace_le_span .posTwo hLane

/-- The nine quadratic-lane bracket routes close internally. -/
theorem quadratic_lane_bracket_mem_core
    {X Y : MatStage 5} {lane₁ lane₂ : QuadraticLane}
    (hX : X ∈ quadraticLaneSpace lane₁)
    (hY : Y ∈ quadraticLaneSpace lane₂) :
    bracket X Y ∈ quadraticCoreSpan := by
  have hn2 : wittNegTwo ≤ quadraticCoreSpan :=
    quadraticLaneSpace_le_core .negTwo
  have hz : wittZero ≤ quadraticCoreSpan :=
    quadraticLaneSpace_le_core .zero
  have hp2 : wittPosTwo ≤ quadraticCoreSpan :=
    quadraticLaneSpace_le_core .posTwo
  rcases lane₁ with (_ | _ | _) <;>
    rcases lane₂ with (_ | _ | _) <;>
    simp only [quadraticLaneSpace] at hX hY
  · rw [wittNegTwo_bracket_eq_zero_quadratic hX hY]
    exact quadraticCoreSpan.zero_mem
  · exact hn2 (wittNegTwo_bracket_mem_wittNegTwo hX hY)
  · exact hz (wittNegTwo_bracket_mem_wittZero hX hY)
  · exact hn2 (wittZero_bracket_mem_wittNegTwo hX hY)
  · exact hz (wittZero_bracket_mem_wittZero hX hY)
  · exact hp2 (wittZero_bracket_mem_wittPosTwo hX hY)
  · exact hz (wittPosTwo_bracket_mem_wittZero hX hY)
  · exact hp2 (wittPosTwo_bracket_mem_wittPosTwo hX hY)
  · rw [wittPosTwo_bracket_eq_zero_quadratic hX hY]
    exact quadraticCoreSpan.zero_mem

/-- Span induction upgrades the quadratic routing table to arbitrary elements. -/
theorem quadraticCoreSpan_bracket_mem
    {X Y : MatStage 5}
    (hX : X ∈ quadraticCoreSpan) (hY : Y ∈ quadraticCoreSpan) :
    bracket X Y ∈ quadraticCoreSpan := by
  refine Submodule.span_induction
    (p := fun X _ => bracket X Y ∈ quadraticCoreSpan)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    change ∃ lane, x ∈ quadraticLaneSpace lane at hx
    rcases hx with ⟨lane₁, hx₁⟩
    refine Submodule.span_induction
      (p := fun Y _ => bracket x Y ∈ quadraticCoreSpan)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      change ∃ lane, y ∈ quadraticLaneSpace lane at hy
      rcases hy with ⟨lane₂, hy₂⟩
      exact quadratic_lane_bracket_mem_core hx₁ hy₂
    · simp [bracket]
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [bracket_add_right]
      exact quadraticCoreSpan.add_mem hy₁ hy₂
    · intro c y _ hy
      rw [bracket_smul_right]
      exact quadraticCoreSpan.smul_mem c hy
  · simp [bracket]
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [bracket_add_left]
    exact quadraticCoreSpan.add_mem hx₁ hx₂
  · intro c x _ hx
    rw [bracket_smul_left]
    exact quadraticCoreSpan.smul_mem c hx

/-- The quadratic core as a native Mathlib Lie subalgebra. -/
def quadraticCoreLieSubalgebra : LieSubalgebra ℝ (MatStage 5) :=
  { quadraticCoreSpan with
    lie_mem' := by
      intro X Y hX hY
      change bracket X Y ∈ quadraticCoreSpan
      exact quadraticCoreSpan_bracket_mem hX hY }

/-- Native inclusion of the quadratic core into the full five-grade Lie algebra. -/
def quadraticCoreIncl :
    quadraticCoreLieSubalgebra →ₗ⁅ℝ⁆ wittFiveGradeLieSubalgebra where
  toFun X := ⟨X.1, quadraticCoreSpan_le_full X.2⟩
  map_add' X Y := rfl
  map_smul' c X := rfl
  map_lie' := by
    intro X Y
    apply Subtype.ext
    rfl

@[simp] theorem quadraticCoreIncl_apply
    (X : quadraticCoreLieSubalgebra) :
    (quadraticCoreIncl X : MatStage 5) = X := by
  change X.1 = X.1
  rfl

/-- Quadratic generators: pair annihilators, balanced mixed quadratics, and
pair creators. -/
def quadraticGenerators : Set (MatStage 5) :=
  (Set.range (fun ij : Fin 5 × Fin 5 =>
      annihilation ij.1 * annihilation ij.2) ∪
    Set.range (fun ij : Fin 5 × Fin 5 => E ij.1 ij.2)) ∪
  Set.range (fun ij : Fin 5 × Fin 5 =>
    creation ij.1 * creation ij.2)

/-- Lie algebra generated by all quadratic Witt words. -/
def quadraticGeneratorLieSpan : LieSubalgebra ℝ (MatStage 5) :=
  LieSubalgebra.lieSpan ℝ (MatStage 5) quadraticGenerators

/-- The quadratic core is generated by precisely the quadratic packets. -/
theorem quadraticCoreLieSubalgebra_eq_generatorLieSpan :
    quadraticCoreLieSubalgebra = quadraticGeneratorLieSpan := by
  apply le_antisymm
  · intro X hX
    change X ∈ quadraticCoreSpan at hX
    refine Submodule.span_induction
      (p := fun X _ => X ∈ quadraticGeneratorLieSpan)
      ?_ ?_ ?_ ?_ hX
    · intro x hx
      rcases hx with ⟨lane, hLane⟩
      cases lane with
      | negTwo =>
          change x ∈ wittNegTwo at hLane
          refine Submodule.span_induction
            (p := fun x _ => x ∈ quadraticGeneratorLieSpan)
            ?_ ?_ ?_ ?_ hLane
          · intro x hx
            rcases hx with ⟨ij, rfl⟩
            exact LieSubalgebra.subset_lieSpan
              (show annihilation ij.1 * annihilation ij.2 ∈
                quadraticGenerators by
                exact Or.inl (Or.inl (Set.mem_range_self ij)))
          · exact quadraticGeneratorLieSpan.zero_mem
          · intro x y _ _ hx hy
            exact quadraticGeneratorLieSpan.add_mem hx hy
          · intro c x _ hx
            exact quadraticGeneratorLieSpan.smul_mem c hx
      | zero =>
          change x ∈ wittZero at hLane
          refine Submodule.span_induction
            (p := fun x _ => x ∈ quadraticGeneratorLieSpan)
            ?_ ?_ ?_ ?_ hLane
          · intro x hx
            rcases hx with ⟨ij, rfl⟩
            exact LieSubalgebra.subset_lieSpan
              (show E ij.1 ij.2 ∈ quadraticGenerators by
                exact Or.inl (Or.inr (Set.mem_range_self ij)))
          · exact quadraticGeneratorLieSpan.zero_mem
          · intro x y _ _ hx hy
            exact quadraticGeneratorLieSpan.add_mem hx hy
          · intro c x _ hx
            exact quadraticGeneratorLieSpan.smul_mem c hx
      | posTwo =>
          change x ∈ wittPosTwo at hLane
          refine Submodule.span_induction
            (p := fun x _ => x ∈ quadraticGeneratorLieSpan)
            ?_ ?_ ?_ ?_ hLane
          · intro x hx
            rcases hx with ⟨ij, rfl⟩
            exact LieSubalgebra.subset_lieSpan
              (show creation ij.1 * creation ij.2 ∈
                quadraticGenerators by
                exact Or.inr (Set.mem_range_self ij))
          · exact quadraticGeneratorLieSpan.zero_mem
          · intro x y _ _ hx hy
            exact quadraticGeneratorLieSpan.add_mem hx hy
          · intro c x _ hx
            exact quadraticGeneratorLieSpan.smul_mem c hx
    · exact quadraticGeneratorLieSpan.zero_mem
    · intro x y _ _ hx hy
      exact quadraticGeneratorLieSpan.add_mem hx hy
    · intro c x _ hx
      exact quadraticGeneratorLieSpan.smul_mem c hx
  · unfold quadraticGeneratorLieSpan
    rw [LieSubalgebra.lieSpan_le]
    intro X hX
    change X ∈ quadraticGenerators at hX
    rcases hX with (hX | hX) | hX
    · rcases hX with ⟨ij, rfl⟩
      change annihilation ij.1 * annihilation ij.2 ∈ quadraticCoreSpan
      exact quadraticLaneSpace_le_core .negTwo
        (Submodule.subset_span (Set.mem_range_self ij))
    · rcases hX with ⟨ij, rfl⟩
      change E ij.1 ij.2 ∈ quadraticCoreSpan
      exact quadraticLaneSpace_le_core .zero
        (Submodule.subset_span (Set.mem_range_self ij))
    · rcases hX with ⟨ij, rfl⟩
      change creation ij.1 * creation ij.2 ∈ quadraticCoreSpan
      exact quadraticLaneSpace_le_core .posTwo
        (Submodule.subset_span (Set.mem_range_self ij))

/-! ## Exact dimension fingerprints -/

/-- Dimension of an ordinary orthogonal Lie algebra on an `n`-dimensional
vector space. -/
def orthogonalDimension (n : ℕ) : ℕ := n * (n - 1) / 2

@[simp] theorem orthogonalDimension_ten :
    orthogonalDimension 10 = 45 := by
  norm_num [orthogonalDimension]

@[simp] theorem orthogonalDimension_eleven :
    orthogonalDimension 11 = 55 := by
  norm_num [orthogonalDimension]

/-- Exact lane dimensions of the quadratic core. -/
theorem quadratic_lane_dimensions :
    Module.finrank ℝ wittNegTwo = 10 ∧
    Module.finrank ℝ wittZero = 25 ∧
    Module.finrank ℝ wittPosTwo = 10 := by
  exact ⟨wittNegTwo_finrank_eq_ten,
    wittZero_finrank_eq_twentyFive,
    wittPosTwo_finrank_eq_ten⟩

/-- Exact lane dimensions of the full five-grade extension. -/
theorem full_five_grade_lane_dimensions :
    Module.finrank ℝ wittNegTwo = 10 ∧
    Module.finrank ℝ wittNegOne = 5 ∧
    Module.finrank ℝ wittZero = 25 ∧
    Module.finrank ℝ wittPosOne = 5 ∧
    Module.finrank ℝ wittPosTwo = 10 := by
  exact ⟨wittNegTwo_finrank_eq_ten,
    wittNegOne_finrank_eq_five,
    wittZero_finrank_eq_twentyFive,
    wittPosOne_finrank_eq_five,
    wittPosTwo_finrank_eq_ten⟩

/-- The quadratic lanes have the split-`D₅` dimension fingerprint. -/
theorem quadratic_core_dimension_fingerprint :
    Module.finrank ℝ wittNegTwo + Module.finrank ℝ wittZero +
        Module.finrank ℝ wittPosTwo = 45 ∧
      orthogonalDimension 10 = 45 := by
  rw [wittNegTwo_finrank_eq_ten,
    wittZero_finrank_eq_twentyFive,
    wittPosTwo_finrank_eq_ten]
  norm_num [orthogonalDimension]

/-- The five lanes have the split-`B₅` dimension fingerprint. -/
theorem full_extension_dimension_fingerprint :
    Module.finrank ℝ wittNegTwo + Module.finrank ℝ wittNegOne +
        Module.finrank ℝ wittZero + Module.finrank ℝ wittPosOne +
        Module.finrank ℝ wittPosTwo = 55 ∧
      orthogonalDimension 11 = 55 := by
  rw [wittNegTwo_finrank_eq_ten,
    wittNegOne_finrank_eq_five,
    wittZero_finrank_eq_twentyFive,
    wittPosOne_finrank_eq_five,
    wittPosTwo_finrank_eq_ten]
  norm_num [orthogonalDimension]

/-- The two orthogonal fingerprints are numerically distinct. -/
theorem quadratic_core_ne_full_extension :
    orthogonalDimension 10 ≠ orthogonalDimension 11 := by
  norm_num [orthogonalDimension]

/-- Complete hierarchy packet.  The final clauses are dimension fingerprints,
not assertions of an unconstructed real-form equivalence. -/
theorem cl55_witt_orthogonal_hierarchy_packet :
    quadraticCoreLieSubalgebra ≤ wittFiveGradeLieSubalgebra ∧
    quadraticCoreLieSubalgebra = quadraticGeneratorLieSpan ∧
    (Module.finrank ℝ wittNegTwo + Module.finrank ℝ wittZero +
      Module.finrank ℝ wittPosTwo = 45) ∧
    (Module.finrank ℝ wittNegTwo + Module.finrank ℝ wittNegOne +
      Module.finrank ℝ wittZero + Module.finrank ℝ wittPosOne +
      Module.finrank ℝ wittPosTwo = 55) := by
  refine ⟨?_, quadraticCoreLieSubalgebra_eq_generatorLieSpan,
    quadratic_core_dimension_fingerprint.1,
    full_extension_dimension_fingerprint.1⟩
  intro X hX
  exact quadraticCoreSpan_le_full hX

end InfoGeometry.Canonical.Cl55WittOrthogonalHierarchy
