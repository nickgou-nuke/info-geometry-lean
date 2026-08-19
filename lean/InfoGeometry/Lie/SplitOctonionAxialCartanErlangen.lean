import InfoGeometry.Lie.SplitOctonionErlangenInvariant
import InfoGeometry.Lie.SplitOctonionAxialCartanProjective
import InfoGeometry.Lie.SplitOctonionAxialCartanDerivation

/-!
# Erlangen packaging for the axial Cartan subgroup

The concrete traceless Cartan flow is inserted into the repository's native
quadratic-form isometry API.  The resulting statements preserve both the
polar form and the incidence relation; no identification with an abstract
named Lie group is used.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionAxialCartanFlow
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionErlangenInvariant

abbrev CZ := CanonicalZorn

/-- The traceless coordinate generator as an actual point of the native
fourteen-dimensional derivation Lie algebra. -/
noncomputable def axialCartanDerivation
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) :
    canonicalZornDerivations :=
  ⟨axialCartanEnd k, axialCartanEnd_isDerivation k hk⟩

@[simp] theorem axialCartanDerivation_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (X : CZ) :
    (axialCartanDerivation k hk :
      InfoGeometry.Lie.CanonicalZornDerivation.EndCZ) X = axialCartanEnd k X :=
  rfl

theorem axialCartanEnd_commute
    (k l : Fin 3 → ℝ) :
    axialCartanEnd k * axialCartanEnd l =
      axialCartanEnd l * axialCartanEnd k := by
  apply LinearMap.ext
  intro X
  ext i <;>
    simp [axialCartanEnd, Module.End.mul_apply] <;>
    ring

theorem axialCartanEnd_lie_bracket_zero
    (k l : Fin 3 → ℝ) :
    ⁅axialCartanEnd k, axialCartanEnd l⁆ = 0 := by
      rw [LieRing.of_associative_ring_bracket, axialCartanEnd_commute, sub_self]

theorem axialCartanEnd_add (k l : Fin 3 → ℝ) :
    axialCartanEnd (k + l) = axialCartanEnd k + axialCartanEnd l := by
  apply LinearMap.ext
  intro X
  ext i <;> simp [axialCartanEnd] <;> ring

theorem axialCartanEnd_smul (r : ℝ) (k : Fin 3 → ℝ) :
    axialCartanEnd (r • k) = r • axialCartanEnd k := by
  apply LinearMap.ext
  intro X
  ext i <;> simp [axialCartanEnd, Equiv.smul_def, ZornMatrix.coordEquiv] <;> ring

noncomputable def weightSum : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun k := ∑ i, k i
  map_add' k l := by simp [Finset.sum_add_distrib]
  map_smul' r k := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

abbrev TracelessWeight := weightSum.ker

noncomputable def tracelessWeightEquiv :
    (Fin 2 → ℝ) ≃ₗ[ℝ] TracelessWeight where
  toFun u :=
    ⟨![u 0, u 1, -(u 0 + u 1)], by
      change ∑ i, (![u 0, u 1, -(u 0 + u 1)] : Fin 3 → ℝ) i = 0
      simp [Fin.sum_univ_three]
      ring⟩
  invFun k := ![k.1 0, k.1 1]
  left_inv u := by
    funext i
    fin_cases i <;> rfl
  right_inv k := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · have hk : k.1 0 + k.1 1 + k.1 2 = 0 := by
        have hk0 := k.2
        change ∑ i, k.1 i = 0 at hk0
        simpa only [Fin.sum_univ_three] using hk0
      simp [Fin.sum_univ_three]
      linarith
  map_add' u v := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' r u := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> ring

theorem tracelessWeight_finrank :
    Module.finrank ℝ TracelessWeight = 2 := by
  rw [← (tracelessWeightEquiv).finrank_eq]
  exact Module.finrank_fin_fun ℝ

/-- The traceless Cartan parameter plane maps linearly into the native
derivation Lie algebra.  This keeps the parameterization bundled without
asserting a rank statement that has not been needed here. -/
noncomputable def axialCartanDerivationLinear :
    TracelessWeight →ₗ[ℝ] canonicalZornDerivations where
  toFun k := axialCartanDerivation k.1 k.2
  map_add' k l := by
    apply Subtype.ext
    change axialCartanEnd (k.1 + l.1) =
      axialCartanEnd k.1 + axialCartanEnd l.1
    exact axialCartanEnd_add k.1 l.1
  map_smul' r k := by
    apply Subtype.ext
    change axialCartanEnd (r • k.1) = r • axialCartanEnd k.1
    exact axialCartanEnd_smul r k.1

@[simp] theorem axialCartanDerivationLinear_apply (k : TracelessWeight) :
    axialCartanDerivationLinear k = axialCartanDerivation k.1 k.2 := rfl

theorem axialCartanDerivationLinear_lie_bracket_zero
    (k l : TracelessWeight) :
    ⁅axialCartanDerivationLinear k, axialCartanDerivationLinear l⁆ = 0 := by
  apply Subtype.ext
  change ⁅axialCartanEnd k.1, axialCartanEnd l.1⁆ = 0
  exact axialCartanEnd_lie_bracket_zero k.1 l.1

theorem axialCartanDerivationLinear_injective :
    Function.Injective axialCartanDerivationLinear := by
  intro k l h
  have h' : axialCartanEnd k.1 = axialCartanEnd l.1 := by
    exact congrArg Subtype.val h
  apply Subtype.ext
  funext i
  fin_cases i
  · have h0 := congrArg (fun D : InfoGeometry.Lie.CanonicalZornDerivation.EndCZ =>
      (D (chiralUpperBasis (R := ℝ) 0)).x 0) h'
    simpa [axialCartanEnd, chiralUpperBasis, ZornMatrix.mul_def,
      Equiv.smul_def, ZornMatrix.coordEquiv] using h0
  · have h1 := congrArg (fun D : InfoGeometry.Lie.CanonicalZornDerivation.EndCZ =>
      (D (chiralUpperBasis (R := ℝ) 1)).x 1) h'
    simpa [axialCartanEnd, chiralUpperBasis, ZornMatrix.mul_def,
      Equiv.smul_def, ZornMatrix.coordEquiv] using h1
  · have h2 := congrArg (fun D : InfoGeometry.Lie.CanonicalZornDerivation.EndCZ =>
      (D (chiralUpperBasis (R := ℝ) 2)).x 2) h'
    simpa [axialCartanEnd, chiralUpperBasis, ZornMatrix.mul_def,
      Equiv.smul_def, ZornMatrix.coordEquiv] using h2

theorem axialCartanDerivationLinear_range_finrank :
    Module.finrank ℝ (LinearMap.range axialCartanDerivationLinear) = 2 := by
  rw [LinearMap.finrank_range_of_inj axialCartanDerivationLinear_injective]
  exact tracelessWeight_finrank

/-! The faithful Cartan image is now packaged as the native Lie subalgebra
whose carrier is the range of the parameter map. -/
noncomputable def axialCartanLieSubalgebra :
    LieSubalgebra ℝ canonicalZornDerivations where
  carrier := LinearMap.range axialCartanDerivationLinear
  zero_mem' := by
    exact ⟨0, (axialCartanDerivationLinear).map_zero⟩
  add_mem' := by
    intro D E hD hE
    rcases hD with ⟨k, hk⟩
    rcases hE with ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    rw [map_add, hk, hl]
  smul_mem' := by
    intro r D hD
    rcases hD with ⟨k, hk⟩
    refine ⟨r • k, ?_⟩
    calc
      axialCartanDerivationLinear (r • k) =
          r • axialCartanDerivationLinear k :=
        (axialCartanDerivationLinear).map_smul r k
      _ = r • D := congrArg (fun z => r • z) hk
  lie_mem' := by
    intro D E hD hE
    rcases hD with ⟨k, hk⟩
    rcases hE with ⟨l, hl⟩
    refine ⟨0, ?_⟩
    rw [map_zero, ← hk, ← hl]
    exact (axialCartanDerivationLinear_lie_bracket_zero k l).symm

@[simp] theorem mem_axialCartanLieSubalgebra
    (D : canonicalZornDerivations) :
    D ∈ axialCartanLieSubalgebra ↔
      D ∈ LinearMap.range axialCartanDerivationLinear := Iff.rfl

/-- Every traceless coordinate generator lies in the faithful two-dimensional
Cartan subalgebra cut out by the native parameter map. -/
theorem axialCartanDerivation_mem_axialCartanLieSubalgebra
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) :
    axialCartanDerivation k hk ∈ axialCartanLieSubalgebra := by
  rw [mem_axialCartanLieSubalgebra]
  exact ⟨⟨k, hk⟩, rfl⟩

/-- The traceless weight plane, mapped into the faithful native Cartan
subalgebra as a genuine linear map. -/
noncomputable def axialCartanDerivationIntoLie :
    TracelessWeight →ₗ[ℝ] axialCartanLieSubalgebra where
  toFun k :=
    ⟨axialCartanDerivationLinear k, by
      exact (mem_axialCartanLieSubalgebra
        (axialCartanDerivationLinear k)).2 ⟨k, rfl⟩⟩
  map_add' k l := by
    apply Subtype.ext
    exact (axialCartanDerivationLinear).map_add k l
  map_smul' r k := by
    apply Subtype.ext
    exact (axialCartanDerivationLinear).map_smul r k

theorem axialCartanDerivationIntoLie_injective :
    Function.Injective axialCartanDerivationIntoLie := by
  intro k l h
  apply axialCartanDerivationLinear_injective
  exact congrArg Subtype.val h

theorem axialCartanDerivationIntoLie_surjective :
    Function.Surjective axialCartanDerivationIntoLie := by
  intro D
  rcases D.property with ⟨k, hk⟩
  exact ⟨k, by
    apply Subtype.ext
    exact hk⟩

/-- The traceless weight plane is linearly equivalent to the faithful native
Cartan Lie subalgebra.  This is obtained from the proved injective and
surjective parameter map, not from a dimension-only witness. -/
noncomputable def axialCartanLieEquiv :
    TracelessWeight ≃ₗ[ℝ] axialCartanLieSubalgebra :=
  LinearEquiv.ofBijective axialCartanDerivationIntoLie
    ⟨axialCartanDerivationIntoLie_injective,
      axialCartanDerivationIntoLie_surjective⟩

@[simp] theorem axialCartanLieEquiv_apply (k : TracelessWeight) :
    (axialCartanLieEquiv k : canonicalZornDerivations) =
      axialCartanDerivationLinear k :=
  rfl

theorem axialCartanLieSubalgebra_finrank :
    Module.finrank ℝ axialCartanLieSubalgebra = 2 := by
  exact axialCartanDerivationLinear_range_finrank

theorem axialCartanLieSubalgebra_bracket_zero
    (D E : axialCartanLieSubalgebra) : ⁅D, E⁆ = 0 := by
  apply Subtype.ext
  rcases D.property with ⟨k, hk⟩
  rcases E.property with ⟨l, hl⟩
  change ⁅D.1, E.1⁆ = 0
  rw [← hk, ← hl]
  exact axialCartanDerivationLinear_lie_bracket_zero k l

/-- The faithful Cartan image is abelian in the standard Mathlib sense. -/
theorem axialCartanLieSubalgebra_isLieAbelian :
    IsLieAbelian axialCartanLieSubalgebra where
  trivial D E := axialCartanLieSubalgebra_bracket_zero D E

noncomputable def axialCartanQuadraticIsometry
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    canonicalDetQuadratic.IsometryEquiv canonicalDetQuadratic :=
  realZornCompositionAut_quadratic_isometry
    (axialCartanCompositionAut k hk t)

@[simp] theorem axialCartanQuadraticIsometry_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ) :
    (axialCartanQuadraticIsometry k hk t) X =
      axialCartanFlow k t X :=
  rfl

@[simp] theorem axialCartanQuadraticIsometry_preserves_form
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : CZ) :
    canonicalDetQuadratic
        ((axialCartanQuadraticIsometry k hk t) X) =
      canonicalDetQuadratic X := by
  exact QuadraticMap.IsometryEquiv.map_app
    (axialCartanQuadraticIsometry k hk t) X

theorem axialCartanCompositionAut_add_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (s t : ℝ) (X : CZ) :
    ((axialCartanCompositionAut k hk (s + t) : CanonicalLinearAut) X) =
      ((axialCartanCompositionAut k hk s : CanonicalLinearAut)
        ((axialCartanCompositionAut k hk t : CanonicalLinearAut) X)) := by
  simp only [axialCartanCompositionAut_apply]
  exact axialCartanFlow_add k s t X

@[simp] theorem axialCartanCompositionAut_zero_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (X : CZ) :
    ((axialCartanCompositionAut k hk 0 : CanonicalLinearAut) X) = X := by
  simp only [axialCartanCompositionAut_apply]
  exact axialCartanFlow_zero k X

theorem axialCartanFlow_commute
    (k l : Fin 3 → ℝ) (s t : ℝ) (X : CZ) :
    axialCartanFlow k s (axialCartanFlow l t X) =
      axialCartanFlow l t (axialCartanFlow k s X) := by
  ext i <;> simp [axialCartanFlow] <;> ring

theorem axialCartanFlow_parameter_add
    (k l : Fin 3 → ℝ) (t : ℝ) (X : CZ) :
    axialCartanFlow (k + l) t X =
      axialCartanFlow k t (axialCartanFlow l t X) := by
  ext i <;> simp [axialCartanFlow]
  · rw [show t * (k i + l i) = t * k i + t * l i by ring,
      Real.exp_add]
    ring
  · rw [show -(t * (k i + l i)) = -(t * k i) + -(t * l i) by ring,
      Real.exp_add]
    ring

theorem axialCartanCompositionAut_commute
    (k l : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (hl : ∑ i, l i = 0)
    (s t : ℝ) (X : CZ) :
    ((axialCartanCompositionAut k hk s : CanonicalLinearAut)
      ((axialCartanCompositionAut l hl t : CanonicalLinearAut) X)) =
      ((axialCartanCompositionAut l hl t : CanonicalLinearAut)
        ((axialCartanCompositionAut k hk s : CanonicalLinearAut) X)) := by
  simp only [axialCartanCompositionAut_apply]
  exact axialCartanFlow_commute k l s t X

theorem axialCartanFlow_preserves_polar
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X Y : CZ) :
    polarZ (axialCartanFlow k t X) (axialCartanFlow k t Y) =
      polarZ X Y := by
  exact realZornCompositionAut_preserves_polar
    (axialCartanCompositionAut k hk t) X Y

theorem axialCartanFlow_preserves_incident
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X Y : CZ) :
    IncidentRep (axialCartanFlow k t X) (axialCartanFlow k t Y) ↔
      IncidentRep X Y := by
  exact realZornCompositionAut_preserves_incident
    (axialCartanCompositionAut k hk t) X Y

end InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
