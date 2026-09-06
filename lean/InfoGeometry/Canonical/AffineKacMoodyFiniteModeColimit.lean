import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import InfoGeometry.External.Virasoro.AffineKacMoody

/-!
# Finite-mode filtered colimit for affine Kac--Moody currents

The external affine Kac--Moody owner defines the full loop-algebra central
extension and its current generators.  This file adds the missing categorical
finite-mode filtration.

At cutoff `N`, the stage is the linear span of the central generator and all
current generators `J_n(x)` with `Int.natAbs n <= N`.  The stages are nested,
so they form a functor `ℕ ⥤ ModuleCat 𝕜`.  Its categorical colimit has a
canonical comparison map to the full affine Kac--Moody carrier.

The present owner proves that every affine current generator and the central
generator have canonical representatives in this colimit and that the
comparison map recovers the native Kac--Moody bracket.  It deliberately does
not claim that the `ModuleCat` colimit itself carries a transported Lie bracket;
that requires a separate compatible-bracket construction because the bracket
of two cutoff-`N` currents can live at a larger cutoff.
-/

noncomputable section

namespace InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

open CategoryTheory CategoryTheory.Limits
open VirasoroProject

universe u
variable {𝕜 : Type u} [Field 𝕜] [CharZero 𝕜]
variable {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
variable (Φ : LinearMap.BilinForm 𝕜 𝓰)
variable (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)

abbrev KM : Type u :=
  AffineKacMoody 𝕜 𝓰 Φ hΦ hΦs

/-- Generating set at symmetric mode cutoff `N`: the central line together
with all current insertions whose integer mode has absolute value at most `N`. -/
def affineFiniteModeGenerators (N : ℕ) : Set (KM Φ hΦ hΦs) :=
  {X | X = affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs ∨
    ∃ n : ℤ, ∃ x : 𝓰,
      Int.natAbs n ≤ N ∧
        X = affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n x}

/-- Linear finite-mode stage. -/
def affineFiniteModeStage (N : ℕ) : Submodule 𝕜 (KM Φ hΦ hΦs) :=
  Submodule.span 𝕜 (affineFiniteModeGenerators Φ hΦ hΦs N)

/-- The affine central generator belongs to every finite-mode stage. -/
theorem affineCentralGen_mem_stage (N : ℕ) :
    affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs ∈
      affineFiniteModeStage Φ hΦ hΦs N := by
  apply Submodule.subset_span
  exact Or.inl rfl

/-- A current generator belongs to every stage whose cutoff contains its mode. -/
theorem affineCurrentGen_mem_stage
    (N : ℕ) (n : ℤ) (x : 𝓰) (hn : Int.natAbs n ≤ N) :
    affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n x ∈
      affineFiniteModeStage Φ hΦ hΦs N := by
  apply Submodule.subset_span
  exact Or.inr ⟨n, x, hn, rfl⟩

/-- Monotonicity of the finite-mode stages. -/
theorem affineFiniteModeStage_mono {N M : ℕ} (hNM : N ≤ M) :
    affineFiniteModeStage Φ hΦ hΦs N ≤
      affineFiniteModeStage Φ hΦ hΦs M := by
  apply Submodule.span_mono
  intro X hX
  rcases hX with hX | hX
  · exact Or.inl hX
  · rcases hX with ⟨n, x, hn, rfl⟩
    exact Or.inr ⟨n, x, hn.trans hNM, rfl⟩

/-- The cutoff stages form a genuine filtered diagram in `ModuleCat`. -/
noncomputable def affineFiniteModeDiagram : ℕ ⥤ ModuleCat 𝕜 where
  obj N := ModuleCat.of 𝕜 (affineFiniteModeStage Φ hΦ hΦs N)
  map f := ModuleCat.ofHom <|
    Submodule.inclusion (affineFiniteModeStage_mono Φ hΦ hΦs (leOfHom f))
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    rfl

/-- Canonical cocone from the finite-mode stages into the full affine
Kac--Moody central extension. -/
noncomputable def affineFiniteModeCocone :
    Cocone (affineFiniteModeDiagram Φ hΦ hΦs) where
  pt := ModuleCat.of 𝕜 (KM Φ hΦ hΦs)
  ι :=
    { app := fun N => ModuleCat.ofHom (Submodule.subtype _)
      naturality := by
        intro N M f
        ext X
        rfl }

/-- Categorical finite-mode current colimit. -/
abbrev affineFiniteModeColimit : ModuleCat 𝕜 :=
  colimit (affineFiniteModeDiagram Φ hΦ hΦs)

/-- Comparison map from the categorical colimit to the native full affine
Kac--Moody carrier. -/
noncomputable def affineFiniteModeColimitMap :
    affineFiniteModeColimit Φ hΦ hΦs ⟶ ModuleCat.of 𝕜 (KM Φ hΦ hΦs) :=
  colimit.desc _ (affineFiniteModeCocone Φ hΦ hΦs)

/-- Stage law for the comparison map. -/
theorem affineFiniteModeColimitMap_stage (N : ℕ) :
    colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N ≫
        affineFiniteModeColimitMap Φ hΦ hΦs =
      (affineFiniteModeCocone Φ hΦ hΦs).ι.app N := by
  exact colimit.ι_desc _ _

/-- Canonical colimit representative of the affine current `J_n(x)`. -/
noncomputable def affineCurrentColimitMode (n : ℤ) (x : 𝓰) :
    (affineFiniteModeColimit Φ hΦ hΦs : Type _) :=
  let N := Int.natAbs n
  let X : affineFiniteModeStage Φ hΦ hΦs N :=
    ⟨affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n x,
      affineCurrentGen_mem_stage Φ hΦ hΦs N n x le_rfl⟩
  (colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N).hom X

/-- The categorical current representative maps to the native affine current. -/
theorem affineFiniteModeColimitMap_current (n : ℤ) (x : 𝓰) :
    (affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs n x) =
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n x := by
  let N := Int.natAbs n
  let X : affineFiniteModeStage Φ hΦ hΦs N :=
    ⟨affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n x,
      affineCurrentGen_mem_stage Φ hΦ hΦs N n x le_rfl⟩
  change (affineFiniteModeColimitMap Φ hΦ hΦs).hom
      ((colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N).hom X) = X.1
  have hs := affineFiniteModeColimitMap_stage Φ hΦ hΦs N
  exact congrArg (fun f => f.hom X) hs

/-- Canonical colimit representative of the central Kac--Moody generator. -/
noncomputable def affineCentralColimitMode :
    (affineFiniteModeColimit Φ hΦ hΦs : Type _) :=
  let X : affineFiniteModeStage Φ hΦ hΦs 0 :=
    ⟨affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs,
      affineCentralGen_mem_stage Φ hΦ hΦs 0⟩
  (colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) 0).hom X

/-- The categorical central representative maps to the native central line. -/
theorem affineFiniteModeColimitMap_central :
    (affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCentralColimitMode Φ hΦ hΦs) =
      affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs := by
  let X : affineFiniteModeStage Φ hΦ hΦs 0 :=
    ⟨affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs,
      affineCentralGen_mem_stage Φ hΦ hΦs 0⟩
  change (affineFiniteModeColimitMap Φ hΦ hΦs).hom
      ((colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) 0).hom X) = X.1
  have hs := affineFiniteModeColimitMap_stage Φ hΦ hΦs 0
  exact congrArg (fun f => f.hom X) hs

/-- After applying the comparison map, two categorical finite-mode current
representatives obey the native affine Kac--Moody bracket with its central
residue cocycle. -/
theorem affineCurrentColimit_bracket_readout
    (m n : ℤ) (x y : 𝓰) :
    ⁅(affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs m x),
      (affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs n y)⁆ =
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs
          (m + n) (⁅x, y⁆ : 𝓰)
        + (if m + n = 0
            then ((m : 𝕜) * Φ x y) •
              affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs
            else 0) := by
  rw [affineFiniteModeColimitMap_current,
    affineFiniteModeColimitMap_current]
  exact affineCurrentGen_bracket (𝕜 := 𝕜) (𝓰 := 𝓰)
    Φ hΦ hΦs m n x y

/-- Every individual current and the central line are visibly generated at a
finite cutoff in the categorical diagram. -/
theorem affine_current_generator_colimit_packet (n : ℤ) (x : 𝓰) :
    (affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCurrentColimitMode Φ hΦ hΦs n x) =
      affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n x
    ∧
    (affineFiniteModeColimitMap Φ hΦ hΦs).hom
        (affineCentralColimitMode Φ hΦ hΦs) =
      affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs := by
  exact ⟨affineFiniteModeColimitMap_current Φ hΦ hΦs n x,
    affineFiniteModeColimitMap_central Φ hΦ hΦs⟩

end InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit
