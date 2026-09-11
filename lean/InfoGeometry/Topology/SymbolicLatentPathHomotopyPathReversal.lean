import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientTopCat
import InfoGeometry.Topology.SymbolicLatentPathReversal

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Path-parameter reversal on symbolic-latent homotopies

This is distinct from reversal of the homotopy parameter.  It reverses each
path, swaps its endpoints, and still preserves the endpoint-relative homotopy
relation.
-/

def symbolicPathSquarePathReversal : C(SymbolicPathSquare, SymbolicPathSquare) :=
  { toFun := fun p => (p.1, symbolicPathReversalParameter p.2)
    continuous_toFun :=
      continuous_fst.prodMk
        (symbolicPathReversalParameter.continuous.comp continuous_snd) }

def reversePathParameterHomotopy
    {X : Type} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (H : SymbolicLatentPathHomotopy γ₀ γ₁) :
    SymbolicLatentPathHomotopy
      (reverseSymbolicLatentPath γ₀)
      (reverseSymbolicLatentPath γ₁) where
  map := H.map.comp symbolicPathSquarePathReversal
  at_start := by
    intro t
    change H.map (0, symbolicPathReversalParameter t) =
      γ₀ (symbolicPathReversalParameter t)
    rw [H.at_start]
  at_finish := by
    intro t
    change H.map (1, symbolicPathReversalParameter t) =
      γ₁ (symbolicPathReversalParameter t)
    rw [H.at_finish]
  fixed_start := by
    intro s
    simpa [symbolicPathSquarePathReversal,
      symbolicPathReversalParameter_zero, reverseSymbolicLatentPath_start] using
      H.fixed_finish s
  fixed_finish := by
    intro s
    simpa [symbolicPathSquarePathReversal,
      symbolicPathReversalParameter_one, reverseSymbolicLatentPath_finish] using
      H.fixed_start s

theorem reversePathParameterHomotopic
    {X : Type} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (h : SymbolicLatentPathHomotopic γ₀ γ₁) :
    SymbolicLatentPathHomotopic
      (reverseSymbolicLatentPath γ₀)
      (reverseSymbolicLatentPath γ₁) := by
  rcases h with ⟨H⟩
  exact ⟨reversePathParameterHomotopy H⟩

def symbolicPathReversalContinuousMap
    {X : Type} [TopologicalSpace X] :
    C(SymbolicLatentPath X, SymbolicLatentPath X) :=
  { toFun := reverseSymbolicLatentPath
    continuous_toFun := ContinuousMap.continuous_precomp
      symbolicPathReversalParameter }

def reversePathHomotopyQuotientMap
    {X : Type} [TopologicalSpace X] :
    SymbolicLatentPathHomotopyQuotient (X := X) →
      SymbolicLatentPathHomotopyQuotient (X := X) :=
  Quotient.lift (s := symbolicLatentPathHomotopySetoid (X := X))
    (fun γ => symbolicLatentPathHomotopyQuotientMap
      (reverseSymbolicLatentPath γ)) (by
    intro γ₀ γ₁ h
    exact Quotient.sound (reversePathParameterHomotopic
      (show SymbolicLatentPathHomotopic γ₀ γ₁ from h)))

theorem reversePathHomotopyQuotientMap_mk
    {X : Type} [TopologicalSpace X] (γ : SymbolicLatentPath X) :
    reversePathHomotopyQuotientMap (symbolicLatentPathHomotopyQuotientMap γ) =
      symbolicLatentPathHomotopyQuotientMap (reverseSymbolicLatentPath γ) := rfl

theorem continuous_reversePathHomotopyQuotientMap
    {X : Type} [TopologicalSpace X] :
    Continuous (reversePathHomotopyQuotientMap (X := X)) := by
  have hq : Continuous (symbolicLatentPathHomotopyQuotientMap (X := X)) :=
    @continuous_quotient_mk' (SymbolicLatentPath X) _
      (symbolicLatentPathHomotopySetoid (X := X))
  have hp : Continuous (reverseSymbolicLatentPath :
      SymbolicLatentPath X → SymbolicLatentPath X) :=
    ContinuousMap.continuous_precomp symbolicPathReversalParameter
  exact Continuous.quotient_lift (hq.comp hp) (by
    intro γ₀ γ₁ h
    exact @Quotient.sound (SymbolicLatentPath X)
      (symbolicLatentPathHomotopySetoid (X := X))
      (reverseSymbolicLatentPath γ₀) (reverseSymbolicLatentPath γ₁)
      (reversePathParameterHomotopic
        (show SymbolicLatentPathHomotopic γ₀ γ₁ from h)))

def reversePathHomotopyQuotientTopCatHom
    {X : Type} [TopologicalSpace X] :
    TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) ⟶
      TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) :=
  TopCat.ofHom
    { toFun := reversePathHomotopyQuotientMap
      continuous_toFun := continuous_reversePathHomotopyQuotientMap }

noncomputable def reversePathHomotopyQuotientHomeomorph
    {X : Type} [TopologicalSpace X] :
    SymbolicLatentPathHomotopyQuotient (X := X) ≃ₜ
      SymbolicLatentPathHomotopyQuotient (X := X) where
  toFun := reversePathHomotopyQuotientMap
  invFun := reversePathHomotopyQuotientMap
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro γ
    change reversePathHomotopyQuotientMap
      (symbolicLatentPathHomotopyQuotientMap
        (reverseSymbolicLatentPath γ)) =
      symbolicLatentPathHomotopyQuotientMap γ
    rw [reversePathHomotopyQuotientMap_mk,
      reverse_reverseSymbolicLatentPath]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro γ
    change reversePathHomotopyQuotientMap
      (symbolicLatentPathHomotopyQuotientMap
        (reverseSymbolicLatentPath γ)) =
      symbolicLatentPathHomotopyQuotientMap γ
    rw [reversePathHomotopyQuotientMap_mk,
      reverse_reverseSymbolicLatentPath]
  continuous_toFun := continuous_reversePathHomotopyQuotientMap
  continuous_invFun := continuous_reversePathHomotopyQuotientMap

theorem reversePathHomotopyQuotientHomeomorph_apply
    {X : Type} [TopologicalSpace X]
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    reversePathHomotopyQuotientHomeomorph q =
      reversePathHomotopyQuotientMap q :=
  rfl

theorem reversePathHomotopyQuotientTopCatHom_square
    {X : Type} [TopologicalSpace X] :
    reversePathHomotopyQuotientTopCatHom (X := X) ≫
        reversePathHomotopyQuotientTopCatHom (X := X) =
      𝟙 (TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X))) := by
  ext q
  refine Quotient.inductionOn q ?_
  intro γ
  change symbolicLatentPathHomotopyQuotientMap
      (reverseSymbolicLatentPath (reverseSymbolicLatentPath γ)) =
    symbolicLatentPathHomotopyQuotientMap γ
  rw [reverse_reverseSymbolicLatentPath]

end InfoGeometry.Topology
