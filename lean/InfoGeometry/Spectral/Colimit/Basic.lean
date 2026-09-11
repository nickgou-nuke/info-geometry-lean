import Mathlib.Algebra.Category.ModuleCat.Limits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Spectral.Colimit.NativeModuleColimit

/-!
# Native inclusions into the split Clifford direct limit

The colimit owner is `NativeModuleColimit.lean`, where the tower is presented
by `ModuleCat.directLimitCocone` and its `IsColimit` proof.  This file exposes
the concrete Mathlib direct-limit inclusions and their transition law.
-/

noncomputable section

namespace InfoGeometry.Spectral.Colimit

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordDirectLimit

/-! ## Native sequential diagrams and cocones -/

universe u v

/-- A sequential system is a genuine functor from the natural-number preorder. -/
abbrev SequentialDiagram (C : Type u) [Category.{v} C] :=
  ℕ ⥤ C

/-- A sequential cocone is Mathlib's categorical cocone. -/
abbrev SequentialCocone
    {C : Type u} [Category.{v} C]
    (F : SequentialDiagram C) :=
  Cocone F

/-- A map of sequential systems is a natural transformation. -/
abbrev SequentialMap
    {C : Type u} [Category.{v} C]
    (F G : SequentialDiagram C) :=
  F ⟶ G

/-- The canonical transition morphism between two ordered stages. -/
def bondMap
    {C : Type u} [Category.{v} C]
    (F : SequentialDiagram C)
    {m n : ℕ} (h : m ≤ n) :
    F.obj m ⟶ F.obj n :=
  F.map (homOfLE h)

/-- Bond maps on refl are identity morphisms. -/
@[simp]
theorem bondMap_refl
    {C : Type u} [Category.{v} C]
    (F : SequentialDiagram C) (n : ℕ) :
    bondMap F (le_refl n) = 𝟙 (F.obj n) := by
  simp [bondMap]

/-- Sequential transition maps compose by functoriality. -/
@[simp]
theorem bondMap_trans
    {C : Type u} [Category.{v} C]
    (F : SequentialDiagram C)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    bondMap F (hij.trans hjk) = bondMap F hij ≫ bondMap F hjk := by
  rw [bondMap, bondMap, bondMap, ← F.map_comp, homOfLE_comp]

@[simp]
theorem sequentialMap_naturality
    {C : Type u} [Category.{v} C]
    {F G : SequentialDiagram C}
    (α : SequentialMap F G)
    {m n : ℕ} (h : m ≤ n) :
    bondMap F h ≫ α.app n = α.app m ≫ bondMap G h := by
  simp [bondMap]

@[simp]
theorem sequentialCocone_compat
    {C : Type u} [Category.{v} C]
    {F : SequentialDiagram C}
    (K : SequentialCocone F)
    {m n : ℕ} (h : m ≤ n) :
    bondMap F h ≫ K.ι.app n = K.ι.app m := by
  simp [bondMap]

/-- Universal descent from a genuine sequential colimit cocone. -/
def sequentialColimitDesc
    {C : Type u} [Category.{v} C]
    {F : SequentialDiagram C}
    {K : SequentialCocone F}
    (hK : IsColimit K)
    (t : SequentialCocone F) :
    K.pt ⟶ t.pt :=
  hK.desc t

/-- Universal descent commutes with every stage injection. -/
theorem sequentialColimitDesc_fac
    {C : Type u} [Category.{v} C]
    {F : SequentialDiagram C}
    {K : SequentialCocone F}
    (hK : IsColimit K)
    (t : SequentialCocone F)
    (n : ℕ) :
    K.ι.app n ≫ sequentialColimitDesc hK t = t.ι.app n := by
  exact hK.fac t n

/-- The descended morphism is uniquely determined by its stage restrictions. -/
theorem sequentialColimitDesc_unique
    {C : Type u} [Category.{v} C]
    {F : SequentialDiagram C}
    {K : SequentialCocone F}
    (hK : IsColimit K)
    (t : SequentialCocone F)
    (f : K.pt ⟶ t.pt)
    (hf : ∀ n : ℕ, K.ι.app n ≫ f = t.ι.app n) :
    f = sequentialColimitDesc hK t := by
  simpa using hK.uniq t f hf

/-! ## Split Clifford stage inclusions -/

/-- The canonical inclusion of a finite split Clifford stage into the Mathlib
direct limit. -/
abbrev SplitCliffordInclusion (n : ℕ) :
    SplitClNNAlg n → SplitCliffordInfinity :=
  DirectLimit.Module.of ℝ ℕ SplitClNNAlg
    (fun m n h => splitCliffordMap m n h) n

@[simp]
theorem SplitCliffordInclusion_apply (n : ℕ) (x : SplitClNNAlg n) :
    SplitCliffordInclusion n x =
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x := by
  rfl

/-- The canonical split-Clifford one-step inclusion is exactly the specimen
`DirectLimit.Module.of` applied to the recursive transition map in the tower. -/
theorem SplitCliffordInclusion_step (n : ℕ) (x : SplitClNNAlg n) :
    SplitCliffordInclusion (n + 1) (splitCliffordStep n x) =
      SplitCliffordInclusion n x := by
  have hstep : splitCliffordStep n =
      splitCliffordMap n (n + 1) (Nat.le_succ n) := by
    rw [splitCliffordMap_succ n n (Nat.le_refl n)]
    simp
  calc
    SplitCliffordInclusion (n + 1) (splitCliffordStep n x) =
        DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h)
          (n + 1) ((splitCliffordStep n) x) := by rfl
    _ = DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h)
          (n + 1)
          ((splitCliffordMap n (n + 1) (Nat.le_succ n)) x) := by
          rw [← hstep]
    _ = DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) n x := by
          rw [DirectLimit.Module.of_f
            (R := ℝ) (ι := ℕ) (G := SplitClNNAlg)
            (f := fun m n h => splitCliffordMap m n h)
            (i := n) (j := n + 1) (hij := Nat.le_succ n)]
    _ = SplitCliffordInclusion n x := by rfl

end InfoGeometry.Spectral.Colimit
