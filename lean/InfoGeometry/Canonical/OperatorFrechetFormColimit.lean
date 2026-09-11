import InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.NativeToeplitzCuntzThree
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Concrete Cuntz stage diagram and exchange data

This module supplies the data needed by the existing categorical topological
colimit owners.  The stages are the supplied C⋆ realizations of a
`CuntzStarTower`; the transition maps are therefore not invented here.  The
exchange is the native stagewise modular flow, descended through
`modularFlowTopologicalColimitMap`.

No claim is made that an arbitrary Frechet-form space is such a colimit.  A
concrete tower, flow, transition naturality proof, and flow law remain the
explicit inputs below.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorFrechetFormColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow
open InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)
variable (Φ : CuntzStageModularFlowData Stage T)

/-- The actual TopCat diagram carried by the supplied Cuntz tower. -/
abbrev cuntzStageDiagram : ℕ ⥤ TopCat :=
  topologicalDiagram Stage (system Stage T)

/-- The actual topological colimit of the Cuntz stage diagram. -/
abbrev cuntzStageTopologicalColimit : TopCat :=
  topologicalColimit Stage (system Stage T)

/-! ## Exchange data -/

structure CuntzStageExchangeData where
  hmap_naturality :
    ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
      T.map hmn (Φ.flow m t a) =
        Φ.flow n t (T.map hmn a)
  hflow_add :
    ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
      Φ.flow n (t + s) a =
        Φ.flow n t (Φ.flow n s a)
  time : ℝ

namespace CuntzStageExchangeData

variable (E : CuntzStageExchangeData Stage T Φ)

/-- The stagewise exchange as a genuine natural transformation in `TopCat`. -/
def naturalTransformation :
    cuntzStageDiagram Stage T ⟶ cuntzStageDiagram Stage T :=
  modularFlowTopCatNatTrans Stage T Φ E.time

/-- The exchange descended through the native categorical colimit. -/
noncomputable def colimitMap :
    cuntzStageTopologicalColimit Stage T ⟶
      cuntzStageTopologicalColimit Stage T :=
  modularFlowTopologicalColimitMap Stage T Φ E.time

@[simp]
theorem colimitMap_stage (n : ℕ) (a : Stage n) :
    CuntzStageExchangeData.colimitMap
        (Stage := Stage) (T := T) (Φ := Φ) E
        (topologicalInjection Stage (system Stage T) n a) =
      topologicalInjection Stage (system Stage T) n
        (Φ.flow n E.time a) := by
  exact modularFlowTopologicalColimitMap_inclusion
    Stage T Φ E.time n a

theorem colimitMap_comp_neg :
    CuntzStageExchangeData.colimitMap
          (Stage := Stage) (T := T) (Φ := Φ) E ≫
        modularFlowTopologicalColimitMap Stage T Φ
          (-E.time) =
      𝟙 (cuntzStageTopologicalColimit Stage T) := by
  exact modularFlowTopologicalColimitMap_right_inverse
    Stage T Φ E.time

theorem neg_colimitMap_comp :
    modularFlowTopologicalColimitMap Stage T Φ
          (-E.time) ≫
        CuntzStageExchangeData.colimitMap
          (Stage := Stage) (T := T) (Φ := Φ) E =
      𝟙 (cuntzStageTopologicalColimit Stage T) := by
  exact modularFlowTopologicalColimitMap_left_inverse
    Stage T Φ E.time

theorem colimitMap_zero
    (hzero : E.time = 0) :
    CuntzStageExchangeData.colimitMap
        (Stage := Stage) (T := T) (Φ := Φ) E =
      𝟙 (cuntzStageTopologicalColimit Stage T) := by
  change modularFlowTopologicalColimitMap Stage T Φ
      E.time =
    𝟙 (cuntzStageTopologicalColimit Stage T)
  rw [hzero]
  exact modularFlowTopologicalColimitMap_zero
    Stage T Φ

end CuntzStageExchangeData

/-! ## Native ternary Toeplitz specialization

The algebraic Toeplitz carrier has no C⋆ norm in the repository, so this
specialization deliberately uses its discrete topology.  It supplies a
genuine `ℕ ⥤ TopCat` diagram and the native involutive star exchange, without
claiming that this constant diagram is an analytic Toeplitz completion.
-/

namespace NativeToeplitzCuntzThree

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Canonical.NativeToeplitzCuntzThree

abbrev Carrier := CuntzToeplitzAlg 3

local instance nativeDiscreteTopology : TopologicalSpace Carrier := ⊥
local instance nativeDiscrete : DiscreteTopology Carrier :=
  discreteTopology_bot Carrier

/-- The concrete constant stage diagram on the native ternary carrier. -/
def stageDiagram : ℕ ⥤ TopCat where
  obj _ := TopCat.of Carrier
  map _ := 𝟙 (TopCat.of Carrier)
  map_id _ := by simp
  map_comp _ _ := by simp

/-- The native algebraic `star`, viewed as a continuous TopCat map. -/
noncomputable def starHom :
    TopCat.of Carrier ⟶ TopCat.of Carrier :=
  TopCat.ofHom
    { toFun := star
      continuous_toFun := continuous_of_discreteTopology }

noncomputable def exchangeNat : stageDiagram ⟶ stageDiagram where
  app _ := starHom
  naturality := by
    intro i j f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl

theorem exchangeNat_involutive :
    exchangeNat ≫ exchangeNat = 𝟙 stageDiagram := by
  dsimp [exchangeNat, starHom, stageDiagram]
  ext n x
  change star (star (show Carrier from x)) = (show Carrier from x)
  exact star_star (show Carrier from x)

noncomputable def exchangeColimit :
    colimit stageDiagram ⟶ colimit stageDiagram :=
  colim.map exchangeNat

theorem exchangeColimit_stage (n : ℕ) :
    colimit.ι stageDiagram n ≫ exchangeColimit =
      starHom ≫ colimit.ι stageDiagram n := by
  exact colimit.ι_map exchangeNat n

theorem exchangeColimit_involutive :
    exchangeColimit ≫ exchangeColimit =
      𝟙 (colimit stageDiagram) := by
  apply colimit.hom_ext
  intro n
  have hstar : starHom ≫ starHom =
      𝟙 (TopCat.of Carrier) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change star (star x) = x
    exact star_star x
  calc
    colimit.ι stageDiagram n ≫ exchangeColimit ≫ exchangeColimit =
        (colimit.ι stageDiagram n ≫ exchangeColimit) ≫ exchangeColimit :=
      (Category.assoc _ _ _).symm
    _ = (starHom ≫ colimit.ι stageDiagram n) ≫ exchangeColimit := by
      rw [exchangeColimit_stage]
    _ = starHom ≫ (colimit.ι stageDiagram n ≫ exchangeColimit) :=
      Category.assoc _ _ _
    _ = starHom ≫ (starHom ≫ colimit.ι stageDiagram n) := by
      rw [exchangeColimit_stage]
    _ = (starHom ≫ starHom) ≫ colimit.ι stageDiagram n := by
      rw [Category.assoc]
    _ = colimit.ι stageDiagram n := by rw [hstar, Category.id_comp]
    _ = colimit.ι stageDiagram n ≫ 𝟙 (colimit stageDiagram) := by simp

end NativeToeplitzCuntzThree

end InfoGeometry.Canonical.OperatorFrechetFormColimit
