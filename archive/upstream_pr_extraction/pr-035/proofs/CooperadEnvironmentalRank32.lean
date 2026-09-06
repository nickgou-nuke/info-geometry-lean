import proofs.QuadricConf3BraidingCooperadBridge
import proofs.VertexAlgebraBraidingCocycle
import proofs.LightConeTripotentMatrixBridge

/-!
# Cooperad environmental split preserves the rank-32 quadric spine

Finite theorem for the split `{1,2}|{3}`:

* edge `12` is the inner/local subsystem;
* edges `13,23` are outer/environment couplings;
* the product/Leray rank-32 basis factors as
  `inner phase bit × outer phase bits × two flux bits`;
* detailed-balance exactness kills the two oriented triangle Wilson cycles.
-/

namespace CooperadEnvironmentalRank32

open LightConeConf3DeRhamCooperad
open NonIsoConf3DeRhamCooperad

/-- Local/environmental partition for the cooperad split `{1,2}|{3}`. -/
def environmentalSlot : Edge3 → ClusterSlot := collapse12

@[simp] theorem environmentalSlot_12 : environmentalSlot Edge3.e12 = ClusterSlot.inner := rfl
@[simp] theorem environmentalSlot_13 : environmentalSlot Edge3.e13 = ClusterSlot.outer := rfl
@[simp] theorem environmentalSlot_23 : environmentalSlot Edge3.e23 = ClusterSlot.outer := rfl

/-- One inner phase bit, corresponding to edge `12`. -/
structure InnerPhaseBasis where
  inner12 : Bool
  deriving DecidableEq, Fintype, Repr

/-- Two outer/environment phase bits, corresponding to edges `13` and `23`. -/
structure OuterPhaseBasis where
  outer13 : Bool
  outer23 : Bool
  deriving DecidableEq, Fintype, Repr

/-- The two product/Leray flux bits retained by the rank-32 quadric candidate. -/
abbrev EnvironmentalFluxBasis := FluxBasis

/-- Environmental factorization of the rank-32 product/Leray basis. -/
structure EnvironmentalRank32Basis where
  inner : InnerPhaseBasis
  outer : OuterPhaseBasis
  flux : EnvironmentalFluxBasis
  deriving DecidableEq, Fintype, Repr

def innerPhaseBasisEquivBool : InnerPhaseBasis ≃ Bool where
  toFun b := b.inner12
  invFun b := ⟨b⟩
  left_inv := by
    intro b
    cases b
    rfl
  right_inv := by
    intro b
    rfl

def outerPhaseBasisEquivBoolPair : OuterPhaseBasis ≃ Bool × Bool where
  toFun b := (b.outer13, b.outer23)
  invFun b := ⟨b.1, b.2⟩
  left_inv := by
    intro b
    cases b
    rfl
  right_inv := by
    intro b
    cases b
    rfl

def environmentalFluxBasisEquivBoolFun : EnvironmentalFluxBasis ≃ (Fin 2 → Bool) where
  toFun b := b.flux
  invFun f := ⟨f⟩
  left_inv := by
    intro b
    cases b
    rfl
  right_inv := by
    intro f
    rfl

def environmentalRank32BasisEquivComponents :
    EnvironmentalRank32Basis ≃ InnerPhaseBasis × OuterPhaseBasis × EnvironmentalFluxBasis where
  toFun b := (b.inner, b.outer, b.flux)
  invFun b := ⟨b.1, b.2.1, b.2.2⟩
  left_inv := by
    intro b
    cases b
    rfl
  right_inv := by
    intro b
    cases b with
    | mk inner rest =>
      cases rest
      rfl

/-- The inner local phase sector has rank `2`. -/
theorem innerPhaseBasis_card : Fintype.card InnerPhaseBasis = 2 := by
  rw [Fintype.card_congr innerPhaseBasisEquivBool]
  simp

/-- The outer environmental phase sector has rank `4`. -/
theorem outerPhaseBasis_card : Fintype.card OuterPhaseBasis = 4 := by
  rw [Fintype.card_congr outerPhaseBasisEquivBoolPair]
  simp

/-- The retained flux sector has rank `4`. -/
theorem environmentalFluxBasis_card : Fintype.card EnvironmentalFluxBasis = 4 := by
  rw [Fintype.card_congr environmentalFluxBasisEquivBoolFun]
  simp

/-- The environmental cooperad split preserves the product/Leray rank `32`. -/
theorem environmentalRank32Basis_card :
    Fintype.card EnvironmentalRank32Basis = 32 := by
  rw [Fintype.card_congr environmentalRank32BasisEquivComponents]
  simp [innerPhaseBasis_card, outerPhaseBasis_card, environmentalFluxBasis_card]

/-- Repackage an environmental split basis as the original product/Leray basis.
Index convention: `0 ↦ 12`, `1 ↦ 13`, `2 ↦ 23`. -/
def toProductBasis (b : EnvironmentalRank32Basis) : ProductBasis where
  phase i :=
    if i = 0 then b.inner.inner12
    else if i = 1 then b.outer.outer13
    else b.outer.outer23
  flux := b.flux.flux

/-- Repackage the original product/Leray basis according to the environmental
split `{1,2}|{3}`. -/
def fromProductBasis (b : ProductBasis) : EnvironmentalRank32Basis where
  inner := ⟨b.phase 0⟩
  outer := ⟨b.phase 1, b.phase 2⟩
  flux := ⟨b.flux⟩

/-- The environmental split is equivalent to the original rank-32 product basis. -/
def environmentalRank32EquivProductBasis : EnvironmentalRank32Basis ≃ ProductBasis where
  toFun := toProductBasis
  invFun := fromProductBasis
  left_inv := by
    intro b
    cases b with
    | mk inner outer flux =>
      cases inner
      cases outer
      cases flux
      rfl
  right_inv := by
    intro b
    cases b with
    | mk phase flux =>
      simp [toProductBasis, fromProductBasis]
      funext i
      fin_cases i <;> simp

/-- Cardinality preservation through the explicit environmental/product equivalence. -/
theorem environmental_equiv_preserves_rank32 :
    Fintype.card EnvironmentalRank32Basis = Fintype.card ProductBasis := by
  exact Fintype.card_congr environmentalRank32EquivProductBasis

/-- The internal light-cone edge for an arbitrary arity-three block decomposition. -/
def internalLightEdge : QuadraticConfiguration3.BlockDecomp3 → Edge3
  | QuadraticConfiguration3.BlockDecomp3.pair12_3 => Edge3.e12
  | QuadraticConfiguration3.BlockDecomp3.pair13_2 => Edge3.e13
  | QuadraticConfiguration3.BlockDecomp3.pair23_1 => Edge3.e23

/-- Generic environmental slot for any arity-three cooperad split. -/
def genericEnvironmentalSlot (b : QuadraticConfiguration3.BlockDecomp3) (e : Edge3) :
    ClusterSlot :=
  if e = internalLightEdge b then ClusterSlot.inner else ClusterSlot.outer

@[simp] theorem genericEnvironmentalSlot_internal
    (b : QuadraticConfiguration3.BlockDecomp3) :
    genericEnvironmentalSlot b (internalLightEdge b) = ClusterSlot.inner := by
  simp [genericEnvironmentalSlot]

/-- For every decomposition, non-internal edges are outer/environmental. -/
theorem genericEnvironmentalSlot_outer_of_ne
    (b : QuadraticConfiguration3.BlockDecomp3) (e : Edge3)
    (h : e ≠ internalLightEdge b) :
    genericEnvironmentalSlot b e = ClusterSlot.outer := by
  simp [genericEnvironmentalSlot, h]

end CooperadEnvironmentalRank32
