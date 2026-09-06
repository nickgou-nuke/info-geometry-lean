import proofs.GrothendieckGromovWittenYangBaxter
import proofs.NonIsoConf3QuadricD4Model

/-!
# Penrose spin-network tiling config for the non-isotropic configuration cooperad

This file implements finite incidence/tile bookkeeping, generator-degree bookkeeping, and the
formal Poincare-signature combinatorics of the proposed arity-three model.
-/

namespace PenroseSpinTilingConfig

/-- Five prototile colors for a Penrose-style incidence alphabet.  This is only
finite combinatorics, not a theorem about the Penrose tiling hull. -/
inductive TileColor where
  | thick | thin | star | boat | diamond
  deriving DecidableEq, Repr

instance : Fintype TileColor where
  elems := {TileColor.thick, TileColor.thin, TileColor.star, TileColor.boat, TileColor.diamond}
  complete := by
    intro x
    cases x <;> simp

/-- Finite oriented incidence between tile colors. -/
structure Incidence where
  source : TileColor
  target : TileColor
  deriving DecidableEq, Repr

/-- A finite multi-point tile is a point-label type together with an incidence
relation between labels. -/
structure MultiPointTile (ι : Type) where
  edge : ι → ι → Prop
  decidableEdge : DecidableRel edge

attribute [instance] MultiPointTile.decidableEdge

/-- The complete three-point incidence tile: every pair of distinct labels is an edge. -/
def complete3Tile : MultiPointTile (Fin 3) where
  edge i j := i ≠ j
  decidableEdge := inferInstance

/-- The complete three-point tile has the three unoriented edges of `K₃`. -/
inductive Edge3 where
  | e12 | e23 | e13
  deriving DecidableEq, Fintype, Repr

/-- The two generator types appearing in the proposed quadric-configuration
cohomology model: phase classes and flux classes. -/
inductive GenKind where
  | phase | flux
  deriving DecidableEq, Fintype, Repr

/-- A formal arity-three generator. -/
structure SpinTileGenerator where
  edge : Edge3
  kind : GenKind
  deriving DecidableEq, Fintype, Repr

/-- Degree of a proposed generator for even ambient dimension `D`. -/
def genDegree (D : ℕ) : GenKind → ℕ
  | GenKind.phase => 1
  | GenKind.flux => D - 1

@[simp] theorem genDegree_phase (D : ℕ) : genDegree D GenKind.phase = 1 := rfl
@[simp] theorem genDegree_flux (D : ℕ) : genDegree D GenKind.flux = D - 1 := rfl

/-- There are exactly six formal edge-generators: three phase and three flux. -/
theorem spinTileGenerator_card : Fintype.card SpinTileGenerator = 6 := by
  rw [Fintype.card_congr
    { toFun := fun g => (g.edge, g.kind)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := by intro g; cases g; rfl
      right_inv := by intro p; cases p; rfl }]
  rw [Fintype.card_prod]
  rfl

/-- Legacy reduced product-of-spheres signature: three degree-`1` exterior
classes and two degree-`D-1` exterior classes.

This records the earlier claimed Poincare polynomial
`(1+t)^3(1+t^(D-1))^2` only as finite generator bookkeeping.  The corrected
visible `D=4` quadric candidate has three alpha and three beta generators and
is recorded in `NonIsoConf3QuadricD4Model`. -/
structure Config3PoincareSignature where
  phaseGenerators : Fin 3 → Bool
  fluxGenerators : Fin 2 → Bool
  deriving DecidableEq, Fintype, Repr

/-- The legacy reduced formal signature has total dimension `2^5 = 32`. -/
theorem config3_signature_total_rank : Fintype.card Config3PoincareSignature = 32 := by
  rw [Fintype.card_congr
    { toFun := fun s => (s.phaseGenerators, s.fluxGenerators)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := by intro s; cases s; rfl
      right_inv := by intro p; cases p; rfl }]
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun]
  norm_num [Fintype.card_bool, Fintype.card_fin]

/-- Anchor from the corrected `D=4` quadric candidate: the alpha Arnold quotient
has rank `2` in degree two, and the first candidate table has total support
only below degree `12`. -/
theorem corrected_d4_rank_anchor :
    NonIsoConf3QuadricD4Model.candidateRank 0 = 1 ∧
    NonIsoConf3QuadricD4Model.candidateRank 1 = 3 ∧
    NonIsoConf3QuadricD4Model.candidateRank 2 = 2 ∧
    NonIsoConf3QuadricD4Model.candidateRank 12 = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A finite incidence-preserving map between multi-point tiles. -/
structure TileMap {ι κ : Type} (A : MultiPointTile ι) (B : MultiPointTile κ) where
  map : ι → κ
  preserves : ∀ {i j}, A.edge i j → B.edge (map i) (map j)

/-- Identity tile map. -/
def TileMap.id {ι : Type} (A : MultiPointTile ι) : TileMap A A where
  map := fun x => x
  preserves := by
    intro i j h
    simpa using h

/-- Composition of incidence-preserving tile maps. -/
def TileMap.comp {ι κ l : Type} {A : MultiPointTile ι} {B : MultiPointTile κ}
    {C : MultiPointTile l} (g : TileMap B C) (f : TileMap A B) : TileMap A C where
  map := fun x => g.map (f.map x)
  preserves := by intro i j h; exact g.preserves (f.preserves h)

@[simp] theorem TileMap.comp_apply {ι κ l : Type} {A : MultiPointTile ι}
    {B : MultiPointTile κ} {C : MultiPointTile l} (g : TileMap B C) (f : TileMap A B)
    (i : ι) : (g.comp f).map i = g.map (f.map i) := rfl

end PenroseSpinTilingConfig
