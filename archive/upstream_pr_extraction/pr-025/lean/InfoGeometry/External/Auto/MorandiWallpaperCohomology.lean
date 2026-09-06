import Mathlib.Tactic

/-!
# Morandi wallpaper-pattern classification: cohomology digest

Formal Lean digest of Patrick J. Morandi's
*The Classification of Wallpaper Patterns: From Group Cohomology to Escher's
Tessellations*.

The core facts recorded here are the ones used downstream by the paperwall/glide
formalization:

* wallpaper groups fit into extensions `1 → T → G → G₀ → 1`, with
  `T ≅ ℤ²` and point group `G₀` finite;
* the crystallographic restriction gives rotations of order `1,2,3,4,6`, hence
  point groups `Cₙ` or `Dₙ` for those `n`;
* for the 13 lattice-action cases in Morandi Table 4.1, the `H²(G₀;T)`
  cardinalities sum to `18` extension classes;
* exactly one extension collision collapses the count to `17` wallpaper groups;
* the group-extension product is associative precisely because of the 2-cocycle
  condition.
-/

noncomputable section

namespace MorandiWallpaperCohomology

/-! ## 1. Crystallographic restriction and point-group bookkeeping -/

/-- Allowed finite rotation orders for a rank-two lattice. -/
def allowedRotationOrders : List ℕ := [1, 2, 3, 4, 6]

/-- The crystallographic restriction list has five allowed orders. -/
theorem allowedRotationOrders_length : allowedRotationOrders.length = 5 := by
  simp [allowedRotationOrders]

/-- Point groups are cyclic or dihedral with allowed orders. -/
inductive PointKind where
  | cyclic
  | dihedral
  deriving DecidableEq, Repr

/-- A point-group type is a kind plus an allowed order. -/
structure PointGroupType where
  kind : PointKind
  order : ℕ
  allowed : order ∈ allowedRotationOrders

/-- The ten abstract point-group families `Cₙ,Dₙ`, `n∈{1,2,3,4,6}`. -/
def pointGroupTypeCount : ℕ := 2 * allowedRotationOrders.length

/-- Morandi Theorem 3.4 count: ten possible point-group types. -/
theorem pointGroupTypeCount_eq_ten : pointGroupTypeCount = 10 := by
  simp [pointGroupTypeCount, allowedRotationOrders]

/-! ## 2. Morandi Table 4.1: H² cardinalities -/

/-- The 13 lattice-action cases appearing in Morandi's cohomology table. -/
inductive LatticeActionCase where
  | C1 | C2 | C3 | C4 | C6
  | D1p | D1c | D2p | D2c | D3l | D3s | D4 | D6
  deriving DecidableEq, Repr

/-- Cardinality of `H²(G₀;T)` for each action case, from Morandi Table 4.1. -/
def H2Card : LatticeActionCase → ℕ
  | .C1 => 1
  | .C2 => 1
  | .C3 => 1
  | .C4 => 1
  | .C6 => 1
  | .D1p => 2
  | .D1c => 1
  | .D2p => 4
  | .D2c => 1
  | .D3l => 1
  | .D3s => 1
  | .D4 => 2
  | .D6 => 1

/-- Explicit list of the 13 cases. -/
def allActionCases : List LatticeActionCase :=
  [.C1, .C2, .C3, .C4, .C6, .D1p, .D1c, .D2p, .D2c, .D3l, .D3s, .D4, .D6]

/-- There are 13 action cases after refining point groups by lattice type. -/
theorem actionCase_count : allActionCases.length = 13 := by
  simp [allActionCases]

/-- Total number of cohomological extension classes in Table 4.1. -/
def totalExtensionClasses : ℕ := (allActionCases.map H2Card).sum

/-- Morandi Table 4.1 totals 18 extensions. -/
theorem totalExtensionClasses_eq_18 : totalExtensionClasses = 18 := by
  simp [totalExtensionClasses, allActionCases, H2Card]

/-- One collision of inequivalent extensions gives the classical 17 wallpaper groups. -/
def morandiWallpaperCount : ℕ := totalExtensionClasses - 1

/-- The final wallpaper-group count is 17. -/
theorem morandiWallpaperCount_eq_17 : morandiWallpaperCount = 17 := by
  simp [morandiWallpaperCount, totalExtensionClasses_eq_18]

/-- Standard international notation for the 17 wallpaper groups. -/
def wallpaperNames : List String :=
  ["p1", "p2", "pm", "pg", "cm", "pmm", "pmg", "pgg", "cmm",
   "p4", "p4m", "p4g", "p3", "p3m1", "p31m", "p6", "p6m"]

/-- The standard list has length 17. -/
theorem wallpaperNames_length : wallpaperNames.length = 17 := by
  simp [wallpaperNames]

/-! ## 3. Group extensions from 2-cocycles -/

section CocycleExtension

variable {G T : Type*} [Group G] [AddCommGroup T] [DistribMulAction G T]

/-- Normalized 2-cocycle condition in additive notation. -/
def IsTwoCocycle (c : G → G → T) : Prop :=
  ∀ g h k : G, g • c h k + c g (h * k) = c g h + c (g * h) k

/-- The first coordinate of Morandi's extension product. -/
def extensionFirst (c : G → G → T) (x y : T × G) : T :=
  x.1 + x.2 • y.1 + c x.2 y.2

/-- Morandi's extension product on the set `T × G₀`. -/
def extensionMul (c : G → G → T) (x y : T × G) : T × G :=
  (extensionFirst c x y, x.2 * y.2)

/-- Neutral element for the extension product when the cocycle is normalized at the identity. -/
def extensionOne : T × G := (0, 1)

/-- Left identity for Morandi's extension product under normalized cocycle condition. -/
theorem extensionMul_one_left (c : G → G → T) (h1 : ∀ g : G, c 1 g = 0)
    (x : T × G) :
    extensionMul c extensionOne x = x := by
  cases x with
  | mk sx gx =>
    ext
    · simp [extensionMul, extensionFirst, extensionOne, h1]
    · simp [extensionMul, extensionOne]

/-- Right identity for Morandi's extension product under normalized cocycle condition. -/
theorem extensionMul_one_right (c : G → G → T) (h1 : ∀ g : G, c g 1 = 0)
    (x : T × G) :
    extensionMul c x extensionOne = x := by
  cases x with
  | mk sx gx =>
    ext
    · simp [extensionMul, extensionFirst, extensionOne, h1]
    · simp [extensionMul, extensionOne]

/-- The 2-cocycle equation is exactly associativity of the extension product. -/
theorem extensionMul_assoc_of_cocycle (c : G → G → T) (hc : IsTwoCocycle c)
    (x y z : T × G) :
    extensionMul c (extensionMul c x y) z = extensionMul c x (extensionMul c y z) := by
  cases x with
  | mk sx gx =>
  cases y with
  | mk sy gy =>
  cases z with
  | mk sz gz =>
    ext
    · simp [extensionMul, extensionFirst, mul_smul, add_assoc]
      rw [hc gx gy gz]
      abel
    · simp [extensionMul, mul_assoc]

end CocycleExtension

end MorandiWallpaperCohomology
