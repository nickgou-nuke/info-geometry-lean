import Mathlib
import InfoGeometry.Canonical.IntegralChiralCliffordOrder

namespace InfoGeometry.Canonical

/-!
# Three coordinate chiral sectors

This file formalizes the convention-independent linear layer.  The carrier is
the named integral coordinate module; its split-octonion multiplication is
intentionally deferred to a separate owner.  The identification of this
coordinate module with the previously defined parity order is also a separate
strengthening theorem.
-/

inductive IntegralSplitBasis
  | one | l | i | il | j | jl | k | kl
  deriving DecidableEq, Fintype

abbrev StandardIntegralSplitOctonion := IntegralSplitBasis → ℤ

def splitBasisVector (b : IntegralSplitBasis) :
    StandardIntegralSplitOctonion := Pi.single b 1

def oneOct := splitBasisVector .one
def lOct := splitBasisVector .l
def iOct := splitBasisVector .i
def ilOct := splitBasisVector .il
def jOct := splitBasisVector .j
def jlOct := splitBasisVector .jl
def kOct := splitBasisVector .k
def klOct := splitBasisVector .kl

abbrev ChiralOrderCoordinates := Fin 4 → ℤ

def redCoordinateEmbedding :
    ChiralOrderCoordinates →ₗ[ℤ] StandardIntegralSplitOctonion where
  toFun x := fun b => match b with
    | .one => x 0
    | .l => x 1
    | .i => x 2
    | .il => x 3
    | .j | .jl | .k | .kl => 0
  map_add' := by
    intro x y
    funext b
    cases b <;> simp [Pi.add_apply]
  map_smul' := by
    intro a x
    funext b
    cases b <;> simp [Pi.smul_apply]

def greenCoordinateEmbedding :
    ChiralOrderCoordinates →ₗ[ℤ] StandardIntegralSplitOctonion where
  toFun x := fun b => match b with
    | .one => x 0
    | .l => x 1
    | .j => x 2
    | .jl => x 3
    | .i | .il | .k | .kl => 0
  map_add' := by
    intro x y
    funext b
    cases b <;> simp [Pi.add_apply]
  map_smul' := by
    intro a x
    funext b
    cases b <;> simp [Pi.smul_apply]

def blueCoordinateEmbedding :
    ChiralOrderCoordinates →ₗ[ℤ] StandardIntegralSplitOctonion where
  toFun x := fun b => match b with
    | .one => x 0
    | .l => x 1
    | .k => x 2
    | .kl => x 3
    | .i | .il | .j | .jl => 0
  map_add' := by
    intro x y
    funext b
    cases b <;> simp [Pi.add_apply]
  map_smul' := by
    intro a x
    funext b
    cases b <;> simp [Pi.smul_apply]

theorem redCoordinateEmbedding_injective :
    Function.Injective redCoordinateEmbedding := by
  intro x y h
  funext n
  fin_cases n
  · simpa [redCoordinateEmbedding] using congrFun h .one
  · simpa [redCoordinateEmbedding] using congrFun h .l
  · simpa [redCoordinateEmbedding] using congrFun h .i
  · simpa [redCoordinateEmbedding] using congrFun h .il

theorem greenCoordinateEmbedding_injective :
    Function.Injective greenCoordinateEmbedding := by
  intro x y h
  funext n
  fin_cases n
  · simpa [greenCoordinateEmbedding] using congrFun h .one
  · simpa [greenCoordinateEmbedding] using congrFun h .l
  · simpa [greenCoordinateEmbedding] using congrFun h .j
  · simpa [greenCoordinateEmbedding] using congrFun h .jl

theorem blueCoordinateEmbedding_injective :
    Function.Injective blueCoordinateEmbedding := by
  intro x y h
  funext n
  fin_cases n
  · simpa [blueCoordinateEmbedding] using congrFun h .one
  · simpa [blueCoordinateEmbedding] using congrFun h .l
  · simpa [blueCoordinateEmbedding] using congrFun h .k
  · simpa [blueCoordinateEmbedding] using congrFun h .kl

def redIntegralSector :
    Submodule ℤ StandardIntegralSplitOctonion where
  carrier := {x |
    x .j = 0 ∧ x .jl = 0 ∧ x .k = 0 ∧ x .kl = 0}
  zero_mem' := by
    change (0 : StandardIntegralSplitOctonion) .j = 0 ∧
      (0 : StandardIntegralSplitOctonion) .jl = 0 ∧
      (0 : StandardIntegralSplitOctonion) .k = 0 ∧
      (0 : StandardIntegralSplitOctonion) .kl = 0
    exact ⟨rfl, rfl, rfl, rfl⟩
  add_mem' := by
    intro x y hx hy
    change x .j + y .j = 0 ∧ x .jl + y .jl = 0 ∧
      x .k + y .k = 0 ∧ x .kl + y .kl = 0
    exact ⟨by rw [hx.1, hy.1, add_zero], by rw [hx.2.1, hy.2.1, add_zero],
      by rw [hx.2.2.1, hy.2.2.1, add_zero],
      by rw [hx.2.2.2, hy.2.2.2, add_zero]⟩
  smul_mem' := by
    intro a x hx
    change a • x .j = 0 ∧ a • x .jl = 0 ∧
      a • x .k = 0 ∧ a • x .kl = 0
    exact ⟨by rw [hx.1, smul_zero], by rw [hx.2.1, smul_zero],
      by rw [hx.2.2.1, smul_zero], by rw [hx.2.2.2, smul_zero]⟩

def greenIntegralSector :
    Submodule ℤ StandardIntegralSplitOctonion where
  carrier := {x |
    x .i = 0 ∧ x .il = 0 ∧ x .k = 0 ∧ x .kl = 0}
  zero_mem' := by
    change (0 : StandardIntegralSplitOctonion) .i = 0 ∧
      (0 : StandardIntegralSplitOctonion) .il = 0 ∧
      (0 : StandardIntegralSplitOctonion) .k = 0 ∧
      (0 : StandardIntegralSplitOctonion) .kl = 0
    exact ⟨rfl, rfl, rfl, rfl⟩
  add_mem' := by
    intro x y hx hy
    change x .i + y .i = 0 ∧ x .il + y .il = 0 ∧
      x .k + y .k = 0 ∧ x .kl + y .kl = 0
    exact ⟨by rw [hx.1, hy.1, add_zero], by rw [hx.2.1, hy.2.1, add_zero],
      by rw [hx.2.2.1, hy.2.2.1, add_zero],
      by rw [hx.2.2.2, hy.2.2.2, add_zero]⟩
  smul_mem' := by
    intro a x hx
    change a • x .i = 0 ∧ a • x .il = 0 ∧
      a • x .k = 0 ∧ a • x .kl = 0
    exact ⟨by rw [hx.1, smul_zero], by rw [hx.2.1, smul_zero],
      by rw [hx.2.2.1, smul_zero], by rw [hx.2.2.2, smul_zero]⟩

def blueIntegralSector :
    Submodule ℤ StandardIntegralSplitOctonion where
  carrier := {x |
    x .i = 0 ∧ x .il = 0 ∧ x .j = 0 ∧ x .jl = 0}
  zero_mem' := by
    change (0 : StandardIntegralSplitOctonion) .i = 0 ∧
      (0 : StandardIntegralSplitOctonion) .il = 0 ∧
      (0 : StandardIntegralSplitOctonion) .j = 0 ∧
      (0 : StandardIntegralSplitOctonion) .jl = 0
    exact ⟨rfl, rfl, rfl, rfl⟩
  add_mem' := by
    intro x y hx hy
    change x .i + y .i = 0 ∧ x .il + y .il = 0 ∧
      x .j + y .j = 0 ∧ x .jl + y .jl = 0
    exact ⟨by rw [hx.1, hy.1, add_zero], by rw [hx.2.1, hy.2.1, add_zero],
      by rw [hx.2.2.1, hy.2.2.1, add_zero],
      by rw [hx.2.2.2, hy.2.2.2, add_zero]⟩
  smul_mem' := by
    intro a x hx
    change a • x .i = 0 ∧ a • x .il = 0 ∧
      a • x .j = 0 ∧ a • x .jl = 0
    exact ⟨by rw [hx.1, smul_zero], by rw [hx.2.1, smul_zero],
      by rw [hx.2.2.1, smul_zero], by rw [hx.2.2.2, smul_zero]⟩

def sharedIntegralHyperbolicAxis :
    Submodule ℤ StandardIntegralSplitOctonion where
  carrier := {x |
    x .i = 0 ∧ x .il = 0 ∧ x .j = 0 ∧ x .jl = 0 ∧
      x .k = 0 ∧ x .kl = 0}
  zero_mem' := by
    change (0 : StandardIntegralSplitOctonion) .i = 0 ∧
      (0 : StandardIntegralSplitOctonion) .il = 0 ∧
      (0 : StandardIntegralSplitOctonion) .j = 0 ∧
      (0 : StandardIntegralSplitOctonion) .jl = 0 ∧
      (0 : StandardIntegralSplitOctonion) .k = 0 ∧
      (0 : StandardIntegralSplitOctonion) .kl = 0
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  add_mem' := by
    intro x y hx hy
    change x .i + y .i = 0 ∧ x .il + y .il = 0 ∧
      x .j + y .j = 0 ∧ x .jl + y .jl = 0 ∧
      x .k + y .k = 0 ∧ x .kl + y .kl = 0
    rcases hx with ⟨hxi, hxil, hxj, hxjl, hxk, hxkl⟩
    rcases hy with ⟨hyi, hyil, hyj, hyjl, hyk, hykl⟩
    exact ⟨by rw [hxi, hyi, add_zero], by rw [hxil, hyil, add_zero],
      by rw [hxj, hyj, add_zero], by rw [hxjl, hyjl, add_zero],
      by rw [hxk, hyk, add_zero], by rw [hxkl, hykl, add_zero]⟩
  smul_mem' := by
    intro a x hx
    change a • x .i = 0 ∧ a • x .il = 0 ∧
      a • x .j = 0 ∧ a • x .jl = 0 ∧
      a • x .k = 0 ∧ a • x .kl = 0
    rcases hx with ⟨hxi, hxil, hxj, hxjl, hxk, hxkl⟩
    exact ⟨by rw [hxi, smul_zero], by rw [hxil, smul_zero],
      by rw [hxj, smul_zero], by rw [hxjl, smul_zero],
      by rw [hxk, smul_zero], by rw [hxkl, smul_zero]⟩

theorem range_redCoordinateEmbedding :
    LinearMap.range redCoordinateEmbedding = redIntegralSector := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro hx
    refine ⟨fun n => match n with
      | 0 => x .one
      | 1 => x .l
      | 2 => x .i
      | 3 => x .il, ?_⟩
    funext b
    cases b <;> simp [redCoordinateEmbedding, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]

theorem range_greenCoordinateEmbedding :
    LinearMap.range greenCoordinateEmbedding = greenIntegralSector := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro hx
    refine ⟨fun n => match n with
      | 0 => x .one
      | 1 => x .l
      | 2 => x .j
      | 3 => x .jl, ?_⟩
    funext b
    cases b <;> simp [greenCoordinateEmbedding, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]

theorem range_blueCoordinateEmbedding :
    LinearMap.range blueCoordinateEmbedding = blueIntegralSector := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro hx
    refine ⟨fun n => match n with
      | 0 => x .one
      | 1 => x .l
      | 2 => x .k
      | 3 => x .kl, ?_⟩
    funext b
    cases b <;> simp [blueCoordinateEmbedding, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]

theorem red_green_intersection_eq_sharedAxis :
    redIntegralSector ⊓ greenIntegralSector = sharedIntegralHyperbolicAxis := by
  ext x
  constructor
  · rintro ⟨hr, hg⟩
    exact ⟨hg.1, hg.2.1, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩
  · intro hx
    rcases hx with ⟨hxi, hxil, hxj, hxjl, hxk, hxkl⟩
    exact ⟨⟨hxj, hxjl, hxk, hxkl⟩, ⟨hxi, hxil, hxk, hxkl⟩⟩

theorem green_blue_intersection_eq_sharedAxis :
    greenIntegralSector ⊓ blueIntegralSector = sharedIntegralHyperbolicAxis := by
  ext x
  constructor
  · rintro ⟨hg, hb⟩
    exact ⟨hg.1, hg.2.1, hb.2.2.1, hb.2.2.2, hg.2.2.1, hg.2.2.2⟩
  · intro hx
    rcases hx with ⟨hxi, hxil, hxj, hxjl, hxk, hxkl⟩
    exact ⟨⟨hxi, hxil, hxk, hxkl⟩, ⟨hxi, hxil, hxj, hxjl⟩⟩

theorem blue_red_intersection_eq_sharedAxis :
    blueIntegralSector ⊓ redIntegralSector = sharedIntegralHyperbolicAxis := by
  ext x
  constructor
  · rintro ⟨hb, hr⟩
    rcases hb with ⟨hbi, hbil, hbj, hbjl⟩
    rcases hr with ⟨hrj, hrjl, hrk, hrkl⟩
    exact ⟨hbi, hbil, hbj, hbjl, hrk, hrkl⟩
  · intro hx
    rcases hx with ⟨hxi, hxil, hxj, hxjl, hxk, hxkl⟩
    exact ⟨⟨hxi, hxil, hxj, hxjl⟩, ⟨hxj, hxjl, hxk, hxkl⟩⟩

theorem threeColor_intersection_eq_sharedAxis :
    redIntegralSector ⊓ greenIntegralSector ⊓ blueIntegralSector =
      sharedIntegralHyperbolicAxis := by
  rw [red_green_intersection_eq_sharedAxis]
  ext x
  constructor
  · rintro ⟨hs, hb⟩
    exact hs
  · intro hx
    rcases hx with ⟨hxi, hxil, hxj, hxjl, hxk, hxkl⟩
    exact ⟨⟨hxi, hxil, hxj, hxjl, hxk, hxkl⟩, ⟨hxi, hxil, hxj, hxjl⟩⟩

end InfoGeometry.Canonical
