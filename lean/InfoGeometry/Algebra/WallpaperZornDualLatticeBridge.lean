/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.BrillouinKleinWallpaperCommonLatticeBridge
import InfoGeometry.Algebra.ZornDualLattice

/-!
# InfoGeometry.Algebra.WallpaperZornDualLatticeBridge

Explicit `ℤ`-linear embedding of the integral wallpaper lattice
`IntegralLattice = ℤ²` into the rational split-octonion carrier
`ZornVectorMatrix ℚ`, proving:

1. Additivity (`zornLatticeEmbedHom : IntegralLattice →+ ZornVectorMatrix ℚ`)
   and injectivity (`zornLatticeEmbed_injective`).
2. `D₄`-equivariance (`zornLatticeEmbed_d4_equivariant`) with respect to an
   explicit `D₄` action on `ZornVectorMatrix ℚ` that preserves the split polar
   form (`polar_zornD4Action`).
3. Exact Euclidean pairing recovery:
   `polar (zornLatticeEmbed t₁) (zornLatticeEmbed t₂) = (t₁.1 * t₂.1 + t₁.2 * t₂.2 : ℤ)`.
4. Exact restriction of `ZornVectorMatrix.dualLattice` to the embedded rational
   plane: a rational point `(x, y)` in the embedded plane lies in
   `dualLattice zornLatticeSubgroup` if and only if both `x` and `y` are
   integers (`zornPlaneEmbed_mem_dualLattice_iff`).
-/

namespace InfoGeometry.Algebra.WallpaperZornDualLatticeBridge

open InfoGeometry.Topology.Wallpaper
open InfoGeometry.Topology.BrillouinKleinWallpaperCommonLatticeBridge
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.AffineWeylD5WallpaperQuotient

/-- Embed a rational 2D point `(x, y)` into the split `(v, w)` vector sector of
`ZornVectorMatrix ℚ` so that the Zorn polar form restricts to the standard
Euclidean dot product `x₁ * x₂ + y₁ * y₂`. -/
def zornPlaneEmbed (x y : ℚ) : ZornVectorMatrix ℚ where
  a := 0
  b := 0
  v := ![x, y, 0]
  w := ![-(x / 2), -(y / 2), 0]

/-- Explicit `ℤ`-linear embedding `IntegralLattice = ℤ² → ZornVectorMatrix ℚ`. -/
def zornLatticeEmbed (t : IntegralLattice) : ZornVectorMatrix ℚ :=
  zornPlaneEmbed (t.1 : ℚ) (t.2 : ℚ)

@[simp] theorem zornPlaneEmbed_zero :
    zornPlaneEmbed 0 0 = (0 : ZornVectorMatrix ℚ) := by
  apply ZornVectorMatrix.ext
  · simp [zornPlaneEmbed, ZornVectorMatrix.zero]
  · funext i
    fin_cases i <;> simp [zornPlaneEmbed, ZornVectorMatrix.zero]
  · funext i
    fin_cases i <;> simp [zornPlaneEmbed, ZornVectorMatrix.zero]
  · simp [zornPlaneEmbed, ZornVectorMatrix.zero]

theorem zornPlaneEmbed_add (x₁ y₁ x₂ y₂ : ℚ) :
    zornPlaneEmbed (x₁ + x₂) (y₁ + y₂) =
      zornPlaneEmbed x₁ y₁ + zornPlaneEmbed x₂ y₂ := by
  apply ZornVectorMatrix.ext
  · simp [zornPlaneEmbed, ZornVectorMatrix.add]
  · funext i
    fin_cases i <;> simp [zornPlaneEmbed, ZornVectorMatrix.add]
  · funext i
    fin_cases i <;> simp [zornPlaneEmbed, ZornVectorMatrix.add]
    all_goals ring
  · simp [zornPlaneEmbed, ZornVectorMatrix.add]

/-- Additive (`ℤ`-linear) homomorphism from `IntegralLattice = ℤ²` into
`ZornVectorMatrix ℚ`. -/
def zornLatticeEmbedHom : IntegralLattice →+ ZornVectorMatrix ℚ where
  toFun := zornLatticeEmbed
  map_zero' := by
    change zornPlaneEmbed ((0 : ℤ) : ℚ) ((0 : ℤ) : ℚ) = 0
    simp
  map_add' := fun s t => by
    rcases s with ⟨s₁, s₂⟩
    rcases t with ⟨t₁, t₂⟩
    change zornPlaneEmbed ((s₁ + t₁ : ℤ) : ℚ) ((s₂ + t₂ : ℤ) : ℚ) =
      zornPlaneEmbed (s₁ : ℚ) (s₂ : ℚ) + zornPlaneEmbed (t₁ : ℚ) (t₂ : ℚ)
    push_cast
    exact zornPlaneEmbed_add (s₁ : ℚ) (s₂ : ℚ) (t₁ : ℚ) (t₂ : ℚ)

theorem zornPlaneEmbed_injective {x₁ y₁ x₂ y₂ : ℚ}
    (h : zornPlaneEmbed x₁ y₁ = zornPlaneEmbed x₂ y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hv0 : (zornPlaneEmbed x₁ y₁).v 0 = (zornPlaneEmbed x₂ y₂).v 0 := by rw [h]
  have hv1 : (zornPlaneEmbed x₁ y₁).v 1 = (zornPlaneEmbed x₂ y₂).v 1 := by rw [h]
  exact ⟨by simpa [zornPlaneEmbed] using hv0, by simpa [zornPlaneEmbed] using hv1⟩

theorem zornLatticeEmbed_injective : Function.Injective zornLatticeEmbed := by
  intro s t h
  rcases s with ⟨s₁, s₂⟩
  rcases t with ⟨t₁, t₂⟩
  obtain ⟨h1, h2⟩ := zornPlaneEmbed_injective h
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- Coordinate-level `D₄` action on the `(0, 1)` plane of a `ZornVec3 ℚ`. -/
def zornVec3D4 (g : Fin 8) (u : ZornVec3 ℚ) : ZornVec3 ℚ :=
  match g with
  | 0 => ![u 0, u 1, u 2]
  | 1 => ![-u 1, u 0, u 2]
  | 2 => ![-u 0, -u 1, u 2]
  | 3 => ![u 1, -u 0, u 2]
  | 4 => ![u 0, -u 1, u 2]
  | 5 => ![u 1, u 0, u 2]
  | 6 => ![-u 0, u 1, u 2]
  | 7 => ![-u 1, -u 0, u 2]

/-- Induced `D₄` action on `ZornVectorMatrix ℚ`, acting simultaneously on the
`(0, 1)` coordinates of `v` and `w` while fixing `a`, `b`, `v 2`, and `w 2`. -/
def zornD4Action (g : Fin 8) (X : ZornVectorMatrix ℚ) : ZornVectorMatrix ℚ where
  a := X.a
  b := X.b
  v := zornVec3D4 g X.v
  w := zornVec3D4 g X.w

/-- Every element of `D₄` acts as an isometry of the split Zorn polar form. -/
theorem polar_zornD4Action (g : Fin 8) (X Y : ZornVectorMatrix ℚ) :
    polar (zornD4Action g X) (zornD4Action g Y) = polar X Y := by
  fin_cases g <;> simp [polar, zornD4Action, zornVec3D4] <;> ring

/-- `D₄`-equivariance of `zornLatticeEmbed` with `d4_action_on_Z2`. -/
theorem zornLatticeEmbed_d4_equivariant (g : Fin 8) (t : IntegralLattice) :
    zornD4Action g (zornLatticeEmbed t) =
      zornLatticeEmbed (d4_action_on_Z2 g t) := by
  rcases t with ⟨u, v⟩
  fin_cases g <;>
    (apply ZornVectorMatrix.ext
     · rfl
     · funext i; fin_cases i <;>
         simp [zornD4Action, zornVec3D4, zornLatticeEmbed, zornPlaneEmbed, d4_action_on_Z2]
     · funext i; fin_cases i <;>
         simp [zornD4Action, zornVec3D4, zornLatticeEmbed, zornPlaneEmbed, d4_action_on_Z2] <;>
         ring
     · rfl)

/-- The split Zorn polar form restricts on the embedded rational plane to the
standard Euclidean inner product `x₁ * x₂ + y₁ * y₂`. -/
theorem polar_zornPlaneEmbed (x₁ y₁ x₂ y₂ : ℚ) :
    polar (zornPlaneEmbed x₁ y₁) (zornPlaneEmbed x₂ y₂) =
      x₁ * x₂ + y₁ * y₂ := by
  simp [polar, zornPlaneEmbed]
  ring

/-- The split Zorn polar form restricts on `zornLatticeEmbed` to the standard
integer Euclidean dot product. -/
theorem polar_zornLatticeEmbed (s t : IntegralLattice) :
    polar (zornLatticeEmbed s) (zornLatticeEmbed t) =
      ((s.1 * t.1 + s.2 * t.2 : ℤ) : ℚ) := by
  rcases s with ⟨s₁, s₂⟩
  rcases t with ⟨t₁, t₂⟩
  simpa [zornLatticeEmbed] using polar_zornPlaneEmbed (s₁ : ℚ) (s₂ : ℚ) (t₁ : ℚ) (t₂ : ℚ)

/-- The embedded wallpaper lattice as an additive subgroup of `ZornVectorMatrix ℚ`. -/
def zornLatticeSubgroup : AddSubgroup (ZornVectorMatrix ℚ) :=
  zornLatticeEmbedHom.range

/-- The embedded wallpaper lattice is an integral lattice with respect to the
Zorn polar form (`zornLatticeSubgroup ≤ dualLattice zornLatticeSubgroup`). -/
theorem zornLatticeSubgroup_is_integral :
    IsIntegralLattice zornLatticeSubgroup := by
  intro X hX Y hY
  rcases hX with ⟨s, rfl⟩
  rcases hY with ⟨t, rfl⟩
  exact ⟨s.1 * t.1 + s.2 * t.2, polar_zornLatticeEmbed s t⟩

/-- Exact dual-lattice restriction: a point `(x, y)` in the embedded rational
plane lies in `dualLattice zornLatticeSubgroup` iff `(x, y) ∈ ℤ²` (i.e., iff it
already lies in `zornLatticeSubgroup`). -/
theorem zornPlaneEmbed_mem_dualLattice_iff (x y : ℚ) :
    zornPlaneEmbed x y ∈ dualLattice zornLatticeSubgroup ↔
      zornPlaneEmbed x y ∈ zornLatticeSubgroup := by
  constructor
  · intro hdual
    have he1 : zornLatticeEmbed (1, 0) ∈ zornLatticeSubgroup := ⟨(1, 0), rfl⟩
    have he2 : zornLatticeEmbed (0, 1) ∈ zornLatticeSubgroup := ⟨(0, 1), rfl⟩
    rcases hdual _ he1 with ⟨m, hm⟩
    rcases hdual _ he2 with ⟨n, hn⟩
    have hx : x = (m : ℚ) := by
      have h1 := polar_zornPlaneEmbed x y 1 0
      simpa [zornLatticeEmbed] using h1.symm.trans hm
    have hy : y = (n : ℚ) := by
      have h2 := polar_zornPlaneEmbed x y 0 1
      simpa [zornLatticeEmbed] using h2.symm.trans hn
    refine ⟨(m, n), ?_⟩
    change zornPlaneEmbed (m : ℚ) (n : ℚ) = zornPlaneEmbed x y
    rw [hx, hy]
  · intro hmem
    exact zornLatticeSubgroup_is_integral hmem

end InfoGeometry.Algebra.WallpaperZornDualLatticeBridge
