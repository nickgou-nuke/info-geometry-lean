/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.BrillouinKleinWallpaperCommonLatticeBridge
import InfoGeometry.Algebra.ZornDualLattice

/-!
# Wallpaper `ℤ²` → Zorn Vector-Matrix Dual-Lattice Bridge

Connects the integral wallpaper lattice `IntegralLattice = ℤ²` (from
`BrillouinKleinWallpaperCommonLatticeBridge`) to the split-octonion Zorn carrier
`ZornVectorMatrix ℚ` and its dual lattice `dualLattice` (from `ZornDualLattice`):

1. `zornEmbed : IntegralLattice →+ ZornVectorMatrix ℚ` maps `(u, v) ↦ ⟨u, ![v, 0, 0], ![-v, 0, 0], u⟩`.
2. `zornEmbed` is `ℤ`-linear and injective (`zornEmbed_injective`).
3. On the embedded 2-plane, the split Zorn polar form restricts to the scaled
   Euclidean inner product:
   `polar (zornEmbed s) (zornEmbed t) = 2 * (s.1 * t.1 + s.2 * t.2)`
   and `norm (zornEmbed t) = t.1 ^ 2 + t.2 ^ 2`.
4. `zornD4Action : Fin 8 → ZornVectorMatrix ℚ → ZornVectorMatrix ℚ` preserves `polar`
   on the embedded plane and satisfies exact `D₄`-equivariance:
   `zornD4Action g (zornEmbed t) = zornEmbed (d4_action_on_Z2 g t)`.
5. `zornLatticeSubgroup` is an integral lattice (`IsIntegralLattice zornLatticeSubgroup`),
   and `dualLattice zornLatticeSubgroup` restricts on the embedded rational plane
   `zornEmbedQ (p, q)` to the half-integral Euclidean dual `(2p ∈ ℤ) ∧ (2q ∈ ℤ)`.
-/

namespace InfoGeometry.Topology.WallpaperZornDualLatticeBridge

open InfoGeometry.Topology.BrillouinKleinWallpaperCommonLatticeBridge
open InfoGeometry.Canonical.AffineWeylD5WallpaperQuotient
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

/-- Rational 2-plane embedding `ℚ × ℚ → ZornVectorMatrix ℚ` into the positive
Euclidean slice `a = b = p`, `v = (q, 0, 0)`, `w = (-q, 0, 0)`. -/
def zornEmbedQ (x : ℚ × ℚ) : ZornVectorMatrix ℚ where
  a := x.1
  v := ![x.2, 0, 0]
  w := ![-x.2, 0, 0]
  b := x.1

/-- `ℤ`-linear embedding of `IntegralLattice = ℤ²` into `ZornVectorMatrix ℚ`. -/
def zornEmbed : IntegralLattice →+ ZornVectorMatrix ℚ where
  toFun t := zornEmbedQ (t.1, t.2)
  map_zero' := by
    change ({ a := (0 : ℚ), v := ![0, 0, 0], w := ![-0, 0, 0], b := 0 } : ZornVectorMatrix ℚ) =
      ZornVectorMatrix.zero
    simp only [ZornVectorMatrix.zero, neg_zero]
    congr 1 <;> ext i <;> fin_cases i <;> rfl
  map_add' s t := by
    change zornEmbedQ (((s.1 + t.1 : ℤ) : ℚ), ((s.2 + t.2 : ℤ) : ℚ)) =
      ZornVectorMatrix.add (zornEmbedQ (s.1, s.2)) (zornEmbedQ (t.1, t.2))
    simp only [zornEmbedQ, ZornVectorMatrix.add, Int.cast_add]
    congr 1
    · ext i; fin_cases i <;> simp
    · ext i; fin_cases i <;> (simp; try ring)

theorem zornEmbedQ_injective : Function.Injective zornEmbedQ := by
  intro x y h
  have ha : x.1 = y.1 := congrArg ZornVectorMatrix.a h
  have hv : x.2 = y.2 := by
    have := congrFun (congrArg ZornVectorMatrix.v h) 0
    simpa [zornEmbedQ] using this
  exact Prod.ext ha hv

/-- `zornEmbed` is injective on `ℤ²`. -/
theorem zornEmbed_injective : Function.Injective zornEmbed := by
  intro s t h
  have hQ := Prod.mk.inj (zornEmbedQ_injective h)
  exact Prod.ext (Int.cast_injective hQ.1) (Int.cast_injective hQ.2)

/-- On the rational 2-plane, the split Zorn polar form is `2 * (x₁ y₁ + x₂ y₂)`. -/
theorem polar_zornEmbedQ (x y : ℚ × ℚ) :
    polar (zornEmbedQ x) (zornEmbedQ y) = 2 * (x.1 * y.1 + x.2 * y.2) := by
  simp only [polar, zornEmbedQ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- On `IntegralLattice`, the split Zorn polar form restricts to twice the Euclidean
dot product. -/
theorem polar_zornEmbed (s t : IntegralLattice) :
    polar (zornEmbed s) (zornEmbed t) = 2 * ((s.1 : ℚ) * t.1 + (s.2 : ℚ) * t.2) :=
  polar_zornEmbedQ (s.1, s.2) (t.1, t.2)

/-- The split Zorn quadratic norm on `zornEmbed t` is the Euclidean squared length
`u² + v²`. -/
theorem norm_zornEmbed (t : IntegralLattice) :
    ZornVectorMatrix.norm (zornEmbed t) = (t.1 : ℚ) ^ 2 + (t.2 : ℚ) ^ 2 := by
  have h := polar_self (zornEmbed t)
  rw [polar_zornEmbed] at h
  linarith

/-- Explicit `D₄` action on the embedded 2-plane coordinates of `ZornVectorMatrix ℚ`,
fixing the orthogonal 6 coordinates. -/
def zornD4Action (g : Fin 8) (X : ZornVectorMatrix ℚ) : ZornVectorMatrix ℚ :=
  let u := X.a
  let q := X.v 0
  match g with
  | 0 => { X with a := u, b := u, v := ![q, X.v 1, X.v 2], w := ![-q, X.w 1, X.w 2] }
  | 1 => { X with a := -q, b := -q, v := ![u, X.v 1, X.v 2], w := ![-u, X.w 1, X.w 2] }
  | 2 => { X with a := -u, b := -u, v := ![-q, X.v 1, X.v 2], w := ![q, X.w 1, X.w 2] }
  | 3 => { X with a := q, b := q, v := ![-u, X.v 1, X.v 2], w := ![u, X.w 1, X.w 2] }
  | 4 => { X with a := u, b := u, v := ![-q, X.v 1, X.v 2], w := ![q, X.w 1, X.w 2] }
  | 5 => { X with a := q, b := q, v := ![u, X.v 1, X.v 2], w := ![-u, X.w 1, X.w 2] }
  | 6 => { X with a := -u, b := -u, v := ![q, X.v 1, X.v 2], w := ![-q, X.w 1, X.w 2] }
  | 7 => { X with a := -q, b := -q, v := ![-u, X.v 1, X.v 2], w := ![u, X.w 1, X.w 2] }

/-- Exact `D₄`-equivariance of `zornEmbed : ℤ² → ZornVectorMatrix ℚ`. -/
theorem zornEmbed_d4_equivariant (g : Fin 8) (t : IntegralLattice) :
    zornD4Action g (zornEmbed t) = zornEmbed (d4_action_on_Z2 g t) := by
  rcases t with ⟨u, v⟩
  fin_cases g <;>
    simp [zornD4Action, zornEmbed, zornEmbedQ, d4_action_on_Z2,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_neg, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

/-- `zornD4Action` preserves the split Zorn polar form on the embedded plane. -/
theorem polar_zornD4Action_zornEmbed (g : Fin 8) (s t : IntegralLattice) :
    polar (zornD4Action g (zornEmbed s)) (zornD4Action g (zornEmbed t)) =
      polar (zornEmbed s) (zornEmbed t) := by
  rw [zornEmbed_d4_equivariant, zornEmbed_d4_equivariant, polar_zornEmbed, polar_zornEmbed]
  rcases s with ⟨s₁, s₂⟩
  rcases t with ⟨t₁, t₂⟩
  fin_cases g <;> simp [d4_action_on_Z2] <;> ring

/-- Additive subgroup of `ZornVectorMatrix ℚ` spanned by `zornEmbed`. -/
def zornLatticeSubgroup : AddSubgroup (ZornVectorMatrix ℚ) :=
  zornEmbed.range

/-- The embedded wallpaper lattice is an integral lattice under `ZornDualLattice.polar`. -/
theorem zornLatticeSubgroup_isIntegral :
    IsIntegralLattice zornLatticeSubgroup := by
  intro X hX Y hY
  rcases hX with ⟨s, rfl⟩
  rcases hY with ⟨t, rfl⟩
  refine ⟨2 * (s.1 * t.1 + s.2 * t.2), ?_⟩
  rw [polar_zornEmbed]
  push_cast
  ring

/-- Restriction of `ZornDualLattice.dualLattice` to the embedded rational 2-plane:
`zornEmbedQ (p, q)` lies in `dualLattice zornLatticeSubgroup` iff `2p ∈ ℤ` and `2q ∈ ℤ`
(the exact Euclidean dual of `(ℤ², 2⟨·,·⟩)`). -/
theorem zornEmbedQ_mem_dualLattice_iff (x : ℚ × ℚ) :
    zornEmbedQ x ∈ dualLattice zornLatticeSubgroup ↔
      (∃ m : ℤ, 2 * x.1 = (m : ℚ)) ∧ (∃ n : ℤ, 2 * x.2 = (n : ℚ)) := by
  constructor
  · intro h
    constructor
    · obtain ⟨m, hm⟩ := h (zornEmbed (1, 0)) ⟨(1, 0), rfl⟩
      refine ⟨m, ?_⟩
      have hcalc : polar (zornEmbedQ x) (zornEmbed (1, 0)) = 2 * x.1 := by
        change polar (zornEmbedQ x) (zornEmbedQ ((1 : ℤ), (0 : ℤ))) = 2 * x.1
        rw [polar_zornEmbedQ]
        norm_num
      linarith
    · obtain ⟨n, hn⟩ := h (zornEmbed (0, 1)) ⟨(0, 1), rfl⟩
      refine ⟨n, ?_⟩
      have hcalc : polar (zornEmbedQ x) (zornEmbed (0, 1)) = 2 * x.2 := by
        change polar (zornEmbedQ x) (zornEmbedQ ((0 : ℤ), (1 : ℤ))) = 2 * x.2
        rw [polar_zornEmbedQ]
        norm_num
      linarith
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ Y hY
    rcases hY with ⟨t, rfl⟩
    refine ⟨m * t.1 + n * t.2, ?_⟩
    change polar (zornEmbedQ x) (zornEmbedQ (t.1, t.2)) = ((m * t.1 + n * t.2 : ℤ) : ℚ)
    rw [polar_zornEmbedQ]
    push_cast
    rw [← hm, ← hn]
    ring

end InfoGeometry.Topology.WallpaperZornDualLatticeBridge
